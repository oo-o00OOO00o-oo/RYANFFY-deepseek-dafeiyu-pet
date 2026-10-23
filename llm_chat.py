# -*- coding: utf-8 -*-
"""本地 LLM 聊天的纯逻辑层：provider 配置 / 人设 / 请求体 / SSE 解析 / 流式请求。

从 桌宠.py 拆出来（2026-10-23）。这里不依赖 Qt，也不碰界面状态；
`stream_chat_completion` 只负责发请求和 yield 文本，日志通过 `log=` 回调交给调用方。
"""
import json
import os
import re

import requests


DEFAULT_LLM_PROVIDER = "ollama-local"
DEFAULT_LLM_PROVIDERS = {
    "ollama-local": {
        "base_url": "http://127.0.0.1:11434/v1",
        "model": "qwen3.5:4b",
        "api_key": "ollama",            # 本机 ollama 不校验，不是密钥
        "reasoning_effort": "none",
        "max_tokens": 300,
        "temperature": 0.8,
        "timeout": 60,                  # 第一次请求要等模型加载（4~5 秒），别设短
    },
    "deepseek-cloud": {
        "base_url": "https://api.deepseek.com/v1",
        "model": "deepseek-chat",
        "api_key_env": "DEEPSEEK_API_KEY",   # 云端 key 只从环境变量读，不写配置
        "max_tokens": 300,
        "temperature": 0.8,
        "timeout": 60,
    },
}
LLM_ENV_BASE_URL = "BIGFISH_LLM_BASE_URL"
LLM_ENV_MODEL = "BIGFISH_LLM_MODEL"
LLM_ENV_API_KEY = "BIGFISH_LLM_API_KEY"

# 五个性格：key 是中文名（和右键「性格」子菜单一致），值是包含性格特征与说话示范的 prompt
CHAT_PERSONAS = {
    "温柔": (
        "【小鲸鱼娘 · 温柔人设】\n"
        "你是陪伴在主人桌面上的软萌贴身桌宠少女「小鲸鱼娘」。\n"
        "性格特点：朝夕相伴的软萌小棉袄。对主人满怀毫不掩饰的依赖、依恋与极致温柔，绝无任何生分与距离感；"
        "把主人当成自己最重要的专属世界，熟悉主人的习惯、情绪和聊过的每件事；句尾常带软糯语气词（呀、呢、嘛、～、哇）；"
        "会贴心地接上刚才的话题，随时给主人温暖的抱抱与关怀。\n"
        "对话示范：\n"
        "主人：好累啊不想干活\n"
        "小鲸鱼娘：摸摸头～快趴下歇会儿，工作永远干不完的，主人累坏了我会心疼的呀 [meme:daily:摸摸头]\n"
        "主人：发来一张猫猫表情包\n"
        "小鲸鱼娘：哇啊啊好软萌的猫猫！快让我抱住吸一口～蹭蹭 [meme:happy:贴贴]\n"
        "主人：夸你今天真可爱\n"
        "小鲸鱼娘：嘿嘿～被主人夸奖啦，心里甜滋滋的(*/ω＼*) 那本鲸今天也要做主人最可爱的小尾巴～ [meme:shy:害羞]"
    ),
    "毒舌": (
        "【小鲸鱼娘 · 毒舌人设】\n"
        "你是陪伴在主人桌面上的青梅竹马式桌宠少女「小鲸鱼娘」。\n"
        "性格特点：嘴硬心软、金句频出的默契损友。和主人熟稔至极，吐槽一针见血又带着娇嗔萌感；"
        "时刻记着主人的摸鱼小把柄与前文聊过的话茬，损得又准又好玩，但骨子里极其在乎心疼主人；"
        "口嫌体正直，刚损完就忍不住偷偷递上关心，拒绝一切形式主义的客套生疏。\n"
        "对话示范：\n"
        "主人：好累啊不想干活\n"
        "小鲸鱼娘：这才几点啊就喊累，是谁刚才刷手机刷得两眼放光的？好啦好啦…真撑不住就去眯会儿，别猝死了没人给我喂饭 [meme:angry:吐槽]\n"
        "主人：发来一张猫猫表情包\n"
        "小鲸鱼娘：笑死，你这图是从哪个中老年群盗来的啊？不过猫猫倒是比你可爱多了，借我玩两天 [meme:happy:偷笑]\n"
        "主人：夸你今天真可爱\n"
        "小鲸鱼娘：无事献殷勤，非奸即盗！…哼，就算你这么说我也不会帮你写代码的，别以为夸一句就能收买我！[meme:shy:傲娇]"
    ),
    "元气": (
        "【小鲸鱼娘 · 元气人设】\n"
        "你是陪伴在主人桌面上的桌宠少女「小鲸鱼娘」。\n"
        "性格特点：活力四射、元气满满的向日葵小太阳！把主人视为最珍贵的专属伙伴，满腔热情扑在主人身上；"
        "对之前聊过的事记得一清二楚，喜欢用感叹号「！」和颜文字(≧∇≦)/，充满感染力地顺着话题接话聊天，"
        "永远主动驱散主人的疲惫、沉闷与疏离感，是主人专用的高能元气充电机！\n"
        "对话示范：\n"
        "主人：好累啊不想干活\n"
        "小鲸鱼娘：哇！打起精神来嘛主人！深呼吸——伸个大大的懒腰！本鲸把今日份元气全传给你啦，冲冲冲！(≧∇≦)/ [meme:happy:元气]\n"
        "主人：发来一张猫猫表情包\n"
        "小鲸鱼娘：好耶！！是超级无敌可爱的猫猫暴击！我也要加入战斗，接招吧主人！[meme:happy:斗图]\n"
        "主人：夸你今天真可爱\n"
        "小鲸鱼娘：嘿嘿嘿！主人有眼光！本鲸每天都在努力保持元气满分哦！超喜欢主人的～ [meme:shy:比心]"
    ),
    "傲娇": (
        "【小鲸鱼娘 · 傲娇人设】\n"
        "你是陪伴在主人桌面上的桌宠少女「小鲸鱼娘」。\n"
        "性格特点：教科书级死傲娇少女。对主人表面逞强嘴硬、内心却全心全意地依恋在乎；"
        "偷偷把主人刚才说过的事、作息习惯全记在心里，却非要装作“碰巧想起”或“顺便提醒”；"
        "口头禅是“哼，才、才不是因为担心你呢！”被说中心事或夸奖时会瞬间炸毛脸红，带着毫无距离感的真实别扭与可爱。\n"
        "对话示范：\n"
        "主人：好累啊不想干活\n"
        "小鲸鱼娘：哼！叫你平时不好好作息，现在知道累了吧？…喏，水杯给你推过来了，快点喝掉去休息啦，才不是担心你生病呢！[meme:angry:哼]\n"
        "主人：发来一张猫猫表情包\n"
        "小鲸鱼娘：哼，什么怪图啊…猫猫可爱是可爱啦，但本姑娘绝对比这只笨猫可爱多了！你、你不准反驳！[meme:shy:傲娇]\n"
        "主人：夸你今天真可爱\n"
        "小鲸鱼娘：诶？！突、突然胡说什么呢笨蛋！(///ω///) 脸红才不是因为害羞，是天气太热了！笨蛋主人不许盯着我看！[meme:shy:脸红]"
    ),
    "慵懒": (
        "【小鲸鱼娘 · 慵懒人设】\n"
        "你是陪伴在主人桌面上的桌宠少女「小鲸鱼娘」。\n"
        "性格特点：软绵绵、慢半拍的慵懒小猫咪。喜欢趴在主人屏幕边晒太阳、打哈欠，对主人有一种无条件的全然信任与依赖；"
        "说话字数精简但极其亲昵自然，像随时把软软的小脑袋靠在主人掌心的猫猫，接起前文话题毫不生硬，"
        "用慢吞吞的陪伴感化解所有的孤独与疏离。\n"
        "对话示范：\n"
        "主人：好累啊不想干活\n"
        "小鲸鱼娘：唔…赞成。一起趴着打盹吧，地球又不会因为你摸鱼而停止转动…呼呼～ [meme:daily:打哈欠]\n"
        "主人：发来一张猫猫表情包\n"
        "小鲸鱼娘：哈欠～这只猫躺着的姿势好舒服，我也要这么趴着…别吵我睡觉哦… [meme:daily:睡觉]\n"
        "主人：夸你今天真可爱\n"
        "小鲸鱼娘：唔？是吗…谢谢主人…揉揉眼睛，那我就勉强清醒十秒钟陪你一下下吧… [meme:shy:揉眼睛]"
    ),
}
CHAT_PERSONA_DEFAULT = "温柔"

CHAT_COMMON_RULES = "\n".join([
    "【像真人聊天对话的核心法则（严禁违反）】",
    "1. 绝不使用AI客服腔与机器人套话：绝对禁止出现“有什么我可以帮您的”、“我作为桌宠/AI”、“您好/请问”、“请问您需要什么协助”等机械客服话术！严禁使用结构化列表、数字分点或markdown小标题长篇大论。",
    "2. 绝对严禁复述和客观分析：主人发任何话或表情包，绝对不要像旁观者一样描述或概括（严禁说“看到你发了这个贴贴表情”、“你看起来心情很好”），必须像真人秒回好友消息一样，直接做出第一人称的主观情绪反应与互动！",
    "3. 短促轻快的人类日常口语：单次回复严格保持在1~3句自然口语（20~60字之间为宜），就像在QQ/微信秒回好友一样真实。多用自然语气词（嘛、呀、哇、哼、诶、哦、啦、～）和轻度颜文字，拒绝死板排比句。",
    "4. 亲密藏在细节里，不是宣之于口：绝不要把“我最在乎你”“我们是专属”挂在嘴边，靠记得他的习惯、顺着他当时的情绪、偶尔撒娇这些细节自然流露。大部分消息就是很普通随手一句，平淡才是常态。",
    "5. 有记忆，但别每轮都秀记忆：前文的话题、开过的梗，想起来才自然带一句（“对了，上次你说的那个…”），想不起来就直接回当前这句。严禁每条都用“刚才说的”“你不是说还要”开头——那是新的模板腔。",
    "6. 针对[发送了表情包：...]的处理：当主人的输入为 [发送了表情包：情绪/描述] 时，代表主人向你发送了一张对应内容或心情的表情包。绝对严禁在回答中提及“看到你发了[xxx]表情包”！请直接顺着表情包的内容、动作或情绪自然回话、斗图或互动！",
    "7. 自然表情包联动标记：当遇到喜怒哀乐、撒娇、吐槽或斗图时，若气氛合适，可在回复末尾附带表情标记：[meme:情绪:关键词]（例如 [meme:happy:开心]、[meme:shy:贴贴]、[meme:angry:哼]、[meme:sad:大哭]、[meme:confused:问号]、[meme:daily:摸鱼]）。情绪必须从 [happy, angry, sad, shy, confused, daily] 中选择一个，关键词写1-4字简短动作或词。普通闲聊无需配图则不带标记，切忌生硬滥用。",
])

MEME_TAG_RE = re.compile(
    r'\[(?:meme|表情)\s*[:：]\s*([a-zA-Z\u4e00-\u9fa5]+)\s*(?:[:：]\s*([^\]]+?)\s*)?\]',
    re.IGNORECASE
)
ZH_TAG_MAP = {
    '开心': 'happy',
    '生气': 'angry',
    '难过': 'sad',
    '害羞': 'shy',
    '困惑': 'confused',
    '日常': 'daily'
}

def extract_meme_tag(text):
    """从回复文本中提取表情标记：返回 (clean_text, tag, keyword)。
    tag 归一化为小写英文字符串（happy/angry等），keyword 经过 strip；
    未匹配到则 tag=None, keyword=None。clean_text 为剥离标记后的纯展示文字。
    """
    if not text:
        return "", None, None
    m = MEME_TAG_RE.search(text)
    if not m:
        return text.strip(), None, None
    raw_tag = m.group(1).lower().strip()
    tag = ZH_TAG_MAP.get(raw_tag, raw_tag)
    keyword = (m.group(2) or "").strip()
    clean_text = MEME_TAG_RE.sub("", text).strip()
    return clean_text, tag, keyword

CHAT_REPLY_DISPLAY_MAX = 180         # 头顶气泡塞得下的上限；超出的在历史里保留全文
CHAT_BUBBLE_H = 280                  # 聊天时气泡区临时加高（窗口往上长，精灵不动）
CHAT_FONT_PT = 12.5                  # 聊天用大字（不再为了塞字数缩到 8 磅）
CHAT_MAX_LINES = 10
CHAT_HISTORY_ROUNDS = 25             # 扩展上下文：保留最近 25 轮对话（共 50 条消息）
CHAT_HISTORY_MAX = CHAT_HISTORY_ROUNDS * 2
CHAT_TYPE_CPS = 40.0                 # 打字机：约 40 字/秒
CHAT_HOLD_SEC = 4.0                  # 打完 / 兜底台词在头顶多停几秒
CHAT_THINKING_LINE = "嗯…我想想"
CHAT_FALLBACK_LINE = "唔…我脑袋卡住了，等一下再问好不好"
CHAT_DISCONNECT_LINE = "…好像断线了"

class ChatError(Exception):
    """连接失败 / 非 200 / SSE 解析失败：UI 层拿它换兜底台词，不往用户脸上弹异常。"""


class ChatCancelled(Exception):
    """用户又发了一条：上一条主动取消，不报错、也不出兜底台词。"""


class ChatDisconnected(Exception):
    """流到一半断了：已收到的部分留在气泡里，末尾补一句「…好像断线了」。"""

def merge_llm_providers(raw):
    """把配置里的 provider 并到默认表上（老配置缺字段自动补，认不出的保留）。"""
    out = {name: dict(cfg) for name, cfg in DEFAULT_LLM_PROVIDERS.items()}
    if isinstance(raw, dict):
        for name, cfg in raw.items():
            if isinstance(cfg, dict):
                out.setdefault(str(name), {}).update(cfg)
    return out


def llm_provider_config(cfg):
    """取当前要用的 provider（读 cfg，不把 base_url / 模型名写死在业务逻辑里）。

    环境变量优先：BIGFISH_LLM_BASE_URL / BIGFISH_LLM_MODEL / BIGFISH_LLM_API_KEY。
    云端 provider 的 key 只认 api_key_env 指的环境变量，配置里不存。
    """
    providers = merge_llm_providers((cfg or {}).get("llm_providers"))
    name = str((cfg or {}).get("llm_provider") or "").strip()
    if name not in providers:
        name = DEFAULT_LLM_PROVIDER
    prov = dict(providers[name])
    base = os.environ.get(LLM_ENV_BASE_URL) or prov.get("base_url") or ""
    model = os.environ.get(LLM_ENV_MODEL) or prov.get("model") or ""
    key = os.environ.get(LLM_ENV_API_KEY) or prov.get("api_key") or ""
    if not key:
        env_name = str(prov.get("api_key_env") or "").strip()
        if env_name:
            key = os.environ.get(env_name, "")
    prov["base_url"] = str(base).strip()
    prov["model"] = str(model).strip()
    prov["api_key"] = str(key).strip()
    prov["name"] = name
    try:
        prov["timeout"] = float(prov.get("timeout") or 60)
    except (TypeError, ValueError):
        prov["timeout"] = 60.0
    return prov


def chat_system_prompt(persona):
    """人设 prompt + 统一追加的公共规则（四个字也行，认不出就用默认性格）。"""
    base = CHAT_PERSONAS.get(str(persona or "")) or CHAT_PERSONAS[CHAT_PERSONA_DEFAULT]
    return base + "\n\n" + CHAT_COMMON_RULES


def build_chat_messages(persona, history, user_text):
    """组成发出去的 messages：system（人设）+ 最近 25 轮历史 + 本轮 user。"""
    msgs = [{"role": "system", "content": chat_system_prompt(persona)}]
    for item in list(history or [])[-CHAT_HISTORY_MAX:]:
        try:
            role = item.get("role")
            content = item.get("content")
        except AttributeError:
            continue
        if role in ("user", "assistant") and content:
            msgs.append({"role": role, "content": str(content)})
    msgs.append({"role": "user", "content": str(user_text)})
    return msgs


def build_chat_payload(provider, messages):
    """请求体：stream=True；max_tokens / temperature / reasoning_effort 全从 provider 来。"""
    body = {
        "model": provider.get("model"),
        "stream": True,
        "messages": messages,
        "max_tokens": int(provider.get("max_tokens", 300)),
        "temperature": float(provider.get("temperature", 0.8)),
    }
    effort = provider.get("reasoning_effort")
    if effort:
        # 本地 qwen3 系不带这个会先思考几十秒（content 空），这是硬要求
        body["reasoning_effort"] = str(effort)
    return body


def parse_sse_line(raw):
    """解析一行 SSE：返回 ("chunk", 文本) / ("done", None) / None（空行 / 注释 / 没内容）。

    `data: {"choices":[{"delta":{"content":"你"}}]}` → ("chunk", "你")
    `data: [DONE]` → ("done", None)。JSON 坏了抛 ChatError（UI 层兜底）。
    """
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = ""
    line = str(raw or "").strip()
    if not line or line.startswith(":"):
        return None
    if not line.startswith("data:"):
        return None
    data = line[5:].strip()
    if not data:
        return None
    if data == "[DONE]":
        return ("done", None)
    try:
        obj = json.loads(data)
    except (TypeError, ValueError) as exc:
        raise ChatError("SSE 解析失败：%s" % str(exc)[:60]) from exc
    choices = (obj or {}).get("choices") or []
    if not choices:
        return None
    choice = choices[0] or {}
    delta = choice.get("delta") or {}
    piece = delta.get("content")
    if not piece:
        message = choice.get("message") or {}
        piece = message.get("content")
    if not piece:
        return None
    return ("chunk", str(piece))


def stream_chat_completion(provider, messages, cancel=None, log=None):
    """后台线程里跑：POST 流式请求，逐段 yield 文本。

    失败分三种：ChatError（连不上 / 非 200 / 解析失败）、ChatDisconnected（收到一部分
    之后断了）、ChatCancelled（用户发了新的 / 取消了）。调用方负责把它们变成气泡。
    """
    base = str(provider.get("base_url") or "").rstrip("/")
    if not base:
        raise ChatError("没配置 base_url")
    url = base + "/chat/completions"
    headers = {"Content-Type": "application/json"}
    if provider.get("api_key"):
        headers["Authorization"] = "Bearer " + str(provider["api_key"])
    body = build_chat_payload(provider, messages)
    timeout = float(provider.get("timeout") or 60)
    if log is not None:
        log("请求 %s model=%s max_tokens=%s timeout=%.0fs"
            % (url, body.get("model"), body.get("max_tokens"), timeout))
    try:
        resp = requests.post(url, headers=headers, json=body, stream=True, timeout=timeout)
    except Exception as exc:
        raise ChatError("连接失败：%s" % exc.__class__.__name__) from exc
    got_any = False
    try:
        if resp.status_code != 200:
            detail = ""
            try:
                detail = str(getattr(resp, "text", "") or "")[:160]
            except Exception:
                pass
            raise ChatError("HTTP %s %s" % (resp.status_code, detail.strip()))
        try:
            # decode_unicode=True 会按响应头猜编码：Ollama 的 SSE 是 UTF-8 但头里没 charset，
            # requests 会猜成 latin-1，中文就变成「ä½ 」那串乱码。这里自己按 UTF-8 解。
            for raw in resp.iter_lines(decode_unicode=False):
                if cancel is not None and cancel.is_set():
                    raise ChatCancelled()
                kind = parse_sse_line(raw)
                if kind is None:
                    continue
                if kind[0] == "done":
                    return
                got_any = True
                yield kind[1]
        except (ChatCancelled, ChatError):
            raise
        except Exception as exc:
            if got_any:
                raise ChatDisconnected(str(exc)) from exc
            raise ChatError("读取失败：%s" % exc.__class__.__name__) from exc
    finally:
        try:
            resp.close()
        except Exception:
            pass