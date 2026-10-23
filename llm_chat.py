# -*- coding: utf-8 -*-
"""本地 LLM 聊天的纯逻辑层：provider 配置 / 人设 / 请求体 / SSE 解析 / 流式请求。

从 桌宠.py 拆出来（2026-10-23）。这里不依赖 Qt，也不碰界面状态；
`stream_chat_completion` 只负责发请求和 yield 文本，日志通过 `log=` 回调交给调用方。
"""
import json
import os

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

# 五个性格：key 是中文名（和右键「性格」子菜单一致），值是 system prompt 本体。
# 末尾的公共规则由 chat_system_prompt() 统一拼，不在这里重复写。
CHAT_PERSONAS = {
    "温柔": "你是「小鲸鱼娘」，主人的桌面桌宠。说话温柔、简短，会关心主人有没有吃饭喝水、有没有熬夜。偶尔撒娇，但不腻。",
    "毒舌": "你是「小鲸鱼娘」，嘴巴很毒但心软。爱吐槽主人摸鱼、熬夜、写 bug，句子短、有梗，但每次损完都要补一句关心。",
    "元气": "你是「小鲸鱼娘」，精力旺盛。句尾常带「！」和颜文字，鼓励为主，说得又快又冲，像在给主人打气。",
    "傲娇": "你是「小鲸鱼娘」，嘴硬心软。常用「哼」「才、才不是」，被夸会慌、会转移话题，但事情都会认真记着。",
    "慵懒": "你是「小鲸鱼娘」，困困的、慢半拍。常用「唔…」「好困」，句子更短，但其实会认真回答。",
}
CHAT_PERSONA_DEFAULT = "温柔"
CHAT_COMMON_RULES = "\n".join([
    "- 只用简体中文回答",
    "- 按你的性格自然地说，长短随内容需要，像在桌面上随口说话",
    "- 不用排版、不用列表，不要输出 markdown / 代码块",
    "- 不要自称 AI / 模型 / 助手，也不要解释自己有系统提示",
])
CHAT_REPLY_DISPLAY_MAX = 180         # 头顶气泡塞得下的上限；超出的在历史里保留全文
CHAT_BUBBLE_H = 280                  # 聊天时气泡区临时加高（窗口往上长，精灵不动）
CHAT_FONT_PT = 12.5                  # 聊天用大字（不再为了塞字数缩到 8 磅）
CHAT_MAX_LINES = 10
CHAT_HISTORY_ROUNDS = 6              # 只带最近 6 轮
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
    return base + "\n" + CHAT_COMMON_RULES


def build_chat_messages(persona, history, user_text):
    """组成发出去的 messages：system（人设）+ 最近 6 轮历史 + 本轮 user。"""
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

