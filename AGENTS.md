# AGENTS.md · 大肥鱼桌宠

这份文件是**跨对话**的项目约定。本仓库是 Codex 桌面应用的本地项目根目录，
新开对话默认从这里起步，所以需要长期保留的规则都写在这里，
不要依赖某个超长对话的历史。

## 环境事实（这台机器 · 2026-10-16 核实）

**先说最容易踩的：这台机器没有 F 盘。** AGENTS.md 是从旧机器带过来的，
以前写的 `F:\Codex\...` 那一整套现在**都不存在**。开工前按这张表找东西：

| 东西 | 在哪 | 备注 |
| --- | --- | --- |
| 仓库 / 工作目录 | `D:\大肥鱼桌宠` | GitHub：`git@github.com:oo-o00OOO00o-oo/RYANFFY-deepseek-dafeiyu-pet.git`（**2026-10-17 重新接的**，旧地址 `RYANFFY/deepseek-dafeiyu-pet` 已不存在） |
| 主干分支 | `main` | 远端同名；`git push -u origin main` 已设好 upstream |
| SSH 认证 | `C:\Users\16050\.ssh\github_oslab` | 从 WSL `~/.ssh/github_oslab` 复制的 ed25519 私钥，指纹 `SHA256:k/tUZhYXeGJrvuVQmQTwB9K3t2emGXn7ykquv7JmV3k`（GitHub 账号 `oo-o00OOO00o-oo`）；`~/.ssh/config` 里已给 github.com 指定它 |
| Git TLS 后端 | 全局 `http.sslBackend=openssl` | **本机 schannel 是坏的**（`SEC_E_NO_CREDENTIALS`），不改这个连 `git ls-remote` 都过不去 |
| Git 凭证 | 全局 `credential.helper=wincred` | 老的 HTTPS 密码凭证已失效，**现在只走 SSH**，不要再用 https 地址 |
| Python | `.venv\Scripts\python.exe` | **3.13.9**；依赖：PySide6 6.12.0、requests 2.32.4、zstandard 0.25.0 |
| 测试 / 排障脚本 | `D:\大肥鱼桌宠\_work\` | 已 gitignore；**不是** `F:\Codex\work` |
| DSH（DeepSeek Harness） | `D:\dsh\DeepSeek Harness.exe` | 另一份 Electron 壳在 `D:\WorkBuddy\WorkBuddyAI\` |
| DSH 会话日志 | `%USERPROFILE%\.dsh\sessions\**\session.v4.jsonl.zstd` | 状态条的数据源 |
| **没有** F 盘 | —— | 旧的 `F:\Codex\tools\innosetup\ISCC.exe`、`F:\Codex\work\publish-pet.ps1` 全没了 |
| **没有** PyInstaller | —— | `.venv` 里没装，`pyinstaller` 命令不存在 |
| **没有** Inno Setup | —— | C 盘、D 盘标准位置都没找到 `ISCC.exe` |
| **没有了** `publish-pet.ps1` | —— | 它本来就不在仓库里（在旧机器的 F 盘），跟着旧机器一起没了 |

所以：**这台机器现在发不了版。** 别照着下面的发版流程硬跑 —— 打包机都没了。
先跟主人说明"要发版得先装 PyInstaller + Inno Setup、并把发布脚本重建到 D 盘"，
再动手（别自己悄悄换一套路径就发出去）。

本机的两个权限坑（2026-10-16 实测）：

- 工作区**子目录**（`_work/`、`sprites/`、`acl-recovery/` 这些）在 DSH 沙箱里
  新建 / 写入文件会 `WinError 5 拒绝访问` —— 只有工作区**根目录**能写。
  所以新写的测试脚本别往子目录里落临时文件；`_work/` 里的现成脚本
  （`test_*.py`、`probe_*.py`）**读和改都正常**，能跑。
  已知影响：`_work/test_dsh_status.py` 跑不动（它要往系统临时目录写文件）。
- 真机探测 / Z 序这类测量**必须在真屏上跑**，不能用 `QT_QPA_PLATFORM=offscreen`：
  offscreen 平台不支持 `raise_()/lower()/SetWindowPos`，量出来的置顶标志全是假的。
  已经在屏幕上短暂弹出窗口的回归（比如 `_work/test_layer_menu.py`）会自己收摊，
  不会影响正在跑的那只桌宠。

## 是什么

Windows 桌面宠物（Python + PySide6）。大肥鱼 / 小鲸鱼形象常驻桌面，
显示 DeepSeek 余额、天气、当前播放的歌曲与歌词，带右键菜单、音效、开机自启、
可换形象，可打包成 exe 与中文安装包发布。

## 常用命令

```bash
# 运行（开发）—— 在仓库根目录跑
.venv\Scripts\pythonw.exe 桌宠.py      # 或直接双击 启动桌宠.bat

# 依赖（venv 里已经装好上面那几个；换机器时）
.venv\Scripts\python.exe -m pip install -r requirements.txt

# 打包独立 exe —— 用 spec，不要手写参数（spec 里做了 ICU 过滤）
# ⚠ 本机还没装 PyInstaller，要先：.venv\Scripts\python.exe -m pip install pyinstaller
pyinstaller --noconfirm --clean 桌宠.spec

# 打包中文安装包（Inno Setup 6）
# ⚠ 本机没有 ISCC.exe（旧路径 F:\Codex\tools\innosetup\ 已随旧机器消失），
#   要发版得先装 Inno Setup 6，然后按实际安装位置替换下面这行。
#   脚本里的中文语言文件默认读仓库 tools\ChineseSimplified.isl，仓库里没有，
#   第一次打包要按 README 的说明放一份，或传 /DMyLangFile="..."。
"C:\Program Files (x86)\Inno Setup 6\ISCC.exe" "/DMyAppVersion=1.1.6" installer.iss
```

产物在 `dist/`，不提交。发版流程见 `README.md` 的「改完代码怎么发版」：
版本号按现有最高版本 +1，保持连续、不跳号；内容没变不重发。

## 关键文件

| 文件 | 作用 |
| --- | --- |
| `桌宠.py` | 主程序，单文件，体量很大（27 万字符级别），改前先定位到具体类/方法 |
| `config.json` | 运行时配置，**已被 .gitignore 忽略**，不要提交、不要当源码改 |
| `sprites/` `assets/` | 形象贴图与音效素材 |
| `桌宠.spec` `installer.iss` | PyInstaller / Inno Setup 打包脚本 |
| `CHANGELOG.md` | 每个版本改了什么 + 怎么验证的（含实测命令与截图路径） |
| `TODO.md` | 待办，以及「已经试过、没能解决的方案」 |
| `README.md` | 面向用户与维护者的说明 |

## 这个项目的习惯（请沿用）

- 交流、注释、提交信息都用中文。commit 风格：`feat: …` / `fix: …` / `perf: …` + 中文说明。
- 每次改动同步更新 `CHANGELOG.md`（写清改了什么、怎么验证）和 `TODO.md`。
- **验证方式要落到实测**：离屏脚本用 `test_*.py`，真机探测用 `probe_*.py`，
  截图存 `shot_*.png` —— 这些放仓库根的 `_work\`（已 gitignore），不要塞进仓库。
  （旧说明写的 `F:\Codex\work\` 在这台机器上不存在，见开头「环境事实」。）
  真机 / 图层类的测量要在**真屏**上跑，不能用 offscreen，原因见开头。
- 改动右键菜单（尤其新增二级菜单）后，必须用真鼠标点一遍子菜单。
- `dist/` `build/` `.venv/` `__pycache__/` 以及运行时文件（`config.json`、`usage.json`、
  `lyrics_cache.json`、`menu-debug.log`）都不提交。
- 用户的反馈常带截图和具体时间点，照原话记进 TODO / CHANGELOG，别改写成自己的说法。

## 已知的坑（别重复踩）

- **二/三级子菜单**：Qt 弹出菜单拿不到鼠标捕获，悬停兜底、事件转发、延时关闭、
  原生消息层拦截、改成浮窗/对话框等方案都试过且无效。v1.0.10 起改为
  自己实现菜单窗口 + 自己持有捕获。细节在 `TODO.md` 末尾。
- **打包报 `DLL load failed while importing QtCore`**：PyInstaller 把本机其它运行时的
  ICU 打进了包。用 `桌宠.spec`（已加过滤）而不是手写命令行。
- **歌词**：网易云不报时间轴时按播放器时间对齐；切歌前不猜进度、失败不清空缓存。
- `make_zip.py`（打源码分享 zip）**已经修好了**：原来 `BASE` / `OUT` 写死旧机器的
  `D:\图图\大肥鱼\…`，现在按脚本自己所在位置取（BASE = 脚本目录），
  zip 默认吐到**上一层**（不给环境变量时就是 `D:\大肥鱼桌宠_源码.zip`）；
  想换地方用 `BIGFISH_ZIP_OUT=<zip 路径>`。实测 38 个文件 / 2.8 MB。
  它只是"分享源码"用的，跟发版流程（安装包 + 微信 zip）不是一回事。

## 发版：主人说「推送 / 发布 / 发版」时怎么做

> ⚠ **本机跑不了这套流程**（2026-10-16 核实）：`publish-pet.ps1` 不在仓库里，
> 它跟着旧机器的 F 盘一起没了；PyInstaller 和 Inno Setup 这台机器也没装。
> 主人说「推送」时：先如实说明"这台机器现在发不了版"，再说清缺什么
> （装 PyInstaller + Inno Setup、把发布脚本重建到 D 盘），**别自己编一套路径硬发**。
> 下面这套规矩本身没变，是**目标状态** —— 工具装回来就照它跑。

主人 2026-09-13 定的规矩（原话）：
> 之后如果我说推送等词，就把绿色安装版发送到 github 里，微信 zip 包留在之前一直放的文件夹里，
> 在回复里给我和以前一样写出来就可以，桌面命令可能因为项目创建原因好像不管用了

所以：**主人一说「推送」就由我（Codex）直接跑发布脚本**，别指望桌面上那个 `.bat`
（它是好的，但"没有代码改动"时整段跳过、连 Release 都不发，看起来就像"不管用"）。

1. 先看有没有代码改动（`git status --short`）：
   - **有改动** → 跑 `publish-pet.ps1`（自动：提交 → 推送 → 打包 → 发新版 Release）
   - **没改动、但当前版本的 Release 还没发** → 加 `-Force` 跑，否则等于什么都没做
   - **没改动、Release 也发过了** → 直接回主人「内容没变，不重发」，别硬发新版
2. 命令（脚本**不在仓库里**，所以改它不用发版；旧位置 `F:\Codex\work\publish-pet.ps1`
   已随旧机器消失，重建时建议放 `D:\Codex\work\`，建好把实际路径写回这里）：
   ```powershell
   powershell -NoProfile -ExecutionPolicy Bypass -File <发布脚本实际路径>\publish-pet.ps1 `
     -Message "feat: 中文说明" [-Force]
   ```
3. **Release 里只放** `dafeiyu-pet-setup.exe`（Windows 中文安装包，能选安装位置）——
   主人 2026-09-13 要求「GitHub 里 exe 文件就给 windows 安装版就可以了，有这个版本的就只留这个，
   没有的不用变更」：**绿色版不再上传**（v1.0.12 及更早本来就只有绿色版，保持原样没动）；
   真没编出安装包时才兜底发绿色版。
4. **微信 zip 不上传**，只做在本地（主人要求「在本地给我」）。
   旧路径 `F:\Codex\2026-09-11\...\outputs\大肥鱼桌宠-vX.Y.Z-微信版.zip` 已随 F 盘消失，
   重建发布脚本时放 `D:\Codex\work\outputs\` 之类，并把新路径写回这里。
   - **zip 里就两样**（主人 2026-09-13 要求：「就是把 windows 安装版和教程打包就可以，其他不需要」；
     后来又批注「对换回安装版，之后的也都是只保留安装版」）：
     `大肥鱼桌宠/大肥鱼桌宠-安装版-vX.Y.Z.exe`（Windows 安装版）+ `大肥鱼桌宠/使用说明.txt`（教程，
     按"先装再用"写）。**不放绿色版、不放源码、不放别的东西**（`publish-pet.ps1` 里 `New-WechatZip` 已经这么做了）。
   - **回复里要给能直接点的链接**（主人 2026-09-13 要求「之后都给我一个可以直接点的链接」）：
     写成 Markdown 链接，别用 `代码块`/纯文本把路径括起来，例如重建后：
     `[大肥鱼桌宠-vX.Y.Z-微信版.zip](D:/Codex/work/outputs/大肥鱼桌宠-vX.Y.Z-微信版.zip)`
   - 只想补做 zip：`publish-pet.ps1 -ZipOnly -Version X.Y.Z`
5. 版本号规则（2026-09-14 主人改的，原话：
   > 「之后迭代就每20一版吧，比如1.2.0的上一版是1.1.19」
   ）：**补丁位每 20 个一进位** —— 一个次版本号带 20 个补丁版，
   `x.y.0` → `x.y.1` → … → `x.y.19`，下一版就是 `x.(y+1).0`。
   也就是**没有再发 `x.y.20` 这回事**，`.19` 用完直接进位。
   现有最高版本接上这条也不会跳号：v1.0.19 已经发过，所以下一版是 **v1.1.0**。
   脚本（`publish-pet.ps1`）如果还在按"最高版本 +1"算，得先改成这个规则。
   保持连续、不跳号，内容没变不重发。
   另：界面里显示的版本号在 `ui_console.py` 的 `APP_VERSION`，
   发版时**要跟版本号一起改**（关于页和侧边栏底部都读它）。
6. 打包用 `桌宠.spec`（别手写 PyInstaller 参数）；安装包用 Inno Setup 6 的 `ISCC.exe`，
   按本机实际安装位置调用（原 `F:\Codex\tools\innosetup\ISCC.exe` 已消失）：
   `"<Inno Setup 6 安装目录>\ISCC.exe" /DMyAppVersion=X.Y.Z installer.iss`。
7. **Release 说明怎么写**（主人 2026-09-13：「现在就改，减少不必要的文案，1.0.15 的就很好」）：
   顺序是 **标题 → `## 这一版改了什么`（用户视角的 `###` 小节）→ `## 下载` → 最后一句
   「每一项的实测数据都写在仓库的 CHANGELOG.md 里。」**，像 v1.0.15 那样。
   脚本生成说明时会**自动丢掉**：以 `- 实测` / `- 回归` 开头的行（连续行）、
   以及 `### 维护者相关（…）` 那一节之后的全部内容。
  所以 **CHANGELOG 每一节按这个顺序写**：用户能看懂的（放前面）→ `- 实测…` / `- 回归…` →
  `### 维护者相关（发版 / 仓库，不写进 Release 说明）`。别把脚本路径、截图名堆在用户部分里。
  另外（主人 2026-09-13 追加：「我 2026-09-13 提的需求：> 「…」这种话就删掉就好了」）：
  **发出去的说明里别写"某某说的 / 需求原话"这类引子**（`主人 … 反馈：`、`我 … 提的需求：`、
  后面跟一段引用，都不要），直接写**改了什么** —— 说明是以主人自己的口吻发出去的，不是转述。
  （内部记录照旧：主人的原话留在 `TODO.md` 里，那是不发出去的。）

## 对话与分支

- 一个任务开一个新对话，做完归档；用项目而不是用超长对话来保存上下文。
- 不要靠「分支」把整段历史带进新对话 —— 分支会继承父对话的全部历史，
  历史越大越容易撞上接口的请求体上限（413）。

## Git 工作流（硬约束 · 2026-10-18 起）

这个仓库现在**多 agent 协作**：人类维护者只负责合并，具体开发交给各个 agent 拉分支做。
所以下面这条不是建议，是**入场券**。

### 第一条：必须先开分支，并在回复第一行贴证据

> **开工第一步必须** `git checkout -b <type>/<名> origin/main`，
> **并在回复第一行贴出 `git branch --show-current` 的输出。**
> **没有这行输出 = 交付作废**（维护者直接拒收，不看内容）。

- `<type>` 只能是 `feat` / `fix` / `refactor` / `docs` / `test` / `chore`，`<名>` 用短横线小写英文。
- **绝不在 `main` 上直接提交。** 已经在 main 上改了？先 `git stash`（或先提交到临时分支），
  再按上面的命令重来一遍，别硬着头皮往下做。
- 分支必须短命：一个分支只做一件事。中途发现别的 bug → 记下来另开分支，不要顺手改。

### 第二条：原子提交

- 消息格式 `type(scope): 中文一句话`，正文写**为什么**，不要只复述改了什么。
- 一个 commit 只完成一件逻辑完整的小事，且提交后**必须能编译、测试是绿的**；
  不要把一大坨改动攒成最后一个提交。
- 提交前自查：`git status`（没有漏 add 的文件）、`git diff --staged`（过一遍）。
- 不要提交：`config.json`、`usage.json`、`_work/`、`dist/`、`build/`、`.venv/`、`__pycache__/`、
  `*.log`、密钥/token、视频源文件、IDE 私有配置。

### 第三条：只推自己的分支

- 只 `git push -u origin <你的分支>`。**不要 push main**，也不要 `push --force`、
  `reset --hard` 公共历史、`rebase -i` 公共历史、`--no-verify`。
- 收尾 `git status` 必须干净；**分支保留不删**，由维护者合并后删除。

### 第四条：交付时必须写全

1. 分支名 + `git branch --show-current` 的输出（第一行）
2. commit 列表（hash + 一行消息）
3. 自测输出（原样贴，不要只写"测试通过"）
4. 手动验证步骤（维护者照着点一遍就能验）
5. 没做的 / 有风险的点

### 维护者这边怎么合（供参考，agent 不用做）

`squash` 或 `--no-ff` 合并 → 推送 main → 删远端/本地分支 → 合并后再跑一遍回归。
已经出现过两次 agent 直接提交到 main 的情况，维护者是把提交退回成分支再合并补救的 ——
**补救得了历史，补不回原子性**，所以第一条才要卡死。

