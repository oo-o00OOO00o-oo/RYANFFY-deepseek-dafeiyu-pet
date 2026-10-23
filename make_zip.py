# -*- coding: utf-8 -*-
"""打源码分享 zip（排除 venv/打包产物/配置）。

以前 BASE / OUT 写的是旧机器的 `D:\图图\大肥鱼\…`，换机器就得先手改这两个常量。
现在按脚本自己所在的位置找 —— 放在仓库根目录就能直接跑，把 zip 吐到上一层。
想指定别处就用环境变量：BIGFISH_ZIP_OUT=<zip 路径>
"""
import os
import zipfile

BASE = os.path.dirname(os.path.abspath(__file__))
OUT = os.environ.get("BIGFISH_ZIP_OUT") or os.path.join(os.path.dirname(BASE), "大肥鱼桌宠_源码.zip")

files = ["桌宠.py", "ui_console.py", "llm_chat.py", "meme_store.py",
         "chat_ui.py", "preprocess.py", "preprocess2.py", "启动桌宠.bat",
         "requirements.txt", "README.md", "LICENSE", "icon.ico", ".gitignore"]
for root, dirs, fs in os.walk(os.path.join(BASE, "sprites")):
    for f in fs:
        files.append(os.path.relpath(os.path.join(root, f), BASE).replace(os.sep, "/"))

with zipfile.ZipFile(OUT, "w", zipfile.ZIP_DEFLATED) as z:
    for f in files:
        z.write(os.path.join(BASE, f), f)

print("files:", len(files))
print("size:", os.path.getsize(OUT) // 1024, "KB")
print("out:", OUT)
for f in files:
    print(" ", f)
