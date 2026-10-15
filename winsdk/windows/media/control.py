"""winsdk.windows.media.control -> winrt.windows.media.control 转发垫片。

本机 Python 3.13 装不上 winsdk（PyPI 没有 3.13 轮子，源码编译失败），
所以用 pywinrt 的 winrt-Windows.Media.Control 顶上：两者由同一份 Windows
Runtime 元数据生成，类名和方法名一致。
"""
import winrt.windows.media.control as _impl
from winrt.windows.media.control import *          # noqa: F401,F403


def __getattr__(name):
    return getattr(_impl, name)
