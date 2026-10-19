通透模式待机曲
================

音频 / 歌词由使用者自备，仓库不包含版权素材。

路径见 config.json：
- clear_music_path：本地音频绝对路径（默认指向本机 Music 下的《朋友的酒》OGG）
- clear_lyrics_path：本地歌词绝对路径（格式 mm:ss.xx|这一句）

文件不存在 / 读不出来时：静默不播，只记一行日志，不报错、不卡住。
仓库里只保留 lyrics.example.txt（格式说明 + 空模板），不放真实歌词。
