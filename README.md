# DLS Bot
App Android: chụp màn hình -> gửi AI (Claude) quyết định -> điều khiển joystick + nút A/B/C bằng cử chỉ đa điểm chạm.

## Build APK
Đẩy toàn bộ lên GitHub -> tab Actions -> build-apk -> tải artifact `dls-bot-apk`.

## Dùng
1. Cài APK, dán API key Anthropic, bật Trợ năng > DLS Bot.
2. Mở game, bấm ⚙, kéo JOY/A/B/C đè đúng nút rồi LƯU.
3. Bấm ▶ để chạy, ⏹ để dừng.

Chỉnh chiến thuật: sửa biến SYS trong BotService.kt.
