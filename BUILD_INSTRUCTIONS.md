# 🔨 Hướng Dẫn Build Executable

## 📋 Yêu Cầu Trước Khi Build

### 1. Cài đặt Python Dependencies

```bash
pip install -r requirements_build.txt
```

Hoặc cài đặt từng package:
```bash
pip install Flask==3.0.0
pip install Werkzeug==3.0.1
pip install matplotlib==3.9.0
pip install numpy>=2.0.0
pip install pyinstaller>=6.0.0
pip install pillow>=10.0.0
pip install gspread==6.0.0
pip install google-auth==2.27.0
pip install playsound==1.2.2
```

### 2. Chuẩn Bị File Cần Thiết

✅ **Bắt buộc:**
- `gap_spike_detector.py` - File chính
- `sounds/` folder với các file: `Gap.wav`, `Spike.wav`, `Delay.wav`
- Các file JSON config:
  - `delay_settings.json`
  - `gap_settings.json`
  - `manual_hidden_delays.json`
  - `market_open_settings.json`
  - `python_reset_settings.json`
  - `screenshot_settings.json`
  - `spike_settings.json`
  - `symbol_filter_settings.json`

⚠️ **Tùy chọn (nhưng nên có):**
- `credentials.json` - Để sử dụng Google Sheets integration
- `icon.ico` - Icon cho file .exe

## 🚀 Cách Build

### Phương pháp 1: Sử dụng script tự động (Khuyến nghị)

```bash
python build_executable.py
```

Script sẽ tự động:
- Kiểm tra PyInstaller có được cài đặt chưa
- Tự động cài PyInstaller nếu chưa có
- Build executable với đầy đủ dependencies
- Thông báo kết quả build

### Phương pháp 2: Build thủ công với PyInstaller

```bash
pyinstaller --name=GapSpikeDetector ^
    --onefile ^
    --windowed ^
    --clean ^
    --icon=icon.ico ^
    --add-data=delay_settings.json;. ^
    --add-data=gap_settings.json;. ^
    --add-data=manual_hidden_delays.json;. ^
    --add-data=market_open_settings.json;. ^
    --add-data=python_reset_settings.json;. ^
    --add-data=screenshot_settings.json;. ^
    --add-data=spike_settings.json;. ^
    --add-data=symbol_filter_settings.json;. ^
    --add-data=credentials.json;. ^
    --add-data=sounds;sounds ^
    --hidden-import=PIL._tkinter_finder ^
    --hidden-import=PIL.Image ^
    --hidden-import=PIL.ImageTk ^
    --hidden-import=google.oauth2.service_account ^
    --hidden-import=google.auth.transport.requests ^
    --hidden-import=gspread.auth ^
    --hidden-import=playsound ^
    --collect-all=matplotlib ^
    --collect-all=flask ^
    --collect-all=gspread ^
    --collect-all=google.auth ^
    --collect-all=google.oauth2 ^
    gap_spike_detector.py
```

**Lưu ý cho Linux/Mac:** Thay `;` bằng `:` trong `--add-data`

## 📦 Kết Quả Build

Sau khi build thành công:

```
dist/
└── GapSpikeDetector.exe  (Khoảng 100-150 MB)
```

File .exe này:
- ✅ Chứa tất cả dependencies (Flask, matplotlib, numpy, gspread, etc.)
- ✅ Chứa tất cả file config JSON
- ✅ Chứa sounds folder với các file âm thanh
- ✅ Chứa credentials.json (nếu có)
- ✅ Không cần cài Python để chạy
- ✅ Có thể chạy trên máy Windows khác ngay lập tức

## 🔍 Các Dependencies Được Bao Gồm

### Core Dependencies:
- **Flask & Werkzeug** - HTTP server để nhận dữ liệu từ MT4/MT5
- **Matplotlib** - Vẽ biểu đồ nến và gap/spike
- **NumPy** - Xử lý dữ liệu số
- **Pillow (PIL)** - Xử lý hình ảnh và screenshots
- **tkinter** - GUI interface (built-in Python)

### Optional Features:
- **gspread & google-auth** - Google Sheets integration
- **playsound** - Phát âm thanh cảnh báo

### Hidden Imports (Đã được xử lý):
- PIL._tkinter_finder
- PIL.Image, PIL.ImageTk
- google.oauth2.service_account
- google.auth.transport.requests
- gspread.auth
- playsound

## ⚠️ Xử Lý Lỗi Thường Gặp

### Lỗi: "ModuleNotFoundError" khi chạy .exe
**Nguyên nhân:** Thiếu hidden import

**Giải pháp:** Thêm module vào `--hidden-import=tên_module` trong build script

### Lỗi: File JSON/Sounds không tìm thấy
**Nguyên nhân:** Không add-data đúng cách

**Giải pháp:** Đảm bảo tất cả file JSON và sounds folder đã được thêm vào

### Lỗi: Google Sheets không hoạt động
**Nguyên nhân:** Thiếu credentials.json

**Giải pháp:**
1. Đảm bảo có file `credentials.json` trong folder build
2. Build lại executable

### Build chậm/Failed
**Giải pháp:**
1. Chạy `pyinstaller --clean` trước
2. Xóa folder `build/` và `dist/`
3. Build lại

## 📊 Thông Tin Build

**Build Configuration:**
- Mode: `--onefile` (Single executable)
- Window: `--windowed` (No console window)
- Clean: `--clean` (Clean cache before build)
- Size: ~100-150 MB (includes all dependencies)

**Platform Support:**
- ✅ Windows (primary)
- ⚠️ Linux (requires adjustment in separator `;` → `:`)
- ⚠️ MacOS (requires adjustment in separator `;` → `:`)

## 🎯 Tips Để Build Tốt Nhất

1. **Luôn build với `--clean`** - Tránh cache cũ gây lỗi
2. **Kiểm tra tất cả file trước khi build** - Đảm bảo không thiếu file
3. **Test trên máy sạch** - Chạy thử .exe trên máy không có Python
4. **Backup .spec file** - Nếu cần custom build phức tạp hơn

## 📝 Checklist Trước Khi Build

- [ ] Đã cài đặt tất cả requirements từ `requirements_build.txt`
- [ ] Có đầy đủ 8 file JSON config
- [ ] Có folder `sounds/` với 3 file .wav
- [ ] Có `credentials.json` (nếu dùng Google Sheets)
- [ ] Có `icon.ico` (nếu muốn custom icon)
- [ ] Đã test app chạy OK bằng `python gap_spike_detector.py`
- [ ] Đã xóa folder `build/` và `dist/` cũ (nếu rebuild)

## 🚀 Quick Start

```bash
# 1. Cài dependencies
pip install -r requirements_build.txt

# 2. Check files
ls *.json
ls sounds/

# 3. Build
python build_executable.py

# 4. Test
cd dist
./GapSpikeDetector.exe
```

---

**Lưu ý:** File này được tạo tự động bởi build optimization process.
