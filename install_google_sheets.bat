@echo off
chcp 65001 >nul
echo ========================================
echo Installing Google Sheets Integration
echo ========================================
echo.

echo [1/2] Installing gspread...
pip install gspread==6.0.0

echo.
echo [2/2] Installing google-auth...
pip install google-auth==2.27.0

echo.
echo ========================================
echo ✅ Installation Complete!
echo ========================================
echo.
echo Next steps:
echo 1. Make sure credentials.json is in the same folder as gap_spike_detector.py
echo 2. Run gap_spike_detector.py
echo 3. Open Picture Gallery
echo 4. Press Enter to Accept screenshots
echo 5. Click "Hoàn thành" to send to Google Sheets
echo.
pause

