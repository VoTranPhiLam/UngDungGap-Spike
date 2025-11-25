@echo off
title Gap & Spike Detector
echo ========================================
echo   Gap ^& Spike Detector - MT4/MT5
echo ========================================
echo.
echo Checking Python installation...
python --version
if %errorlevel% neq 0 (
    echo ERROR: Python not found!
    echo Please install Python 3.8 or higher
    pause
    exit /b 1
)

echo.
echo Installing dependencies...
pip install -r requirements.txt

echo.
echo Starting Gap ^& Spike Detector...
echo.
python gap_spike_detector.py

pause

