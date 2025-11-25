@echo off
chcp 65001 >nul
color 0A
title Gap & Spike Detector - Quick Start

cls
echo.
echo ══════════════════════════════════════════════════════════
echo        GAP ^& SPIKE DETECTOR - QUICK START
echo ══════════════════════════════════════════════════════════
echo.
echo 📋 Step 1: Checking Python...
python --version 2>nul
if %errorlevel% neq 0 (
    color 0C
    echo.
    echo ❌ ERROR: Python NOT FOUND!
    echo.
    echo Please install Python 3.8 or higher from:
    echo https://www.python.org/downloads/
    echo.
    echo ⚠️  Remember to check "Add Python to PATH" during installation!
    echo.
    pause
    exit /b 1
)

echo ✅ Python is installed
echo.
echo 📋 Step 2: Installing dependencies...
pip install -r requirements.txt --quiet --disable-pip-version-check
if %errorlevel% neq 0 (
    color 0C
    echo ❌ ERROR: Failed to install dependencies!
    pause
    exit /b 1
)

echo ✅ Dependencies installed
echo.
echo ══════════════════════════════════════════════════════════
echo        INSTRUCTIONS
echo ══════════════════════════════════════════════════════════
echo.
echo 1️⃣  Install EA on MT4/MT5:
echo    - Copy GetData_v2/GetData_v2.ex4 to MT4/MQL4/Experts/
echo    - Copy GetData_v2/GetData_v2.ex5 to MT5/MQL5/Experts/
echo.
echo 2️⃣  Configure MT4/MT5:
echo    - Tools → Options → Expert Advisors
echo    - ☑ Allow WebRequest for URL: http://127.0.0.1
echo.
echo 3️⃣  Drag EA to any chart in MT4/MT5
echo.
echo 4️⃣  Wait for data to appear in the application
echo.
echo ══════════════════════════════════════════════════════════
echo.
echo 🚀 Starting Gap ^& Spike Detector...
echo.
timeout /t 2 >nul

python gap_spike_detector.py

if %errorlevel% neq 0 (
    color 0C
    echo.
    echo ❌ Application exited with error
    pause
)

