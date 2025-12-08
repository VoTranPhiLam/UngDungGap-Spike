#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Build script for Gap & Spike Detector
Creates standalone executable for Windows
"""

import os
import sys
import subprocess
import shutil

def main():
    print("=" * 60)
    print("Gap & Spike Detector - Build Executable")
    print("=" * 60)
    print()
    
    # Check if PyInstaller is installed
    try:
        import PyInstaller
        print("✅ PyInstaller found")
    except ImportError:
        print("❌ PyInstaller not found. Installing...")
        subprocess.check_call([sys.executable, "-m", "pip", "install", "pyinstaller"])
        print("✅ PyInstaller installed")
    
    print()
    print("Building executable...")
    print("-" * 60)
    
    # Build command
    cmd = [
        "pyinstaller",
        "--name=GapSpikeDetector",
        "--onefile",
        "--windowed",
        "--clean",  # Clean cache before building
        "--icon=icon.ico",  # Optional: add icon if you have one

        # Add data files (JSON configs and sounds)
        "--add-data=delay_settings.json;.",
        "--add-data=gap_settings.json;.",
        "--add-data=manual_hidden_delays.json;.",
        "--add-data=market_open_settings.json;.",
        "--add-data=python_reset_settings.json;.",
        "--add-data=screenshot_settings.json;.",
        "--add-data=spike_settings.json;.",
        "--add-data=symbol_filter_settings.json;.",
        "--add-data=sounds;sounds",  # Include sounds folder

        # Hidden imports for dependencies
        "--hidden-import=PIL._tkinter_finder",
        "--hidden-import=PIL.Image",
        "--hidden-import=PIL.ImageTk",
        "--hidden-import=google.oauth2.service_account",
        "--hidden-import=google.auth.transport.requests",
        "--hidden-import=gspread.auth",
        "--hidden-import=playsound",

        # Collect all packages (includes all sub-modules)
        "--collect-all=matplotlib",
        "--collect-all=flask",
        "--collect-all=gspread",
        "--collect-all=google.auth",
        "--collect-all=google.oauth2",

        # Main script
        "gap_spike_detector.py"
    ]
    
    # Remove --icon if icon.ico doesn't exist
    if not os.path.exists("icon.ico"):
        cmd.remove("--icon=icon.ico")
        print("ℹ️  No icon.ico found - building without icon")

    # Add credentials.json if exists (for Google Sheets integration)
    if os.path.exists("credentials.json"):
        cmd.insert(-1, "--add-data=credentials.json;.")
        print("✅ credentials.json found - including Google Sheets support")
    else:
        print("⚠️  No credentials.json found - Google Sheets features may not work")
    
    try:
        subprocess.check_call(cmd)
        print()
        print("=" * 60)
        print("✅ BUILD SUCCESSFUL!")
        print("=" * 60)
        print()
        print("📁 Executable location:")
        print(f"   {os.path.abspath('dist/GapSpikeDetector.exe')}")
        print()
        print("📦 File size: ~100-150 MB (includes all dependencies)")
        print()
        print("🚀 You can now distribute this .exe file!")
        print("   Users don't need Python installed.")
        print()
        
    except subprocess.CalledProcessError as e:
        print()
        print("=" * 60)
        print("❌ BUILD FAILED")
        print("=" * 60)
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()

