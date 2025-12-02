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
        "--icon=icon.ico",  # Optional: add icon if you have one
        "--add-data=*.json;.",
        "--add-data=sounds;sounds",  # Include sounds folder
        "--hidden-import=PIL._tkinter_finder",
        "--collect-all=matplotlib",
        "--collect-all=flask",
        "gap_spike_detector.py"
    ]
    
    # Remove --icon if icon.ico doesn't exist
    if not os.path.exists("icon.ico"):
        cmd.remove("--icon=icon.ico")
        print("ℹ️  No icon.ico found - building without icon")
    
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

