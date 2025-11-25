#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test script to verify Gap & Spike Detector connection
"""

import requests
import json
import time
from datetime import datetime

SERVER_URL = "http://127.0.0.1:80"

def test_health_check():
    """Test health check endpoint"""
    print("\n" + "="*60)
    print("TEST 1: Health Check")
    print("="*60)
    try:
        response = requests.get(f"{SERVER_URL}/health", timeout=5)
        if response.status_code == 200:
            data = response.json()
            print("✅ Server is running!")
            print(f"   Status: {data.get('status')}")
            print(f"   Brokers: {data.get('brokers')}")
            print(f"   Total Symbols: {data.get('total_symbols')}")
            return True
        else:
            print(f"❌ Server returned error: {response.status_code}")
            return False
    except requests.exceptions.ConnectionError:
        print("❌ Cannot connect to server!")
        print("   Please make sure Gap & Spike Detector is running")
        return False
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def test_send_sample_data():
    """Send sample data to test Gap/Spike detection"""
    print("\n" + "="*60)
    print("TEST 2: Send Sample Data")
    print("="*60)
    
    # Sample data simulating EA
    sample_data = {
        "timestamp": int(time.time()),
        "broker": "TEST-DEMO",
        "data": [
            {
                "symbol": "EURUSD",
                "bid": 1.08500,
                "ask": 1.08520,
                "digits": 5,
                "points": 0.00001,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 1.08400,
                    "high": 1.08550,
                    "low": 1.08350,
                    "close": 1.08480  # Close trước
                },
                "current_ohlc": {
                    "open": 1.08800,  # Open hiện tại - GAP UP 0.296%
                    "high": 1.08850,
                    "low": 1.08750,
                    "close": 1.08810
                }
            },
            {
                "symbol": "GBPUSD",
                "bid": 1.26500,
                "ask": 1.26520,
                "digits": 5,
                "points": 0.00001,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 1.26800,
                    "high": 1.26900,
                    "low": 1.26700,
                    "close": 1.26850
                },
                "current_ohlc": {
                    "open": 1.26200,  # Open < Close
                    "high": 1.26300,
                    "low": 1.26150,
                    "close": 1.26250
                }
            },
            {
                "symbol": "XAUUSD",
                "bid": 2050.50,
                "ask": 2051.00,
                "digits": 2,
                "points": 0.01,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 2000.00,
                    "high": 2010.00,
                    "low": 1995.00,
                    "close": 2005.00  # Close trước
                },
                "current_ohlc": {
                    "open": 2150.00,  # GAP UP rất lớn: 7.23%
                    "high": 2160.00,
                    "low": 2140.00,
                    "close": 2155.00
                }
            }
        ]
    }
    
    try:
        print("Sending sample data...")
        print(f"  Broker: {sample_data['broker']}")
        print(f"  Symbols: {len(sample_data['data'])}")
        
        response = requests.post(
            f"{SERVER_URL}/api/receive_data",
            json=sample_data,
            headers={"Content-Type": "application/json"},
            timeout=5
        )
        
        if response.status_code == 200:
            result = response.json()
            print("✅ Data sent successfully!")
            print(f"   Response: {result}")
            print("\n📊 Expected Results:")
            print("   EURUSD: GAP UP ~0.30% (detected if threshold < 0.30%)")
            print("   GBPUSD: No significant gap/spike")
            print("   XAUUSD: GAP UP ~7.23% (definitely detected)")
            print("\n👉 Check the application GUI to see the results!")
            return True
        else:
            print(f"❌ Server returned error: {response.status_code}")
            print(f"   Response: {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def main():
    """Main test function"""
    print("\n" + "="*60)
    print("   GAP & SPIKE DETECTOR - CONNECTION TEST")
    print("="*60)
    print(f"\nTesting connection to: {SERVER_URL}")
    print(f"Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Test 1: Health Check
    if not test_health_check():
        print("\n⚠️  Please start the Gap & Spike Detector application first!")
        print("   Run: python gap_spike_detector.py")
        print("   Or:  START_HERE.bat")
        return
    
    # Test 2: Send Sample Data
    test_send_sample_data()
    
    print("\n" + "="*60)
    print("   TEST COMPLETED")
    print("="*60)
    print("\n💡 Tips:")
    print("   - Check the application GUI for results")
    print("   - Adjust gap/spike thresholds in Settings")
    print("   - Monitor Activity Log for connection status")
    print()

if __name__ == '__main__':
    main()

