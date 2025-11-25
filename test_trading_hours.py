#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test Trading Hours - Gửi dữ liệu mẫu với trade_sessions
"""

import requests
import json
import time
from datetime import datetime

SERVER_URL = "http://127.0.0.1:80"

def send_sample_trading_hours_data():
    """Gửi dữ liệu mẫu với trade_sessions đầy đủ"""
    print("\n" + "="*70)
    print("📅 TEST TRADING HOURS - Gửi dữ liệu mẫu")
    print("="*70)
    
    # Dữ liệu mẫu với các loại sessions khác nhau
    sample_data = {
        "timestamp": int(time.time()),
        "broker": "DEMO-TradingHours-Test",
        "data": [
            # 1. EURUSD - Forex 24/5
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
                    "close": 1.08480
                },
                "current_ohlc": {
                    "open": 1.08500,
                    "high": 1.08530,
                    "low": 1.08490,
                    "close": 1.08510
                },
                "trade_sessions": {
                    "current_day": "Monday",
                    "days": [
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        }
                    ]
                }
            },
            
            # 2. XAUUSD - Gold với gap
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
                    "close": 2005.00
                },
                "current_ohlc": {
                    "open": 2050.00,
                    "high": 2055.00,
                    "low": 2048.00,
                    "close": 2052.00
                },
                "trade_sessions": {
                    "current_day": "Monday",
                    "days": [
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "00:05", "end": "23:00"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "00:05", "end": "23:00"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "00:05", "end": "23:00"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "00:05", "end": "23:00"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "00:05", "end": "20:55"}
                            ]
                        }
                    ]
                }
            },
            
            # 3. BTCUSD - Crypto 24/7
            {
                "symbol": "BTCUSD",
                "bid": 43500.00,
                "ask": 43510.00,
                "digits": 2,
                "points": 0.01,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 43000.00,
                    "high": 43800.00,
                    "low": 42900.00,
                    "close": 43200.00
                },
                "current_ohlc": {
                    "open": 43400.00,
                    "high": 43600.00,
                    "low": 43350.00,
                    "close": 43500.00
                },
                "trade_sessions": {
                    "current_day": "Monday",
                    "days": [
                        {
                            "day": "Sunday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        },
                        {
                            "day": "Saturday",
                            "sessions": [
                                {"start": "00:00", "end": "00:00"}
                            ]
                        }
                    ]
                }
            },
            
            # 4. US30 - Index với nhiều sessions
            {
                "symbol": "US30",
                "bid": 38500.00,
                "ask": 38502.00,
                "digits": 2,
                "points": 0.01,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 38400.00,
                    "high": 38600.00,
                    "low": 38350.00,
                    "close": 38450.00
                },
                "current_ohlc": {
                    "open": 38480.00,
                    "high": 38550.00,
                    "low": 38460.00,
                    "close": 38500.00
                },
                "trade_sessions": {
                    "current_day": "Monday",
                    "days": [
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "01:00", "end": "23:15"},
                                {"start": "23:30", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "01:00", "end": "23:15"},
                                {"start": "23:30", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "01:00", "end": "23:15"},
                                {"start": "23:30", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "01:00", "end": "23:15"},
                                {"start": "23:30", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "01:00", "end": "23:00"}
                            ]
                        }
                    ]
                }
            },
            
            # 5. GBPUSD - Closed example (Weekend)
            {
                "symbol": "GBPUSD",
                "bid": 1.26500,
                "ask": 1.26520,
                "digits": 5,
                "points": 0.00001,
                "isOpen": False,
                "prev_ohlc": {
                    "open": 1.26800,
                    "high": 1.26900,
                    "low": 1.26700,
                    "close": 1.26850
                },
                "current_ohlc": {
                    "open": 1.26500,
                    "high": 1.26550,
                    "low": 1.26480,
                    "close": 1.26510
                },
                "trade_sessions": {
                    "current_day": "Saturday",
                    "days": [
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "00:00", "end": "23:59"}
                            ]
                        }
                    ]
                }
            },
            
            # 6. NZDUSD - Overnight session
            {
                "symbol": "NZDUSD",
                "bid": 0.61500,
                "ask": 0.61520,
                "digits": 5,
                "points": 0.00001,
                "isOpen": True,
                "prev_ohlc": {
                    "open": 0.61400,
                    "high": 0.61550,
                    "low": 0.61350,
                    "close": 0.61480
                },
                "current_ohlc": {
                    "open": 0.61500,
                    "high": 0.61530,
                    "low": 0.61490,
                    "close": 0.61510
                },
                "trade_sessions": {
                    "current_day": "Monday",
                    "days": [
                        {
                            "day": "Sunday",
                            "sessions": [
                                {"start": "22:00", "end": "23:59"}
                            ]
                        },
                        {
                            "day": "Monday",
                            "sessions": [
                                {"start": "00:00", "end": "21:00"}
                            ]
                        },
                        {
                            "day": "Tuesday",
                            "sessions": [
                                {"start": "00:00", "end": "21:00"}
                            ]
                        },
                        {
                            "day": "Wednesday",
                            "sessions": [
                                {"start": "00:00", "end": "21:00"}
                            ]
                        },
                        {
                            "day": "Thursday",
                            "sessions": [
                                {"start": "00:00", "end": "21:00"}
                            ]
                        },
                        {
                            "day": "Friday",
                            "sessions": [
                                {"start": "00:00", "end": "21:00"}
                            ]
                        }
                    ]
                }
            }
        ]
    }
    
    try:
        print(f"\n📤 Sending data to {SERVER_URL}/api/receive_data")
        print(f"   Broker: {sample_data['broker']}")
        print(f"   Symbols: {len(sample_data['data'])}")
        print(f"   Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        response = requests.post(
            f"{SERVER_URL}/api/receive_data",
            json=sample_data,
            headers={"Content-Type": "application/json"},
            timeout=5
        )
        
        if response.status_code == 200:
            print("\n✅ Data sent successfully!")
            print("\n📊 Test Data Summary:")
            print("   1. EURUSD  - Forex 24/5 (Mon-Fri 00:00-23:59)")
            print("   2. XAUUSD  - Gold with gap (00:05-23:00)")
            print("   3. BTCUSD  - Crypto 24/7 (00:00-00:00)")
            print("   4. US30    - Index multiple sessions (01:00-23:15, 23:30-23:59)")
            print("   5. GBPUSD  - Weekend CLOSED example")
            print("   6. NZDUSD  - Overnight session (22:00-21:00)")
            print("\n👉 Now click 'Trading Hours' button on the application to see the results!")
            return True
        else:
            print(f"\n❌ Server returned error: {response.status_code}")
            print(f"   Response: {response.text}")
            return False
            
    except requests.exceptions.ConnectionError:
        print("\n❌ Cannot connect to server!")
        print("   Please make sure Gap & Spike Detector is running")
        return False
    except Exception as e:
        print(f"\n❌ Error: {e}")
        return False

def main():
    """Main test function"""
    print("\n" + "="*70)
    print("   📅 TRADING HOURS - TEST SCRIPT")
    print("="*70)
    print(f"\nTesting server: {SERVER_URL}")
    print(f"Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Health check
    print("\n" + "-"*70)
    print("Step 1: Health Check")
    print("-"*70)
    try:
        response = requests.get(f"{SERVER_URL}/health", timeout=5)
        if response.status_code == 200:
            data = response.json()
            print("✅ Server is running!")
            print(f"   Status: {data.get('status')}")
            print(f"   Brokers: {data.get('brokers')}")
        else:
            print(f"❌ Server returned error: {response.status_code}")
            print("\n⚠️  Please start the Gap & Spike Detector application first!")
            return
    except:
        print("❌ Cannot connect to server!")
        print("\n⚠️  Please start the Gap & Spike Detector application first!")
        print("   Run: python gap_spike_detector.py")
        print("   Or:  START_HERE.bat")
        return
    
    # Send test data
    print("\n" + "-"*70)
    print("Step 2: Send Test Data")
    print("-"*70)
    send_sample_trading_hours_data()
    
    print("\n" + "="*70)
    print("   ✅ TEST COMPLETED")
    print("="*70)
    print("\n💡 Next Steps:")
    print("   1. Open the Gap & Spike Detector application")
    print("   2. Click the 'Trading Hours' button")
    print("   3. You will see:")
    print("      - 🟢 Green rows: Symbols currently trading")
    print("      - 🔴 Red rows: Symbols not trading")
    print("   4. Try changing the Broker filter")
    print("   5. Check the Active Session and All Sessions columns")
    print("\n📚 For more info, see: TRADING_HOURS_GUIDE.md")
    print()

if __name__ == '__main__':
    main()

