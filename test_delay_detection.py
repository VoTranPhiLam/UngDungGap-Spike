#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test Delay Detection - Gửi dữ liệu mô phỏng bid không đổi
"""

import requests
import json
import time
from datetime import datetime

SERVER_URL = "http://127.0.0.1:80"

def send_data_with_static_bid():
    """Gửi dữ liệu với bid cố định để test delay detection"""
    print("\n" + "="*70)
    print("⏱️  TEST DELAY DETECTION")
    print("="*70)
    
    # Test symbols với các scenarios khác nhau
    test_scenarios = {
        "EURUSD": {
            "bid": 1.08500,  # Bid không đổi
            "ask": 1.08520,
            "delay_type": "static",
            "description": "Bid cố định - sẽ trigger delay"
        },
        "GBPUSD": {
            "bid": 1.26500,
            "ask": 1.26520,
            "delay_type": "static",
            "description": "Bid cố định - sẽ trigger delay"
        },
        "XAUUSD": {
            "bid": 2050.50,
            "ask": 2051.00,
            "delay_type": "changing",
            "description": "Bid thay đổi - không delay"
        },
        "USDJPY": {
            "bid": 149.500,
            "ask": 149.520,
            "delay_type": "static",
            "description": "Bid cố định - sẽ trigger delay"
        }
    }
    
    print("\n📊 Test Scenarios:")
    for symbol, info in test_scenarios.items():
        print(f"   {symbol:10s} - {info['description']}")
    
    print(f"\n⏱️  Sẽ gửi dữ liệu trong 200 giây (>180s threshold)...")
    print(f"   Bạn có thể:")
    print(f"   1. Mở ứng dụng Gap & Spike Detector")
    print(f"   2. Xem bảng 'Delay Alert' trên giao diện chính")
    print(f"   3. EURUSD, GBPUSD, USDJPY sẽ xuất hiện sau 180 giây")
    print(f"   4. XAUUSD sẽ không xuất hiện (bid thay đổi)")
    
    input("\n👉 Nhấn Enter để bắt đầu test...")
    
    start_time = time.time()
    iteration = 0
    
    try:
        while True:
            iteration += 1
            elapsed = time.time() - start_time
            
            # Dừng sau 200 giây
            if elapsed > 200:
                print("\n✅ Test hoàn thành (200 giây)")
                break
            
            # Chuẩn bị data
            data = {
                "timestamp": int(time.time()),
                "broker": "DELAY-TEST-BROKER",
                "data": []
            }
            
            for symbol, info in test_scenarios.items():
                # XAUUSD: bid thay đổi mỗi 10 giây
                if info['delay_type'] == 'changing' and iteration % 10 == 0:
                    info['bid'] += 0.50  # Tăng bid
                
                symbol_data = {
                    "symbol": symbol,
                    "bid": info['bid'],
                    "ask": info['ask'],
                    "digits": 5 if symbol != "XAUUSD" else 2,
                    "points": 0.00001 if symbol != "XAUUSD" else 0.01,
                    "isOpen": True,
                    "prev_ohlc": {
                        "open": info['bid'] - 0.001,
                        "high": info['bid'] + 0.002,
                        "low": info['bid'] - 0.002,
                        "close": info['bid']
                    },
                    "current_ohlc": {
                        "open": info['bid'],
                        "high": info['bid'] + 0.001,
                        "low": info['bid'] - 0.001,
                        "close": info['bid']
                    },
                    "trade_sessions": {
                        "current_day": "Monday",
                        "days": [
                            {
                                "day": "Monday",
                                "sessions": [
                                    {"start": "00:00", "end": "23:59"}
                                ]
                            }
                        ]
                    }
                }
                data['data'].append(symbol_data)
            
            # Gửi data
            try:
                response = requests.post(
                    f"{SERVER_URL}/api/receive_data",
                    json=data,
                    headers={"Content-Type": "application/json"},
                    timeout=3
                )
                
                if response.status_code == 200:
                    # Hiển thị progress
                    minutes = int(elapsed / 60)
                    seconds = int(elapsed % 60)
                    
                    status = ""
                    if elapsed < 180:
                        status = f"⏳ Chờ delay trigger ({180 - int(elapsed)}s còn lại)"
                    else:
                        status = f"⚠️  DELAY TRIGGERED! Kiểm tra bảng Delay trên app"
                    
                    print(f"\r[{minutes:02d}:{seconds:02d}] Iteration {iteration:3d} - {status}", end='', flush=True)
                else:
                    print(f"\n❌ Server error: {response.status_code}")
                    
            except requests.exceptions.ConnectionError:
                print("\n❌ Cannot connect to server!")
                print("   Please make sure Gap & Spike Detector is running")
                break
            except Exception as e:
                print(f"\n❌ Error: {e}")
                break
            
            # Gửi mỗi giây
            time.sleep(1)
    
    except KeyboardInterrupt:
        print("\n\n⚠️  Test interrupted by user")
    
    print("\n\n" + "="*70)
    print("📈 TEST RESULTS")
    print("="*70)
    print(f"   Total time: {int(elapsed)} seconds")
    print(f"   Iterations: {iteration}")
    print("\n✅ Expected results in Delay Alert board:")
    print(f"   - EURUSD: Should appear (bid không đổi)")
    print(f"   - GBPUSD: Should appear (bid không đổi)")
    print(f"   - USDJPY: Should appear (bid không đổi)")
    print(f"   - XAUUSD: Should NOT appear (bid thay đổi)")
    print("\n💡 Tip: Thay đổi 'Delay (s)' trên app để test ngưỡng khác")
    print()

def test_bid_change_removal():
    """Test xóa khỏi bảng delay khi bid thay đổi"""
    print("\n" + "="*70)
    print("🔄 TEST BID CHANGE REMOVAL")
    print("="*70)
    print("\nTest này sẽ:")
    print("1. Gửi bid cố định trong 200s để trigger delay")
    print("2. Sau 200s, thay đổi bid")
    print("3. Symbol sẽ biến mất khỏi bảng Delay")
    
    input("\n👉 Nhấn Enter để bắt đầu...")
    
    symbol = "TESTEUR"
    base_bid = 1.10000
    current_bid = base_bid
    
    print(f"\n📍 Phase 1: Gửi bid cố định ({base_bid}) trong 200s...")
    
    start_time = time.time()
    iteration = 0
    phase = 1
    
    try:
        while True:
            iteration += 1
            elapsed = time.time() - start_time
            
            # Phase 1: 0-200s - Bid cố định
            if elapsed <= 200 and phase == 1:
                current_bid = base_bid
                phase_msg = f"⏳ Phase 1: Bid cố định - {int(200-elapsed)}s còn lại"
            
            # Phase 2: 200-230s - Thay đổi bid
            elif elapsed > 200 and phase == 1:
                phase = 2
                print(f"\n\n🔄 Phase 2: Thay đổi bid để test removal...")
                current_bid = base_bid + 0.00050  # Thay đổi bid
            
            if phase == 2:
                current_bid += 0.00001 * (iteration % 10)  # Bid dao động
                phase_msg = f"✅ Phase 2: Bid thay đổi - Symbol sẽ biến mất khỏi Delay board"
                
                if elapsed > 230:
                    print("\n\n✅ Test hoàn thành!")
                    break
            
            # Gửi data
            data = {
                "timestamp": int(time.time()),
                "broker": "REMOVAL-TEST",
                "data": [{
                    "symbol": symbol,
                    "bid": current_bid,
                    "ask": current_bid + 0.00020,
                    "digits": 5,
                    "points": 0.00001,
                    "isOpen": True,
                    "prev_ohlc": {
                        "open": current_bid - 0.001,
                        "high": current_bid + 0.002,
                        "low": current_bid - 0.002,
                        "close": current_bid
                    },
                    "current_ohlc": {
                        "open": current_bid,
                        "high": current_bid + 0.001,
                        "low": current_bid - 0.001,
                        "close": current_bid
                    },
                    "trade_sessions": {
                        "current_day": "Monday",
                        "days": [{
                            "day": "Monday",
                            "sessions": [{"start": "00:00", "end": "23:59"}]
                        }]
                    }
                }]
            }
            
            try:
                response = requests.post(
                    f"{SERVER_URL}/api/receive_data",
                    json=data,
                    timeout=3
                )
                
                minutes = int(elapsed / 60)
                seconds = int(elapsed % 60)
                print(f"\r[{minutes:02d}:{seconds:02d}] {phase_msg} (Bid: {current_bid:.5f})", end='', flush=True)
                
            except:
                print("\n❌ Connection error")
                break
            
            time.sleep(1)
    
    except KeyboardInterrupt:
        print("\n\n⚠️  Test interrupted")
    
    print("\n\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"✅ {symbol} đã trigger delay (sau 180s)")
    print(f"✅ {symbol} bid thay đổi → tự động xóa khỏi Delay board")
    print()

def main():
    """Main test menu"""
    print("\n" + "="*70)
    print("   ⏱️  DELAY DETECTION - TEST MENU")
    print("="*70)
    
    # Health check
    try:
        response = requests.get(f"{SERVER_URL}/health", timeout=5)
        if response.status_code == 200:
            print("✅ Server is running!")
        else:
            print("❌ Server error")
            return
    except:
        print("❌ Cannot connect to server!")
        print("   Please start: python gap_spike_detector.py")
        return
    
    print("\nChọn test:")
    print("1. Test Delay Detection (4 symbols, 200s)")
    print("2. Test Bid Change Removal (1 symbol, 230s)")
    print("3. Exit")
    
    choice = input("\nLựa chọn (1-3): ").strip()
    
    if choice == "1":
        send_data_with_static_bid()
    elif choice == "2":
        test_bid_change_removal()
    else:
        print("Goodbye!")

if __name__ == '__main__':
    main()

