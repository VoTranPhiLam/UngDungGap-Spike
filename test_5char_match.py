#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test script để verify logic 5-char matching
"""

def check_5_char_match(str1, str2):
    """
    Kiểm tra xem có ít nhất 5 ký tự liên tiếp khớp nhau không
    """
    str1_lower = str1.lower()
    str2_lower = str2.lower()

    # Kiểm tra các substring 5 ký tự của str1 có xuất hiện trong str2 không
    if len(str1_lower) >= 5:
        for i in range(len(str1_lower) - 4):
            substring = str1_lower[i:i+5]
            if substring in str2_lower:
                return True, f"Match: '{substring}' in str2"

    # Kiểm tra ngược lại: các substring 5 ký tự của str2 có xuất hiện trong str1 không
    if len(str2_lower) >= 5:
        for i in range(len(str2_lower) - 4):
            substring = str2_lower[i:i+5]
            if substring in str1_lower:
                return True, f"Match: '{substring}' in str1"

    return False, "No match"

# Test cases
test_cases = [
    ("BTCUSDT", "BTCUSD", True),      # 5 ký tự "BTCUS" khớp
    ("BTCUSD", "Bitcoin", False),     # Không khớp 5 ký tự
    ("XAUUSD", "XAUUSD.m", True),     # "XAUUS" khớp
    ("GOLD", "XAUUSD", False),        # Không khớp
    ("EURUSD.m", "EURUSD", True),     # "EURUS" khớp
    ("BTC", "BTCUSD", False),         # Chỉ 3 ký tự
    ("ETHUSDT", "ETHUSD", True),      # "ETHUS" khớp
]

print("Testing 5-char matching logic:")
print("-" * 60)

for str1, str2, expected in test_cases:
    result, reason = check_5_char_match(str1, str2)
    status = "✅" if result == expected else "❌"
    print(f"{status} '{str1}' vs '{str2}' → {result} ({reason})")
    if result != expected:
        print(f"   Expected: {expected}")

print("-" * 60)
print("Test completed!")
