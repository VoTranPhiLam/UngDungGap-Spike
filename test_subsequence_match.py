#!/usr/bin/env python3
"""
Test script for subsequence matching logic
Verify that the improved is_subsequence_match() function works correctly
"""

import sys
import re

# Copy hàm normalize_symbol và is_subsequence_match để test độc lập
def normalize_symbol(symbol):
    """
    Loại bỏ ký tự đặc biệt, chỉ giữ chữ và số
    Ví dụ: "#RACE" → "RACE", "BTCUSD.m" → "BTCUSDm"
    """
    return re.sub(r'[^a-zA-Z0-9]', '', symbol)

def is_subsequence_match(str1, str2, min_length=5, min_similarity=0.5):
    """
    Logic subsequence matching cải tiến với các điều kiện chặt chẽ hơn:
    1. Normalize symbol (loại bỏ ký tự đặc biệt) trước khi so sánh
    2. Yêu cầu khớp ít nhất min_length ký tự (default 5)
    3. Yêu cầu tỷ lệ similarity tối thiểu (default 50%)
    4. Yêu cầu ký tự đầu tiên phải khớp để tránh false positives
    """
    # Normalize: loại bỏ ký tự đặc biệt
    norm1 = normalize_symbol(str1).lower()
    norm2 = normalize_symbol(str2).lower()

    if not norm1 or not norm2:
        return False

    def calculate_subsequence_match(pattern, text):
        if len(pattern) < min_length:
            return 0, 0.0

        # Kiểm tra ký tự đầu tiên phải khớp
        if pattern[0] != text[0]:
            return 0, 0.0

        pattern_idx = 0
        for char in text:
            if pattern_idx < len(pattern) and char == pattern[pattern_idx]:
                pattern_idx += 1

        matched_count = pattern_idx
        max_len = max(len(pattern), len(text))
        similarity = matched_count / max_len if max_len > 0 else 0.0

        return matched_count, similarity

    count1, sim1 = calculate_subsequence_match(norm1, norm2)
    count2, sim2 = calculate_subsequence_match(norm2, norm1)

    best_count = max(count1, count2)
    best_similarity = max(sim1, sim2)

    return best_count >= min_length and best_similarity >= min_similarity

def test_subsequence_match():
    """Test various subsequence matching scenarios"""

    print("=" * 70)
    print("🧪 Testing Subsequence Matching Logic")
    print("=" * 70)

    # Test cases: (str1, str2, expected_result, description)
    test_cases = [
        # Positive cases - should match
        ("USTECH100", "USTEC", True, "USTEC là subsequence của USTECH100 (U-S-T-E-C theo thứ tự)"),
        ("USTEC", "USTECH100", True, "Kiểm tra chiều ngược lại"),
        ("BTCUSDT", "BTCUSD", True, "BTCUSD là subsequence của BTCUSDT"),
        ("XAUUSD", "XAUUSD.m", True, "Exact match với thêm suffix"),
        ("EURUSD.m", "EURUSD", True, "Symbol có thêm suffix .m"),
        ("NASDAQ100", "NAS100", True, "NAS100 là subsequence của NASDAQ100"),

        # Negative cases - should NOT match
        ("#RACE", "France120", False, "RACE KHÔNG khớp với France (ký tự đầu khác nhau)"),
        ("RACE", "France120", False, "RACE KHÔNG khớp với France (ký tự đầu khác nhau)"),
        ("HSTECH", "USTECH", False, "USTECH KHÔNG phải subsequence của HSTECH (ký tự đầu khác nhau)"),
        ("USTECH", "HSTECH", False, "Kiểm tra chiều ngược lại"),
        ("GOLD", "XAUUSD", False, "Ký tự đầu khác nhau (G vs X)"),
        ("ABC", "XYZ", False, "Hoàn toàn khác nhau"),
        ("SHORT", "LONGER", False, "Ký tự đầu khác nhau (S vs L)"),

        # Edge cases
        ("BTCUSD", "BTCUSD", True, "Exact match"),
        ("", "SOMETHING", False, "Empty string"),
        ("SOMETHING", "", False, "Empty string (reversed)"),
        ("TEST", "T", False, "Quá ngắn - dưới 5 ký tự"),
    ]

    passed = 0
    failed = 0

    for str1, str2, expected, description in test_cases:
        result = is_subsequence_match(str1, str2)
        status = "✅ PASS" if result == expected else "❌ FAIL"

        if result == expected:
            passed += 1
        else:
            failed += 1

        print(f"\n{status}")
        print(f"  Input: '{str1}' ↔ '{str2}'")
        print(f"  Expected: {expected}, Got: {result}")
        print(f"  Description: {description}")

    print("\n" + "=" * 70)
    print(f"📊 Test Results: {passed} passed, {failed} failed out of {len(test_cases)} tests")
    print("=" * 70)

    return failed == 0

if __name__ == "__main__":
    success = test_subsequence_match()
    sys.exit(0 if success else 1)
