#!/usr/bin/env python3
"""
Test script for subsequence matching logic
Verify that the new is_subsequence_match() function works correctly
"""

import sys

# Copy hàm is_subsequence_match để test độc lập
def is_subsequence_match(str1, str2, min_length=5):
    """
    Kiểm tra xem các ký tự có khớp theo thứ tự từ trái qua phải không (subsequence matching)
    Ví dụ: "USTEC" là subsequence của "USTECH100" (U-S-T-E-C theo thứ tự)
           "USTECH" KHÔNG phải subsequence của "HSTECH" (không có U ở đầu)

    Args:
        str1: Chuỗi thứ nhất (symbol từ sàn)
        str2: Chuỗi thứ hai (alias từ file txt)
        min_length: Số ký tự tối thiểu phải khớp (mặc định 5)

    Returns:
        bool: True nếu một chuỗi là subsequence của chuỗi kia với ít nhất min_length ký tự
    """
    str1_lower = str1.lower()
    str2_lower = str2.lower()

    def is_subsequence(pattern, text):
        """Kiểm tra pattern có phải subsequence của text không"""
        if len(pattern) < min_length:
            return False

        pattern_idx = 0
        for char in text:
            if pattern_idx < len(pattern) and char == pattern[pattern_idx]:
                pattern_idx += 1

        return pattern_idx >= min_length

    # Kiểm tra cả 2 chiều: str1 là subsequence của str2 hoặc ngược lại
    return is_subsequence(str1_lower, str2_lower) or is_subsequence(str2_lower, str1_lower)

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
        ("HSTECH", "USTECH", False, "USTECH KHÔNG phải subsequence của HSTECH (không có U ở đầu)"),
        ("USTECH", "HSTECH", False, "Kiểm tra chiều ngược lại"),
        ("GOLD", "XAUUSD", False, "Không có ký tự nào khớp theo thứ tự"),
        ("ABC", "XYZ", False, "Hoàn toàn khác nhau"),
        ("SHORT", "LONGER", False, "Không đủ 5 ký tự khớp theo thứ tự"),

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
