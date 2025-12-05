#!/usr/bin/env python3
"""
Logic matching cải tiến để tránh false positives
Giải quyết vấn đề: #RACE khớp với France120
"""
import re

def normalize_symbol(symbol):
    """
    Loại bỏ ký tự đặc biệt, chỉ giữ chữ và số
    Ví dụ: "#RACE" → "RACE", "BTCUSD.m" → "BTCUSDm"
    """
    # Loại bỏ tất cả ký tự không phải chữ và số
    return re.sub(r'[^a-zA-Z0-9]', '', symbol)

def is_subsequence_match_improved(str1, str2, min_length=5, min_similarity=0.5):
    """
    Logic subsequence matching cải tiến với các điều kiện chặt chẽ hơn:
    1. Normalize symbol (loại bỏ ký tự đặc biệt) trước khi so sánh
    2. Yêu cầu khớp ít nhất min_length ký tự (default 5)
    3. Yêu cầu tỷ lệ similarity tối thiểu (default 50%)
    4. Yêu cầu ký tự đầu tiên phải khớp để tránh false positives

    Args:
        str1: Chuỗi thứ nhất (symbol từ sàn)
        str2: Chuỗi thứ hai (alias từ file txt)
        min_length: Số ký tự tối thiểu phải khớp (mặc định 5)
        min_similarity: Tỷ lệ similarity tối thiểu (mặc định 0.5 = 50%)

    Returns:
        bool: True nếu khớp với tất cả điều kiện
    """
    # Normalize: loại bỏ ký tự đặc biệt
    norm1 = normalize_symbol(str1).lower()
    norm2 = normalize_symbol(str2).lower()

    # Nếu sau khi normalize mà rỗng hoặc quá ngắn → không match
    if not norm1 or not norm2:
        return False

    def calculate_subsequence_match(pattern, text):
        """
        Tính số ký tự khớp và tỷ lệ similarity
        Returns: (matched_count, similarity_ratio)
        """
        if len(pattern) < min_length:
            return 0, 0.0

        # Kiểm tra ký tự đầu tiên phải khớp
        if pattern[0] != text[0]:
            return 0, 0.0

        pattern_idx = 0
        matched_positions = []

        for i, char in enumerate(text):
            if pattern_idx < len(pattern) and char == pattern[pattern_idx]:
                matched_positions.append(i)
                pattern_idx += 1

        matched_count = pattern_idx

        # Tính tỷ lệ similarity dựa trên chuỗi dài hơn
        # Để tránh false positive khi khớp ít ký tự trong chuỗi dài
        # Ví dụ: "ABCDE" trong "AXXXBXXXCXXXDXXXE" → 5/17 = 29% (thấp)
        max_len = max(len(pattern), len(text))
        similarity = matched_count / max_len if max_len > 0 else 0.0

        return matched_count, similarity

    # Kiểm tra cả 2 chiều
    count1, sim1 = calculate_subsequence_match(norm1, norm2)
    count2, sim2 = calculate_subsequence_match(norm2, norm1)

    # Lấy kết quả tốt nhất
    best_count = max(count1, count2)
    best_similarity = max(sim1, sim2)

    # Kiểm tra điều kiện:
    # 1. Khớp ít nhất min_length ký tự
    # 2. Tỷ lệ similarity >= min_similarity
    result = best_count >= min_length and best_similarity >= min_similarity

    return result, best_count, best_similarity, norm1, norm2

def test_improved_matching():
    """Test logic cải tiến"""
    print('=' * 70)
    print('🧪 TEST LOGIC MATCHING CẢI TIẾN')
    print('=' * 70)

    test_cases = [
        # (str1, str2, expected, description)

        # ❌ False positives cần ngăn chặn
        ("#RACE", "France120", False, "RACE không nên khớp với France (ký tự đầu khác nhau)"),
        ("RACE", "France120", False, "RACE không nên khớp với France (ký tự đầu khác nhau)"),
        ("USTECH", "HSTECH", False, "Ký tự đầu khác nhau (U vs H)"),
        ("HSTECH", "USTECH", False, "Ký tự đầu khác nhau (H vs U)"),

        # ✅ True positives nên match
        ("USTECH100", "USTEC", True, "USTEC là subsequence của USTECH100 (cùng ký tự đầu U)"),
        ("USTEC", "USTECH100", True, "Kiểm tra chiều ngược lại"),
        ("BTCUSDT", "BTCUSD", True, "BTCUSD là subsequence của BTCUSDT"),
        ("BTCUSD.m", "BTCUSD", True, "Normalize: BTCUSD.m → BTCUSDm"),
        ("#BTCUSD", "BTCUSD", True, "Normalize: #BTCUSD → BTCUSD"),
        ("NASDAQ100", "NAS100", True, "NAS100 là subsequence của NASDAQ100"),

        # ✅ Exact matches
        ("BTCUSD", "BTCUSD", True, "Exact match"),
        ("#France120", "France120", True, "Normalize: #France120 → France120"),

        # ❌ Quá ngắn
        ("BTC", "BTCUSD", False, "BTC chỉ có 3 ký tự, không đủ min_length=5"),
        ("TEST", "TESTING", False, "TEST chỉ có 4 ký tự, không đủ min_length=5"),

        # ❌ Similarity thấp
        ("ABCDE", "AXXXBXXXCXXXDXXXE", False, "Khớp 5 ký tự nhưng similarity quá thấp"),
    ]

    passed = 0
    failed = 0

    for str1, str2, expected, description in test_cases:
        result, count, similarity, norm1, norm2 = is_subsequence_match_improved(str1, str2)
        status = "✅ PASS" if result == expected else "❌ FAIL"

        if result == expected:
            passed += 1
        else:
            failed += 1

        print(f"\n{status}")
        print(f"  Input: '{str1}' ↔ '{str2}'")
        print(f"  Normalized: '{norm1}' ↔ '{norm2}'")
        print(f"  Matched: {count} chars, Similarity: {similarity:.1%}")
        print(f"  Expected: {expected}, Got: {result}")
        print(f"  Description: {description}")

    print("\n" + "=" * 70)
    print(f"📊 KẾT QUẢ: {passed} passed, {failed} failed / {len(test_cases)} tests")
    print("=" * 70)

    if failed > 0:
        print("\n⚠️  CÓ TEST CASES FAILED - CẦN KIỂM TRA LẠI LOGIC")
    else:
        print("\n✅ TẤT CẢ TEST CASES ĐỀU PASS!")

    return failed == 0

if __name__ == "__main__":
    import sys
    success = test_improved_matching()
    sys.exit(0 if success else 1)
