#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test cho logic matching alias mới
- Alias khớp phải hiển thị alias từ file txt, không phải symbol từ sàn
- Similarity matching >= 70%
"""

import difflib

# Mock data từ file txt
gap_config = {
    'BTCUSD': {
        'aliases': ['BTCUSD', 'XBTUSD', 'Bitcoin', 'BTC/USD', 'BTC-USD', 'BTCUSDT'],
        'default_gap_percent': 1.0,
        'custom_gap': 81
    },
    'EURUSD': {
        'aliases': ['EURUSD', 'EUR/USD', 'EUR-USD', 'EURUSD.ecn'],
        'default_gap_percent': 0.15,
        'custom_gap': 8
    },
    'GOLD': {
        'aliases': ['GOLD', 'XAUUSD', 'XAUUSDT', 'Gold-Spot'],
        'default_gap_percent': 2.0,
        'custom_gap': 100
    }
}

# Tạo reverse map (lowercase)
gap_config_reverse_map = {}
for symbol_chuan, config in gap_config.items():
    for alias in config['aliases']:
        gap_config_reverse_map[alias.lower()] = symbol_chuan


def calculate_similarity(str1, str2):
    """Tính độ tương đồng giữa 2 chuỗi (0-100%)"""
    return difflib.SequenceMatcher(None, str1.lower(), str2.lower()).ratio()


def find_symbol_config(symbol):
    """
    Tìm cấu hình cho symbol (matching với aliases, case-insensitive)
    Hỗ trợ 3 mức độ matching (theo thứ tự ưu tiên):
    - Exact match (ưu tiên 1): So sánh chính xác 100%
    - Prefix match (ưu tiên 2): Tìm alias là prefix của symbol
    - Similarity match (ưu tiên 3): Tìm alias có độ tương đồng >= 70%

    Returns:
        tuple: (symbol_chuan, config_dict, matched_alias_from_txt) or (None, None, None)
    """
    if not gap_config:
        return None, None, None

    symbol_lower = symbol.lower().strip()

    # Bước 1: Thử exact match (O(1) - very fast)
    symbol_chuan = gap_config_reverse_map.get(symbol_lower)

    if symbol_chuan:
        config = gap_config[symbol_chuan]

        # Tìm alias từ file txt đã khớp
        if symbol_lower == symbol_chuan.lower():
            matched_alias = symbol_chuan  # Exact match với symbol chính
        else:
            # Tìm alias nào trong danh sách khớp với symbol
            for alias in config['aliases']:
                if alias.lower() == symbol_lower:
                    matched_alias = alias  # Trả về alias từ file txt
                    break
            else:
                matched_alias = symbol_chuan  # Fallback

        return symbol_chuan, config, matched_alias

    # Bước 2: Thử prefix match (O(n) where n = số aliases)
    best_match = None
    best_match_len = 0
    best_matched_alias = None

    for alias_lower, symbol_chuan in gap_config_reverse_map.items():
        if symbol_lower.startswith(alias_lower):
            if len(alias_lower) > best_match_len:
                best_match = symbol_chuan
                best_match_len = len(alias_lower)
                # Tìm alias gốc (không lowercase) từ config
                config = gap_config[symbol_chuan]
                for alias in config['aliases']:
                    if alias.lower() == alias_lower:
                        best_matched_alias = alias  # Alias từ file txt
                        break
                if not best_matched_alias:
                    best_matched_alias = symbol_chuan

    if best_match:
        config = gap_config[best_match]
        # Trả về alias từ file txt thay vì symbol từ sàn
        return best_match, config, best_matched_alias

    # Bước 3: Thử similarity match (O(n) - fallback cuối cùng)
    best_similarity = 0.0
    best_match = None
    best_matched_alias = None
    SIMILARITY_THRESHOLD = 0.70  # 70%

    for alias_lower, symbol_chuan in gap_config_reverse_map.items():
        similarity = calculate_similarity(symbol_lower, alias_lower)
        if similarity >= SIMILARITY_THRESHOLD and similarity > best_similarity:
            best_similarity = similarity
            best_match = symbol_chuan
            # Tìm alias gốc (không lowercase) từ config
            config = gap_config[symbol_chuan]
            for alias in config['aliases']:
                if alias.lower() == alias_lower:
                    best_matched_alias = alias
                    break
            if not best_matched_alias:
                best_matched_alias = symbol_chuan

    if best_match:
        config = gap_config[best_match]
        print(f"      ✅ Fuzzy match: '{symbol}' → '{best_matched_alias}' (similarity: {best_similarity*100:.1f}%)")
        return best_match, config, best_matched_alias

    return None, None, None


def run_tests():
    """Chạy các test cases"""

    print("=" * 80)
    print("TEST ALIAS MATCHING - HIỂN THỊ ALIAS TỪ FILE TXT")
    print("=" * 80)
    print()

    test_cases = [
        # (symbol_from_exchange, expected_symbol_chuan, expected_matched_alias, description)

        # ==== EXACT MATCH ====
        ("BTCUSD", "BTCUSD", "BTCUSD", "Exact match với symbol chính"),
        ("XBTUSD", "BTCUSD", "XBTUSD", "Exact match với alias XBTUSD"),
        ("Bitcoin", "BTCUSD", "Bitcoin", "Exact match với alias Bitcoin"),
        ("EURUSD", "EURUSD", "EURUSD", "Exact match với symbol chính EURUSD"),

        # ==== PREFIX MATCH ====
        ("BTCUSD-spot", "BTCUSD", "BTCUSD", "Prefix match: hiển thị BTCUSD (alias từ txt) thay vì BTCUSD-spot (symbol từ sàn)"),
        ("XBTUSD.m", "BTCUSD", "XBTUSD", "Prefix match: hiển thị XBTUSD (alias từ txt) thay vì XBTUSD.m (symbol từ sàn)"),
        ("Bitcoin_futures", "BTCUSD", "Bitcoin", "Prefix match: hiển thị Bitcoin (alias từ txt) thay vì Bitcoin_futures (symbol từ sàn)"),
        ("EURUSD.ecn_pro", "EURUSD", "EURUSD.ecn", "Prefix match: hiển thị EURUSD.ecn (alias từ txt)"),

        # ==== SIMILARITY MATCH (>= 70%) ====
        ("BTCUSDT-perp", "BTCUSD", "BTCUSDT", "Similarity match: BTCUSDT-perp tương tự BTCUSDT (>= 70%)"),
        ("XAUUSD-spot", "GOLD", "XAUUSD", "Similarity match: XAUUSD-spot tương tự XAUUSD (>= 70%)"),
        ("EUR_USD", "EURUSD", "EUR/USD", "Similarity match: EUR_USD tương tự EUR/USD (>= 70%)"),

        # ==== NO MATCH (<70%) ====
        ("AAPL", None, None, "Không khớp: AAPL không giống bất kỳ alias nào >= 70%"),
        ("TSLA", None, None, "Không khớp: TSLA không giống bất kỳ alias nào >= 70%"),
    ]

    print("\n📋 CHẠY TEST CASES:")
    print("-" * 80)

    passed = 0
    failed = 0

    for symbol_input, expected_chuan, expected_alias, description in test_cases:
        print(f"\n🔍 Test: {description}")
        print(f"   Input symbol từ sàn: '{symbol_input}'")

        symbol_chuan, config, matched_alias = find_symbol_config(symbol_input)

        # Kiểm tra kết quả
        if symbol_chuan == expected_chuan and matched_alias == expected_alias:
            print(f"   ✅ PASS")
            print(f"      Symbol chuẩn: {symbol_chuan}")
            print(f"      Alias khớp (từ file txt): {matched_alias}")
            passed += 1
        else:
            print(f"   ❌ FAIL")
            print(f"      Expected: symbol_chuan='{expected_chuan}', matched_alias='{expected_alias}'")
            print(f"      Got:      symbol_chuan='{symbol_chuan}', matched_alias='{matched_alias}'")
            failed += 1

    print("\n" + "=" * 80)
    print(f"KẾT QUẢ: {passed} PASS, {failed} FAIL")
    print("=" * 80)

    # Test similarity calculation
    print("\n📊 KIỂM TRA ĐỘ TƯƠNG ĐỒNG (SIMILARITY):")
    print("-" * 80)
    similarity_tests = [
        ("BTCUSD", "BTCUSDT", "Tương tự nhau (khác 1 ký tự)"),
        ("XAUUSD", "XAUUSD-spot", "Prefix (spot là suffix)"),
        ("EUR/USD", "EUR_USD", "Chỉ khác ký tự giữa"),
        ("BTCUSD", "AAPL", "Hoàn toàn khác nhau"),
    ]

    for str1, str2, desc in similarity_tests:
        similarity = calculate_similarity(str1, str2)
        status = "✅ PASS (>=70%)" if similarity >= 0.70 else "❌ FAIL (<70%)"
        print(f"{desc}")
        print(f"   '{str1}' vs '{str2}': {similarity*100:.1f}% {status}")
        print()


if __name__ == "__main__":
    run_tests()
