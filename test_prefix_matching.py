#!/usr/bin/env python3
"""
Test script để verify prefix matching logic
"""

# Giả lập gap_config và gap_config_reverse_map
gap_config = {
    'BTCUSD': {
        'aliases': ['btcusd', 'btcusdt', 'bitcoin', 'btc/usd', 'btc-usd'],
        'default_gap_percent': 0.05
    },
    'EURUSD': {
        'aliases': ['eurusd', 'eur/usd', 'eurusd.', 'eurusd-'],
        'default_gap_percent': 0.02
    },
    'XAUUSD': {
        'aliases': ['xauusd', 'gold', 'xau/usd', 'xauusd.'],
        'default_gap_percent': 0.08
    },
    'US30': {
        'aliases': ['us30', 'us30.', 'us30cash', 'dj30'],
        'default_gap_percent': 0.1
    }
}

gap_config_reverse_map = {}
for symbol_chuan, config in gap_config.items():
    gap_config_reverse_map[symbol_chuan.lower()] = symbol_chuan
    for alias in config['aliases']:
        gap_config_reverse_map[alias.lower()] = symbol_chuan


def find_symbol_config(symbol):
    """
    Tìm cấu hình cho symbol (matching với aliases, case-insensitive)
    Hỗ trợ:
    - Exact match (ưu tiên 1): So sánh chính xác 100%
    - Prefix match (ưu tiên 2): Tìm alias là prefix của symbol
      Ví dụ: BTCUSD.m, BTCUSD-spot, BTCUSD_futures đều match với BTCUSD
    """
    if not gap_config:
        return None, None, None

    symbol_lower = symbol.lower().strip()

    # Bước 1: Thử exact match (O(1) - very fast)
    symbol_chuan = gap_config_reverse_map.get(symbol_lower)

    if symbol_chuan:
        config = gap_config[symbol_chuan]

        # Determine which alias matched
        if symbol_lower == symbol_chuan.lower():
            matched_alias = symbol_chuan  # Exact match with canonical symbol
        else:
            matched_alias = symbol  # Matched via alias

        return symbol_chuan, config, matched_alias

    # Bước 2: Thử prefix match (O(n) where n = số aliases)
    # Tìm alias dài nhất là prefix của symbol để tránh false positive
    # Ví dụ: BTCUSDM nên match BTCUSD chứ không phải BTC
    best_match = None
    best_match_len = 0
    best_alias = None

    for alias_lower, symbol_chuan in gap_config_reverse_map.items():
        if symbol_lower.startswith(alias_lower):
            if len(alias_lower) > best_match_len:
                best_match = symbol_chuan
                best_match_len = len(alias_lower)
                best_alias = alias_lower

    if best_match:
        config = gap_config[best_match]
        # Return original symbol as matched_alias để hiển thị đúng
        return best_match, config, symbol

    return None, None, None


# Test cases
test_cases = [
    # Exact matches (should work as before)
    ("BTCUSD", "BTCUSD", True),
    ("btcusd", "BTCUSD", True),
    ("Bitcoin", "BTCUSD", True),
    ("BTCUSDT", "BTCUSD", True),
    ("EURUSD", "EURUSD", True),
    ("EUR/USD", "EURUSD", True),
    ("XAUUSD", "XAUUSD", True),
    ("Gold", "XAUUSD", True),
    ("US30", "US30", True),
    ("US30Cash", "US30", True),

    # Prefix matches (new functionality)
    ("BTCUSD.m", "BTCUSD", True),
    ("BTCUSD-spot", "BTCUSD", True),
    ("BTCUSD_futures", "BTCUSD", True),
    ("BTCUSD.pro", "BTCUSD", True),
    ("BTCUSD#", "BTCUSD", True),
    ("EURUSD-main", "EURUSD", True),
    ("EURUSD.ecn", "EURUSD", True),
    ("EURUSD_PRO", "EURUSD", True),
    ("XAUUSD.m", "XAUUSD", True),
    ("XAUUSD-spot", "XAUUSD", True),
    ("US30.cash", "US30", True),  # Should match US30 or US30.

    # No matches
    ("UNKNOWN", None, False),
    ("XYZ123", None, False),
    ("BTC", None, False),  # Too short, no exact match
]

print("=" * 80)
print("TEST RESULTS - PREFIX MATCHING LOGIC")
print("=" * 80)

passed = 0
failed = 0

for symbol, expected_canonical, should_match in test_cases:
    result = find_symbol_config(symbol)
    symbol_chuan, config, matched_alias = result

    if should_match:
        if symbol_chuan == expected_canonical:
            status = "✅ PASS"
            passed += 1
        else:
            status = f"❌ FAIL (got {symbol_chuan}, expected {expected_canonical})"
            failed += 1
    else:
        if symbol_chuan is None:
            status = "✅ PASS (no match)"
            passed += 1
        else:
            status = f"❌ FAIL (got {symbol_chuan}, expected no match)"
            failed += 1

    print(f"{status:30} | Input: {symbol:20} → {symbol_chuan}")

print("=" * 80)
print(f"SUMMARY: {passed} passed, {failed} failed out of {len(test_cases)} tests")
print("=" * 80)

if failed == 0:
    print("✅ All tests passed!")
else:
    print(f"❌ {failed} test(s) failed!")
