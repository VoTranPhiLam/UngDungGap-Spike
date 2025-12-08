#!/usr/bin/env python3
"""
Test matching logic với symbols thực từ RadexMarkets-Live và ZForexcapitalmarket-Server
"""

import re

# Mock gap_config từ file txt (28 FX symbols)
gap_config = {}
gap_config_reverse_map = {}

def load_gap_config_mock():
    """Load mock gap config"""
    global gap_config, gap_config_reverse_map

    fx_symbols = [
        'EURUSD', 'GBPUSD', 'USDJPY', 'USDCHF', 'USDCAD', 'AUDUSD', 'NZDUSD',
        'EURGBP', 'EURJPY', 'GBPJPY', 'AUDJPY', 'NZDJPY', 'CADJPY', 'CHFJPY',
        'EURCHF', 'EURCAD', 'EURAUD', 'EURNZD', 'GBPAUD', 'GBPCAD', 'GBPNZD',
        'AUDCAD', 'AUDCHF', 'AUDNZD', 'NZDCAD', 'NZDCHF', 'CADCHF', 'GBPCHF'
    ]

    for symbol in fx_symbols:
        gap_config[symbol] = {
            'aliases': [],  # Không có aliases trong file txt!
            'default_gap_percent': 0.003,
            'custom_gap': 0.003
        }
        gap_config_reverse_map[symbol.lower()] = symbol

load_gap_config_mock()

def find_symbol_config(symbol):
    """
    Logic matching từ gap_spike_detector.py (dòng 461-555)
    """
    if not gap_config:
        return None, None, None

    symbol_lower = symbol.lower().strip()

    # Bước 1: Try exact match
    symbol_chuan = gap_config_reverse_map.get(symbol_lower)
    if symbol_chuan:
        config = gap_config[symbol_chuan]
        return symbol_chuan, config, symbol_chuan

    # Bước 2: Try prefix match
    best_match = None
    best_match_len = 0
    best_matched_alias = None

    for alias_lower, symbol_chuan in gap_config_reverse_map.items():
        if symbol_lower.startswith(alias_lower):
            if len(alias_lower) > best_match_len:
                best_match = symbol_chuan
                best_match_len = len(alias_lower)
                best_matched_alias = symbol_chuan

    if best_match:
        config = gap_config[best_match]
        return best_match, config, best_matched_alias

    return None, None, None

def test_radex_zforex_matching():
    """Test matching với symbols thực từ 2 brokers"""

    print("=" * 80)
    print("TEST 1: RadexMarkets-Live symbols (có đuôi .ra)")
    print("=" * 80)

    radex_symbols = [
        'EURUSD.ra', 'GBPUSD.ra', 'USDJPY.ra', 'USDCHF.ra', 'USDCAD.ra',
        'AUDUSD.ra', 'NZDUSD.ra', 'EURGBP.ra', 'EURJPY.ra', 'GBPJPY.ra',
        'AUDJPY.ra', 'NZDJPY.ra', 'CADJPY.ra', 'CHFJPY.ra', 'EURCHF.ra',
        'EURCAD.ra', 'EURAUD.ra', 'EURNZD.ra', 'GBPAUD.ra', 'GBPCAD.ra',
        'GBPNZD.ra', 'AUDCAD.ra', 'AUDCHF.ra', 'AUDNZD.ra', 'NZDCAD.ra',
        'NZDCHF.ra', 'CADCHF.ra', 'GBPCHF.ra'
    ]

    pass_count = 0
    fail_count = 0

    for symbol in radex_symbols:
        symbol_chuan, config, matched_alias = find_symbol_config(symbol)

        if config:
            status = "✅ PASS"
            pass_count += 1
            print(f"{status} - {symbol:<20} → matched: {matched_alias}, config found: YES")
        else:
            status = "❌ FAIL"
            fail_count += 1
            print(f"{status} - {symbol:<20} → NOT MATCHED (sẽ dùng công thức %)")

    print(f"\nKết quả: {pass_count}/{len(radex_symbols)} PASS, {fail_count}/{len(radex_symbols)} FAIL")

    print("\n" + "=" * 80)
    print("TEST 2: ZForexcapitalmarket-Server symbols (KHÔNG có đuôi)")
    print("=" * 80)

    zforex_symbols = [
        'EURUSD', 'GBPUSD', 'USDJPY', 'USDCHF', 'USDCAD', 'AUDUSD', 'NZDUSD',
        'EURGBP', 'EURJPY', 'GBPJPY', 'AUDJPY', 'NZDJPY', 'CADJPY', 'CHFJPY',
        'EURCHF', 'EURCAD', 'EURAUD', 'EURNZD', 'GBPAUD', 'GBPCAD', 'GBPNZD',
        'AUDCAD', 'AUDCHF', 'AUDNZD', 'NZDCAD', 'NZDCHF', 'CADCHF', 'GBPCHF'
    ]

    pass_count = 0
    fail_count = 0

    for symbol in zforex_symbols:
        symbol_chuan, config, matched_alias = find_symbol_config(symbol)

        if config:
            status = "✅ PASS"
            pass_count += 1
            print(f"{status} - {symbol:<20} → matched: {matched_alias}, config found: YES")
        else:
            status = "❌ FAIL"
            fail_count += 1
            print(f"{status} - {symbol:<20} → NOT MATCHED (sẽ dùng công thức %)")

    print(f"\nKết quả: {pass_count}/{len(zforex_symbols)} PASS, {fail_count}/{len(zforex_symbols)} FAIL")

    print("\n" + "=" * 80)
    print("DEBUG: Kiểm tra gap_config_reverse_map")
    print("=" * 80)
    print(f"gap_config có {len(gap_config)} symbols")
    print(f"gap_config_reverse_map có {len(gap_config_reverse_map)} entries")
    print(f"Ví dụ entries: {list(gap_config_reverse_map.keys())[:10]}")

    print("\n" + "=" * 80)
    print("DEBUG: Test prefix matching chi tiết")
    print("=" * 80)

    test_cases = [
        'EURUSD.ra',
        'GBPUSD.ra',
        'EURUSD',
        'GBPUSD'
    ]

    for symbol in test_cases:
        symbol_lower = symbol.lower()
        print(f"\nSymbol: {symbol}")
        print(f"  symbol_lower: '{symbol_lower}'")
        print(f"  Checking exact match in reverse_map...")

        if symbol_lower in gap_config_reverse_map:
            print(f"    ✅ EXACT MATCH found: {gap_config_reverse_map[symbol_lower]}")
        else:
            print(f"    ❌ No exact match")
            print(f"  Checking prefix match...")

            found = False
            for alias_lower, symbol_chuan in gap_config_reverse_map.items():
                if symbol_lower.startswith(alias_lower):
                    print(f"    ✅ PREFIX MATCH: '{symbol_lower}'.startswith('{alias_lower}') → {symbol_chuan}")
                    found = True
                    break

            if not found:
                print(f"    ❌ No prefix match found")

if __name__ == '__main__':
    test_radex_zforex_matching()
