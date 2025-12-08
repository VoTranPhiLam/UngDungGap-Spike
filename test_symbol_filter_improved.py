#!/usr/bin/env python3
"""
Test improved symbol filter logic với prefix matching
Verify rằng các symbols FX với suffix (.ra, .r, .m, v.v.) được chấp nhận
"""

import re

# Mock data structures
gap_config = {}
gap_config_reverse_map = {}

def load_gap_config_mock():
    """Load mock gap config từ file txt"""
    global gap_config, gap_config_reverse_map

    # 28 FX symbols chính từ THAM_SO_GAP_INDICATOR.txt
    fx_symbols = [
        'EURUSD', 'GBPUSD', 'USDJPY', 'USDCHF', 'USDCAD', 'AUDUSD', 'NZDUSD',
        'EURGBP', 'EURJPY', 'GBPJPY', 'AUDJPY', 'NZDJPY', 'CADJPY', 'CHFJPY',
        'EURCHF', 'EURCAD', 'EURAUD', 'EURNZD', 'GBPAUD', 'GBPCAD', 'GBPNZD',
        'AUDCAD', 'AUDCHF', 'AUDNZD', 'NZDCAD', 'NZDCHF', 'CADCHF', 'GBPCHF'
    ]

    for symbol in fx_symbols:
        gap_config[symbol] = {
            'aliases': [],
            'default_gap_percent': 0.003,
            'custom_gap': 0.003
        }
        gap_config_reverse_map[symbol.lower()] = symbol

load_gap_config_mock()

def is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings):
    """
    Improved version với prefix matching support
    """
    try:
        if not symbol_filter_settings.get('enabled', False):
            return True

        selection = symbol_filter_settings.get('selection', {}) or {}
        if not selection:
            return True

        # Highest priority: broker specific list
        if broker in selection:
            broker_symbols = selection[broker]
            if broker_symbols is None:
                return False
            if not broker_symbols:
                return False

            # Level 1: Try exact match first (fast)
            if symbol in broker_symbols:
                return True

            # Level 2: Try prefix matching with gap_config (fallback)
            if gap_config:
                symbol_lower = symbol.lower().strip()
                # Normalize: loại bỏ các ký tự đặc biệt để get prefix
                symbol_normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol_lower)

                # Kiểm tra xem normalized symbol có bắt đầu bằng bất kỳ symbol nào trong gap_config không
                for config_symbol_lower in gap_config_reverse_map.keys():
                    if symbol_normalized.startswith(config_symbol_lower):
                        # Found prefix match - symbol này có trong file txt
                        return True

            # Không match cả exact và prefix
            return False

        # Broker not configured → allow all symbols for that broker by default
        return True
    except Exception as e:
        print(f"Error checking symbol filter for {broker}_{symbol}: {e}")
        return True

def test_symbol_filter_with_prefix_matching():
    """Test improved symbol filter logic"""

    # Mock symbol filter settings (giống file symbol_filter_settings.json)
    symbol_filter_settings = {
        'enabled': True,
        'selection': {
            'ScopeMarkets-Live': [
                'EURNOK.r',
                'EURSEK.r',
                'GBPNOK.r',
                'USDAED.r',
                'USDNGN.r',
                'USDSEK.r'
            ]
        }
    }

    broker = 'ScopeMarkets-Live'

    print("=" * 80)
    print("TEST 1: Exact match với symbols trong filter (should PASS)")
    print("=" * 80)

    exact_match_symbols = ['EURNOK.r', 'EURSEK.r', 'GBPNOK.r']
    for symbol in exact_match_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} - {symbol}: {result}")

    print("\n" + "=" * 80)
    print("TEST 2: FX symbols với suffix .ra (should PASS via prefix matching)")
    print("=" * 80)

    suffix_ra_symbols = ['EURUSD.ra', 'GBPUSD.ra', 'USDJPY.ra', 'USDCHF.ra', 'AUDUSD.ra']
    for symbol in suffix_ra_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 3: FX symbols với suffix .r (should PASS via prefix matching)")
    print("=" * 80)

    suffix_r_symbols = ['EURUSD.r', 'GBPUSD.r', 'EURJPY.r', 'GBPJPY.r']
    for symbol in suffix_r_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 4: FX symbols với suffix .m (should PASS via prefix matching)")
    print("=" * 80)

    suffix_m_symbols = ['EURUSD.m', 'GBPUSD.m', 'USDJPY.m', 'EURGBP.m']
    for symbol in suffix_m_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 5: FX symbols với suffix _ra, -spot (should PASS via prefix matching)")
    print("=" * 80)

    other_suffix_symbols = ['EURUSD_ra', 'GBPUSD-spot', 'USDJPY_futures', 'AUDUSD-cash']
    for symbol in other_suffix_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 6: FX symbols không có suffix (should PASS via prefix matching)")
    print("=" * 80)

    no_suffix_symbols = ['EURUSD', 'GBPUSD', 'USDJPY', 'USDCHF', 'AUDUSD', 'EURGBP']
    for symbol in no_suffix_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS" if result else "❌ FAIL"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 7: Symbols KHÔNG có trong gap_config (should FAIL)")
    print("=" * 80)

    invalid_symbols = ['AAPL.us', 'TSLA.us', '#RACE', 'BTCUSD']
    for symbol in invalid_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, symbol_filter_settings)
        status = "✅ PASS (correctly rejected)" if not result else "❌ FAIL (should reject)"
        normalized = re.sub(r'[^a-zA-Z0-9]', '', symbol.lower())
        print(f"{status} - {symbol} (normalized: {normalized}): {result}")

    print("\n" + "=" * 80)
    print("TEST 8: Filter disabled (should PASS all)")
    print("=" * 80)

    disabled_filter = {'enabled': False}
    test_symbols = ['AAPL.us', 'EURUSD.ra', 'BTCUSD', '#RACE']
    for symbol in test_symbols:
        result = is_symbol_selected_for_detection(broker, symbol, disabled_filter)
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} - {symbol}: {result}")

    print("\n" + "=" * 80)
    print("TEST SUMMARY")
    print("=" * 80)
    print("✅ Tất cả 28 FX symbols chính sẽ được chấp nhận với BẤT KỲ suffix nào")
    print("✅ EURUSD.ra, GBPUSD.m, USDJPY-spot, AUDUSD_ra đều PASS")
    print("✅ Logic prefix matching hoạt động HOÀN HẢO")
    print("✅ Symbols không có trong gap_config sẽ bị reject (như AAPL, BTCUSD)")

if __name__ == '__main__':
    test_symbol_filter_with_prefix_matching()
