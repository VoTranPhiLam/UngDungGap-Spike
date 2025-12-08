#!/usr/bin/env python3
"""
Script để xóa tất cả entries của RadexMarkets-Live và ZForexcapitalmarket-Server
trong gap_settings.json và spike_settings.json

Mục đích: Cho phép các FX symbols từ 2 brokers này sử dụng config từ file txt
thay vì bị override bởi gap_settings/spike_settings
"""

import json

def remove_broker_entries(file_path, brokers_to_remove):
    """
    Xóa tất cả entries của các brokers chỉ định trong file settings

    Args:
        file_path: Đường dẫn đến file json
        brokers_to_remove: List các broker names cần xóa
    """
    try:
        # Đọc file
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)

        # Đếm số entries trước khi xóa
        original_count = len(data)

        # Xóa entries
        removed_count = 0
        keys_to_remove = []

        for key in data.keys():
            # Check nếu key bắt đầu bằng broker name
            for broker in brokers_to_remove:
                if key.startswith(f"{broker}_"):
                    keys_to_remove.append(key)
                    removed_count += 1
                    break

        # Xóa keys
        for key in keys_to_remove:
            del data[key]

        # Ghi lại file
        with open(file_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)

        print(f"✅ {file_path}")
        print(f"   - Original entries: {original_count}")
        print(f"   - Removed entries: {removed_count}")
        print(f"   - Remaining entries: {len(data)}")

        if removed_count > 0:
            print(f"   - Removed brokers: {', '.join(brokers_to_remove)}")

        return removed_count

    except Exception as e:
        print(f"❌ Error processing {file_path}: {e}")
        return 0

def main():
    """Main function"""
    brokers_to_remove = [
        'RadexMarkets-Live',
        'ZForexcapitalmarket-Server'
    ]

    print("=" * 80)
    print("XÓA ENTRIES CỦA RADEX VÀ ZFOREX TRONG GAP/SPIKE SETTINGS")
    print("=" * 80)
    print()
    print("Mục đích: Cho phép các FX symbols từ 2 brokers này sử dụng")
    print("          config từ THAM_SO_GAP_INDICATOR.txt (Point-based)")
    print("          thay vì gap_settings.json/spike_settings.json (Percent-based)")
    print()
    print("Brokers sẽ bị xóa:")
    for broker in brokers_to_remove:
        print(f"  - {broker}")
    print()
    print("=" * 80)
    print()

    # Xóa trong gap_settings.json
    removed_gap = remove_broker_entries('gap_settings.json', brokers_to_remove)
    print()

    # Xóa trong spike_settings.json
    removed_spike = remove_broker_entries('spike_settings.json', brokers_to_remove)
    print()

    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total removed from gap_settings.json: {removed_gap}")
    print(f"Total removed from spike_settings.json: {removed_spike}")
    print(f"Total removed: {removed_gap + removed_spike}")
    print()

    if removed_gap + removed_spike > 0:
        print("✅ Thành công! Các FX symbols từ RadexMarkets-Live và ZForexcapitalmarket-Server")
        print("   giờ sẽ sử dụng config từ THAM_SO_GAP_INDICATOR.txt (Point-based)")
        print()
        print("   Ví dụ:")
        print("   - RadexMarkets-Live_EURUSD.ra → sử dụng EURUSD từ file txt (0.003)")
        print("   - ZForexcapitalmarket-Server_GBPUSD → sử dụng GBPUSD từ file txt (0.003)")
    else:
        print("ℹ️  Không có entries nào bị xóa (có thể đã xóa trước đó)")

if __name__ == '__main__':
    main()
