# ⚡ QUICK TEST - DELAY DETECTION

## 🚀 Test Nhanh (3 bước)

### Bước 1: Chạy ứng dụng
```bash
python gap_spike_detector.py
```

**Quan sát:**
- ✅ Bảng "⏱️ Delay Alert (Bid không đổi)" xuất hiện
- ✅ Có input "Delay (s): [180]" trên thanh control
- ✅ Có nút "Connected" thay vì bảng Connected Brokers
- ✅ Hiển thị: "✅ All symbols updating (threshold: 180s)"

---

### Bước 2: Chạy test script
**Mở terminal mới:**
```bash
python test_delay_detection.py
```

**Chọn test:**
```
1. Test Delay Detection (4 symbols, 200s)
2. Test Bid Change Removal (1 symbol, 230s)
3. Exit

Lựa chọn (1-3): 1
```

**Kết quả:**
```
⏱️  TEST DELAY DETECTION
========================================
📊 Test Scenarios:
   EURUSD     - Bid cố định - sẽ trigger delay
   GBPUSD     - Bid cố định - sẽ trigger delay
   XAUUSD     - Bid thay đổi - không delay
   USDJPY     - Bid cố định - sẽ trigger delay

⏱️  Sẽ gửi dữ liệu trong 200 giây (>180s threshold)...
   Bạn có thể:
   1. Mở ứng dụng Gap & Spike Detector
   2. Xem bảng 'Delay Alert' trên giao diện chính
   3. EURUSD, GBPUSD, USDJPY sẽ xuất hiện sau 180 giây
   4. XAUUSD sẽ không xuất hiện (bid thay đổi)

👉 Nhấn Enter để bắt đầu test...
```

---

### Bước 3: Quan sát kết quả

#### **0-180s: Chờ trigger**
```
[03:00] Iteration 180 - ⏳ Chờ delay trigger (0s còn lại)
```

**Delay Alert Board:**
```
┌────────────────────────────────────────────────────────┐
│ ⏱️ Delay Alert (Bid không đổi)                         │
├────────────────────────────────────────────────────────┤
│ No delays detected                                     │
│ ✅ All symbols updating (threshold: 180s)              │
└────────────────────────────────────────────────────────┘
```

#### **180-359s: Delay Warning (🟡)**
```
[03:05] Iteration 185 - ⚠️  DELAY TRIGGERED! Kiểm tra bảng Delay
```

**Delay Alert Board:**
```
┌────────────────────────────────────────────────────────────────┐
│ ⏱️ Delay Alert (Bid không đổi)                                 │
├────────────────────────────────────────────────────────────────┤
│ Broker       │ Symbol │ Bid     │ Last Change │ Delay  │...   │
├────────────────────────────────────────────────────────────────┤
│ DELAY-TEST.. │ EURUSD │ 1.08500 │ 14:20:00    │ 3m 5s  │⚠️... │ 🟡
│ DELAY-TEST.. │ GBPUSD │ 1.26500 │ 14:20:00    │ 3m 5s  │⚠️... │ 🟡
│ DELAY-TEST.. │ USDJPY │ 149.500 │ 14:20:00    │ 3m 5s  │⚠️... │ 🟡
└────────────────────────────────────────────────────────────────┘

❌ XAUUSD không xuất hiện (bid thay đổi)
```

#### **360s+: Critical Delay (🔴)**
```
[06:05] Iteration 365 - ⚠️  DELAY TRIGGERED! Kiểm tra bảng Delay
```

**Delay Alert Board:**
```
┌────────────────────────────────────────────────────────────────┐
│ ⏱️ Delay Alert (Bid không đổi)                                 │
├────────────────────────────────────────────────────────────────┤
│ Broker       │ Symbol │ Bid     │ Last Change │ Delay  │...   │
├────────────────────────────────────────────────────────────────┤
│ DELAY-TEST.. │ EURUSD │ 1.08500 │ 14:20:00    │ 6m 5s  │🔴... │ 🔴
│ DELAY-TEST.. │ GBPUSD │ 1.26500 │ 14:20:00    │ 6m 5s  │🔴... │ 🔴
│ DELAY-TEST.. │ USDJPY │ 149.500 │ 14:20:00    │ 6m 5s  │🔴... │ 🔴
└────────────────────────────────────────────────────────────────┘
```

---

## 🎯 Expected Results

### ✅ Phase 1 (0-180s):
- Bảng hiển thị: "✅ All symbols updating"
- Không có symbol nào trong bảng

### ✅ Phase 2 (180-359s):
- 3 symbols xuất hiện: EURUSD, GBPUSD, USDJPY
- Màu: 🟡 Vàng (warning)
- Status: ⚠️ DELAYED (Xm Ys)
- XAUUSD không xuất hiện

### ✅ Phase 3 (360s+):
- 3 symbols chuyển sang màu đỏ
- Màu: 🔴 Đỏ (critical)
- Status: 🔴 CRITICAL DELAY (Xm Ys)
- Delay time tăng dần

---

## 🧪 Test 2: Bid Change Removal

### Chạy test:
```bash
python test_delay_detection.py
```

**Chọn:** `2. Test Bid Change Removal`

### Timeline:

#### **0-180s: Chờ trigger**
```
📍 Phase 1: Gửi bid cố định (1.10000) trong 200s...
[00:30] ⏳ Phase 1: Bid cố định - 170s còn lại (Bid: 1.10000)
```

**Result:** Chưa có gì trong Delay board

#### **180-200s: TESTEUR xuất hiện**
```
[03:05] ⏳ Phase 1: Bid cố định - 115s còn lại (Bid: 1.10000)
```

**Delay Alert Board:**
```
┌─────────────────────────────────────────────────┐
│ REMOVAL-TEST │ TESTEUR │ 1.10000 │ ... │⚠️...  │ 🟡
└─────────────────────────────────────────────────┘
```

#### **200s: Bid thay đổi → Auto removal**
```
🔄 Phase 2: Thay đổi bid để test removal...
[03:20] ✅ Phase 2: Bid thay đổi - Symbol sẽ biến mất (Bid: 1.10050)
```

**Delay Alert Board:**
```
┌─────────────────────────────────────────────────┐
│ No delays detected                              │
│ ✅ All symbols updating (threshold: 180s)       │
└─────────────────────────────────────────────────┘

✅ TESTEUR đã biến mất!
```

---

## 🔧 Test Các Tính Năng

### Test 1: Thay đổi Delay Threshold
```
1. Trên app, thay đổi "Delay (s): [180]" → "Delay (s): [60]"
2. Chạy lại test script
3. Symbols sẽ xuất hiện sau 60s thay vì 180s
```

### Test 2: Connected Brokers Window
```
1. Click nút "Connected" trên app
2. Window mới mở ra hiển thị:
   - DELAY-TEST-BROKER
   - 4 Symbols
   - 🟢 Connected
   - Last Update: HH:MM:SS (Xs ago)
3. Đóng window → Main app vẫn hoạt động
```

### Test 3: Multiple Delays
```
1. Chạy test script Option 1
2. Chạy thêm test script Option 2 (terminal khác)
3. Delay board hiển thị:
   - 3 symbols từ DELAY-TEST-BROKER
   - 1 symbol từ REMOVAL-TEST
4. Tất cả sort by delay time (longest first)
```

---

## 📊 Visual Guide

### Timeline Test 1:
```
0s     180s                360s               200s
├───────┼────────────────────┼──────────────────┤
│       │                    │                  │
│ Chờ   │ 🟡 Warning        │ 🔴 Critical     │ End
│       │ 3 symbols         │ 3 symbols        │
│       │                   │                  │
└───────┴───────────────────┴──────────────────┘
```

### Timeline Test 2:
```
0s     180s       200s         230s
├───────┼──────────┼────────────┤
│       │          │            │
│ Chờ   │ 🟡 Delay│ ✅ Removed │ End
│       │ TESTEUR │ (bid đổi)  │
│       │          │            │
└───────┴──────────┴────────────┘
```

---

## 💡 Tips

### 1. Thay đổi threshold real-time
```
Không cần restart app
Thay đổi input → Delay board update ngay
```

### 2. Monitor nhiều terminals
```
Terminal 1: python gap_spike_detector.py
Terminal 2: python test_delay_detection.py (Option 1)
Terminal 3: python test_delay_detection.py (Option 2)
```

### 3. So sánh màu
```
🟡 Vàng = threshold ≤ delay < 2×threshold
🔴 Đỏ   = delay ≥ 2×threshold

VD: threshold=180s
  - 180-359s → 🟡
  - 360s+    → 🔴
```

---

## ❓ Troubleshooting

### Không thấy Delay board?
```
→ Kiểm tra app đang chạy
→ Reload browser (nếu web)
→ Check terminal có lỗi không
```

### Symbols không xuất hiện?
```
→ Đợi đủ threshold (180s)
→ Kiểm tra bid có thực sự cố định không
→ Xem Activity Log
```

### Màu không đúng?
```
→ Kiểm tra delay time
→ So với threshold × 2
→ Nếu delay < 360s → Vàng
→ Nếu delay ≥ 360s → Đỏ
```

### Connected button không hoạt động?
```
→ Click lại
→ Kiểm tra có lỗi trong log không
→ Restart app
```

---

## ✅ Checklist

Sau khi test, xác nhận:

- [ ] Delay board hiển thị đúng
- [ ] Input "Delay (s)" hoạt động
- [ ] Symbols xuất hiện sau threshold
- [ ] Màu vàng (180-359s)
- [ ] Màu đỏ (360s+)
- [ ] XAUUSD không xuất hiện (bid thay đổi)
- [ ] Auto removal khi bid thay đổi
- [ ] Connected button mở window
- [ ] Connected window hiển thị broker
- [ ] Multiple tests không conflict

---

**Chúc test thành công! ⏱️🚀**

Xem hướng dẫn đầy đủ: `DELAY_DETECTION_GUIDE.md`

