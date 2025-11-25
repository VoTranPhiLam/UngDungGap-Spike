# 📊 CÔNG THỨC TÍNH GAP & SPIKE HIỆN TẠI

**Version:** 2.8.1+
**Ngày cập nhật:** 15/10/2025

---

## 📈 CÔNG THỨC GAP

### Định Nghĩa:
**Gap** = Khoảng cách giữa giá **Open** của nến hiện tại so với **Close** của nến trước đó.

### Công Thức:

```
Gap % = (Open_hiện_tại - Close_trước) / Close_trước × 100
```

### Chi Tiết:

**Dữ liệu sử dụng:**
```python
prev_close = prev_ohlc['close']        # Nến M1 index 1 (nến trước - đã đóng)
current_open = current_ohlc['open']    # Nến M1 index 0 (nến hiện tại)
```

**Tính toán:**
```python
gap_percentage = ((current_open - prev_close) / prev_close * 100)
```

**Xác định hướng:**
```python
- Nếu gap_percentage > 0  → GAP UP (giá mở cửa cao hơn giá đóng trước)
- Nếu gap_percentage < 0  → GAP DOWN (giá mở cửa thấp hơn giá đóng trước)
- Nếu gap_percentage = 0  → NONE (không có gap)
```

**Điều kiện cảnh báo:**
```python
- Nếu |gap_percentage| >= gap_threshold → DETECTED (cảnh báo Gap)
```

---

### Ví Dụ Gap:

#### Gap UP:
```
Nến trước (14:29):
  Close = 1.0500

Nến hiện tại (14:30):
  Open = 1.0515

Gap % = (1.0515 - 1.0500) / 1.0500 × 100
      = 0.0015 / 1.0500 × 100
      = 0.143%

→ GAP UP: 0.143%
→ Nếu gap_threshold = 0.1% → CẢNH BÁO ✅
```

#### Gap DOWN:
```
Nến trước (14:29):
  Close = 1.0500

Nến hiện tại (14:30):
  Open = 1.0485

Gap % = (1.0485 - 1.0500) / 1.0500 × 100
      = -0.0015 / 1.0500 × 100
      = -0.143%

→ GAP DOWN: 0.143% (lấy trị tuyệt đối)
→ Nếu gap_threshold = 0.1% → CẢNH BÁO ✅
```

---

## ⚡ CÔNG THỨC SPIKE (BIDIRECTIONAL)

### Định Nghĩa:
**Spike** = Biến động mạnh **trong** nến hiện tại so với giá Close của nến trước đó.

**Phát hiện 2 chiều:**
1. **Spike UP** = High của nến hiện tại cao hơn Close trước nhiều
2. **Spike DOWN** = Low của nến hiện tại thấp hơn Close trước nhiều

### Công Thức:

```
Spike UP % = (High_hiện_tại - Close_trước) / Close_trước × 100

Spike DOWN % = (Close_trước - Low_hiện_tại) / Close_trước × 100
```

**Lấy giá trị lớn nhất:**
```
Spike % = MAX(|Spike UP %|, |Spike DOWN %|)
```

### Chi Tiết:

**Dữ liệu sử dụng:**
```python
prev_close = prev_ohlc['close']         # Nến M1 index 1 (nến trước - đã đóng)
current_high = current_ohlc['high']     # Nến M1 index 0 (High của nến hiện tại)
current_low = current_ohlc['low']       # Nến M1 index 0 (Low của nến hiện tại)
```

**Tính toán:**
```python
# Spike UP
spike_up = ((current_high - prev_close) / prev_close * 100)
spike_up_abs = abs(spike_up)

# Spike DOWN
spike_down = ((prev_close - current_low) / prev_close * 100)
spike_down_abs = abs(spike_down)
```

**Xác định loại Spike:**
```python
if spike_up_abs > spike_down_abs:
    → SPIKE UP (biến động tăng mạnh hơn)
    → Giá trị: spike_up_abs
    
else:
    → SPIKE DOWN (biến động giảm mạnh hơn)
    → Giá trị: spike_down_abs
```

**Điều kiện cảnh báo:**
```python
- Nếu spike_up_abs >= spike_threshold   → SPIKE UP DETECTED
- Nếu spike_down_abs >= spike_threshold → SPIKE DOWN DETECTED
- Cảnh báo nếu 1 trong 2 vượt ngưỡng
```

---

### Ví Dụ Spike:

#### Spike UP (Tăng mạnh):
```
Nến trước (14:29):
  Close = 1.0500

Nến hiện tại (14:30):
  High = 1.0550
  Low = 1.0480

Tính toán:
  Spike UP = (1.0550 - 1.0500) / 1.0500 × 100
           = 0.0050 / 1.0500 × 100
           = 0.476%

  Spike DOWN = (1.0500 - 1.0480) / 1.0500 × 100
             = 0.0020 / 1.0500 × 100
             = 0.190%

So sánh:
  Spike UP (0.476%) > Spike DOWN (0.190%)

→ SPIKE UP: 0.476%
→ Nếu spike_threshold = 0.3% → CẢNH BÁO ✅
```

#### Spike DOWN (Giảm mạnh):
```
Nến trước (14:29):
  Close = 1.0500

Nến hiện tại (14:30):
  High = 1.0510
  Low = 1.0430

Tính toán:
  Spike UP = (1.0510 - 1.0500) / 1.0500 × 100
           = 0.0010 / 1.0500 × 100
           = 0.095%

  Spike DOWN = (1.0500 - 1.0430) / 1.0500 × 100
             = 0.0070 / 1.0500 × 100
             = 0.667%

So sánh:
  Spike DOWN (0.667%) > Spike UP (0.095%)

→ SPIKE DOWN: 0.667%
→ Nếu spike_threshold = 0.3% → CẢNH BÁO ✅
```

#### Spike 2 Chiều Đều Mạnh:
```
Nến trước (14:29):
  Close = 1.0500

Nến hiện tại (14:30):
  High = 1.0560   (tăng mạnh)
  Low = 1.0440    (giảm mạnh)

Tính toán:
  Spike UP = (1.0560 - 1.0500) / 1.0500 × 100
           = 0.571%

  Spike DOWN = (1.0500 - 1.0440) / 1.0500 × 100
             = 0.571%

→ Cả 2 đều vượt ngưỡng 0.3%!
→ CẢNH BÁO: SPIKE UP: 0.571% (vì bằng nhau, ưu tiên UP)
```

---

## 🔍 SO SÁNH GAP vs SPIKE

| Đặc điểm | GAP | SPIKE |
|----------|-----|-------|
| **Định nghĩa** | Khoảng cách Open hiện tại vs Close trước | Biến động trong nến so với Close trước |
| **Dữ liệu** | Open vs Close | High/Low vs Close |
| **Thời điểm** | Mở cửa nến mới | Trong quá trình nến |
| **Phát hiện** | 1 chiều (UP/DOWN) | 2 chiều (UP & DOWN) |
| **Nguyên nhân** | Gap giá giữa 2 nến | Biến động mạnh trong nến |

### Ví Dụ Phân Biệt:

```
Nến 14:29:
  Close = 1.0500

Nến 14:30:
  Open  = 1.0515 ← Gap UP (so với Close 1.0500)
  High  = 1.0560 ← Spike UP (so với Close 1.0500)
  Low   = 1.0480 ← Spike DOWN (so với Close 1.0500)
  Close = 1.0520

Kết quả:
  Gap UP   = (1.0515 - 1.0500) / 1.0500 × 100 = 0.143%
  Spike UP = (1.0560 - 1.0500) / 1.0500 × 100 = 0.571%
  Spike DN = (1.0500 - 1.0480) / 1.0500 × 100 = 0.190%

→ Gap: 0.143%
→ Spike: 0.571% (UP mạnh hơn)
```

---

## 📋 NGƯỠNG MẶC ĐỊNH

### Gap:
```
gap_threshold = 0.3%  (mặc định)
```

### Spike:
```
spike_threshold = 0.5%  (mặc định)
```

**Có thể tùy chỉnh:**
- Theo từng sản phẩm: `EURUSD`, `XAUUSD`, ...
- Theo broker: `Exness_EURUSD`, ...
- Theo nhóm: `Exness_*`, ...
- Toàn bộ: `*`

---

## 💡 LƯU Ý QUAN TRỌNG

### Dữ Liệu Chart Hiện Tại:

**⚠️ VẤN ĐỀ PHÁT HIỆN:**
```python
# Code hiện tại đang dùng:
current_ohlc = symbol_data.get('current_ohlc', {})  # Index 0 - Đang hình thành
```

**Vấn đề:**
```
❌ current_ohlc = Nến index 0 (đang hình thành)
   → Close thay đổi mỗi tick
   → High/Low thay đổi liên tục
   → Không ổn định
   → Chart không chính xác!
```

**Giải pháp:**
```python
# Nên dùng:
prev_ohlc = symbol_data.get('prev_ohlc', {})  # Index 1 - Đã đóng
```

**Lợi ích:**
```
✅ prev_ohlc = Nến index 1 (đã đóng)
   → OHLC đã xác định
   → Không thay đổi
   → Ổn định
   → Chart chính xác như MT4!
```

---

## 🎯 TÓM TẮT

### GAP:
```
Gap % = (Open_hiện_tại - Close_trước) / Close_trước × 100

- Phát hiện khoảng cách giá giữa 2 nến
- So sánh Open với Close
- 1 chiều (UP/DOWN)
```

### SPIKE:
```
Spike UP % = (High_hiện_tại - Close_trước) / Close_trước × 100
Spike DOWN % = (Close_trước - Low_hiện_tại) / Close_trước × 100

Spike % = MAX(|Spike UP|, |Spike DOWN|)

- Phát hiện biến động mạnh trong nến
- So sánh High/Low với Close
- 2 chiều (UP & DOWN)
- Lấy giá trị lớn nhất
```

---

**📌 Công thức này đảm bảo:**
- ✅ Phát hiện chính xác Gap và Spike
- ✅ Hỗ trợ 2 chiều cho Spike
- ✅ Tính toán theo % chuẩn
- ✅ Dễ tùy chỉnh ngưỡng

