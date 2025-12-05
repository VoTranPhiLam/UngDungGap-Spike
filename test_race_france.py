#!/usr/bin/env python3
"""
Test script để phân tích vấn đề #RACE khớp với France120
"""

def is_subsequence_match_current(str1, str2, min_length=5):
    """Logic hiện tại"""
    str1_lower = str1.lower()
    str2_lower = str2.lower()

    def is_subsequence(pattern, text):
        if len(pattern) < min_length:
            return False

        pattern_idx = 0
        for char in text:
            if pattern_idx < len(pattern) and char == pattern[pattern_idx]:
                pattern_idx += 1

        return pattern_idx >= min_length

    result1 = is_subsequence(str1_lower, str2_lower)
    result2 = is_subsequence(str2_lower, str1_lower)

    print(f'\nTesting: "{str1}" vs "{str2}"')
    print(f'  is_subsequence("{str1_lower}", "{str2_lower}"): {result1}')
    print(f'  is_subsequence("{str2_lower}", "{str1_lower}"): {result2}')
    print(f'  Result: {result1 or result2}')

    return result1 or result2

# Test các trường hợp có thể gây nhầm lẫn
print('=' * 70)
print('PHÂN TÍCH VẤN ĐỀ: #RACE vs France120')
print('=' * 70)

test_cases = [
    ('#RACE', 'France120'),
    ('#RACE', 'france'),
    ('RACE', 'France120'),
    ('RACE', 'france'),
    ('#France120', 'France120'),
]

for str1, str2 in test_cases:
    is_subsequence_match_current(str1, str2)

print('\n' + '=' * 70)
print('PHÂN TÍCH CHI TIẾT: Tại sao "RACE" có thể khớp với "France120"?')
print('=' * 70)

# Kiểm tra từng bước
text = "france120"
pattern = "race"

print(f'\nPattern: "{pattern}"')
print(f'Text: "{text}"')
print('\nDuyệt qua từng ký tự của text:')

pattern_idx = 0
for i, char in enumerate(text):
    if pattern_idx < len(pattern):
        if char == pattern[pattern_idx]:
            print(f'  [{i}] "{char}" → MATCH với pattern[{pattern_idx}] = "{pattern[pattern_idx]}" ✅')
            pattern_idx += 1
        else:
            print(f'  [{i}] "{char}" → Không khớp với pattern[{pattern_idx}] = "{pattern[pattern_idx]}"')
    else:
        print(f'  [{i}] "{char}" → Pattern đã hoàn thành')

print(f'\nKết quả: Khớp được {pattern_idx} ký tự (min_length=5)')
print(f'pattern_idx ({pattern_idx}) >= min_length (5)? {pattern_idx >= 5}')

# Vấn đề: pattern "race" chỉ có 4 ký tự, không đủ min_length=5
# Nhưng nếu check len(pattern) < min_length → return False ngay
print(f'\nKiểm tra: len("{pattern}") = {len(pattern)} < min_length (5)? {len(pattern) < 5}')
print('→ Logic hiện tại sẽ return False ngay vì pattern quá ngắn')

print('\n' + '=' * 70)
print('KẾT LUẬN')
print('=' * 70)
print('Với logic hiện tại, "#RACE" KHÔNG NÊN khớp với "France120"')
print('vì "race" chỉ có 4 ký tự, không đủ min_length=5')
print('\nNếu vẫn xảy ra khớp sai, có thể do:')
print('1. Có logic khác đang được sử dụng')
print('2. Symbol được normalize/transform trước khi matching')
print('3. Có bug trong logic kiểm tra điều kiện len(pattern) < min_length')
