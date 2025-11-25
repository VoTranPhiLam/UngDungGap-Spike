#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Script to setup Google Sheet in YOUR Drive (not service account Drive)
This avoids the 15GB quota limit of service account
"""

import gspread
from google.oauth2.service_account import Credentials
import json

CREDENTIALS_FILE = "credentials.json"
SHEET_NAME = "Chấm công TestSanPython"

def get_service_account_email():
    """Get service account email from credentials file"""
    try:
        with open(CREDENTIALS_FILE, 'r') as f:
            creds_data = json.load(f)
            return creds_data.get('client_email', 'N/A')
    except Exception as e:
        return f"Error: {e}"

def setup_sheet():
    """Create sheet and get instructions"""
    print("="*70)
    print("  Google Sheets Setup - Use YOUR Drive (Unlimited Storage!)")
    print("="*70)
    print()
    
    # Get service account email
    sa_email = get_service_account_email()
    print(f"📧 Service Account Email: {sa_email}")
    print()
    print("="*70)
    print("  HƯỚNG DẪN SETUP (3 BƯỚC - 2 PHÚT)")
    print("="*70)
    print()
    
    print("📝 BƯỚC 1: Tạo Google Sheet trong Drive CỦA BẠN")
    print("-" * 70)
    print("1. Vào: https://drive.google.com")
    print("2. Click 'New' → 'Google Sheets' → 'Blank spreadsheet'")
    print(f"3. Đổi tên thành: '{SHEET_NAME}'")
    print()
    
    print("📧 BƯỚC 2: Share Sheet với Service Account")
    print("-" * 70)
    print("1. Click nút 'Share' (góc trên bên phải)")
    print(f"2. Add email: {sa_email}")
    print("3. Quyền: 'Editor' (không phải 'Viewer'!)")
    print("4. Click 'Send'")
    print()
    
    print("🔑 BƯỚC 3: Copy Sheet ID")
    print("-" * 70)
    print("1. Copy URL của sheet:")
    print("   https://docs.google.com/spreadsheets/d/SHEET_ID_HERE/edit")
    print("                                              ^^^^^^^^^^^^^")
    print("2. Copy phần SHEET_ID_HERE")
    print("3. Paste vào bên dưới")
    print()
    print("="*70)
    
    sheet_id = input("\n✏️  Nhập Sheet ID (hoặc Enter để skip): ").strip()
    
    if not sheet_id:
        print("\n⏭️  Skipped. Bạn có thể làm thủ công sau.")
        print("\n📝 Sau khi có Sheet ID, sửa file gap_spike_detector.py:")
        print("   Tìm dòng: GOOGLE_SHEET_NAME = \"Chấm công TestSanPython\"")
        print("   Thay bằng: GOOGLE_SHEET_ID = \"YOUR_SHEET_ID_HERE\"")
        print("   Và sửa code dùng: client.open_by_key(GOOGLE_SHEET_ID)")
        return
    
    # Test access
    print("\n🔍 Testing access to sheet...")
    try:
        scopes = [
            'https://www.googleapis.com/auth/spreadsheets',
            'https://www.googleapis.com/auth/drive'
        ]
        
        creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scopes)
        client = gspread.authorize(creds)
        
        # Try to open the sheet
        sheet = client.open_by_key(sheet_id)
        worksheet = sheet.sheet1
        
        print(f"✅ Success! Can access sheet: '{sheet.title}'")
        print(f"   URL: {sheet.url}")
        
        # Add header if not exists
        if worksheet.row_count == 0 or worksheet.cell(1, 1).value != 'Accepted Time':
            header = ['Accepted Time', 'Server Time', 'Broker', 'Symbol', 'Type', 'Percentage', 
                     'Bid', 'Ask', 'Open', 'High', 'Low', 'Close']
            worksheet.append_row(header)
            print(f"✅ Added header row")
        
        # Save to config file
        config = {
            'sheet_id': sheet_id,
            'sheet_name': sheet.title,
            'sheet_url': sheet.url
        }
        
        with open('google_sheet_config.json', 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2, ensure_ascii=False)
        
        print(f"✅ Saved config to: google_sheet_config.json")
        print()
        print("="*70)
        print("  🎉 SETUP COMPLETE!")
        print("="*70)
        print()
        print("📊 Sheet Info:")
        print(f"   Name: {sheet.title}")
        print(f"   ID: {sheet_id}")
        print(f"   URL: {sheet.url}")
        print()
        print("✅ Bây giờ chương trình sẽ ghi data vào sheet CỦA BẠN")
        print("✅ KHÔNG còn lỗi Drive quota nữa!")
        print()
        print("🚀 Chạy lại chương trình:")
        print("   python gap_spike_detector.py")
        
    except Exception as e:
        print(f"❌ Error: {e}")
        print()
        print("⚠️  Có thể do:")
        print("   1. Sheet ID sai")
        print("   2. Chưa share với service account")
        print("   3. Quyền chỉ là 'Viewer' (cần 'Editor')")
        print()
        print("📝 Hãy kiểm tra lại và thử lại!")

if __name__ == "__main__":
    setup_sheet()

