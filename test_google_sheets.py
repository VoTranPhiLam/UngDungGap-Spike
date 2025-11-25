#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Test script to send sample data to Google Sheets
"""

import gspread
from google.oauth2.service_account import Credentials
from datetime import datetime
import json
import os

CREDENTIALS_FILE = "credentials.json"
GOOGLE_SHEET_NAME = "Chấm công TestSanPython"
SHEET_ID_CACHE_FILE = "sheet_id_cache.json"

def send_test_data_to_google_sheets():
    """Send test data to Google Sheets"""
    
    print("="*70)
    print("  Test Google Sheets Integration")
    print("="*70)
    print()
    
    # Check credentials file
    if not os.path.exists(CREDENTIALS_FILE):
        print(f"❌ Error: {CREDENTIALS_FILE} not found!")
        return
    
    print(f"✅ Found {CREDENTIALS_FILE}")
    
    # Create sample accepted screenshot data
    sample_data = [
        {
            'server_time': '2024-10-20 14:30:00',
            'broker': 'ICM',
            'symbol': 'EURUSD',
            'detection_type': 'GAP UP',
            'percentage': '0.350%',
            'bid': '1.09500',
            'ask': '1.09520',
            'open': '1.09480',
            'high': '1.09550',
            'low': '1.09450',
            'close': '1.09510'
        },
        {
            'server_time': '2024-10-20 14:35:00',
            'broker': 'ICM',
            'symbol': 'GBPUSD',
            'detection_type': 'SPIKE',
            'percentage': '0.520%',
            'bid': '1.27500',
            'ask': '1.27520',
            'open': '1.27480',
            'high': '1.27550',
            'low': '1.27450',
            'close': '1.27510'
        }
    ]
    
    print(f"\n📊 Sample data to send: {len(sample_data)} items")
    for i, item in enumerate(sample_data, 1):
        print(f"   {i}. {item['server_time']} | {item['broker']} {item['symbol']} | {item['detection_type']} | {item['percentage']}")
    
    print("\n" + "="*70)
    confirm = input("Send this test data to Google Sheets? (yes/no): ").strip().lower()
    
    if confirm != 'yes':
        print("\n❌ Cancelled.")
        return
    
    try:
        # Authenticate with Google Sheets
        scopes = [
            'https://www.googleapis.com/auth/spreadsheets',
            'https://www.googleapis.com/auth/drive'
        ]
        
        print("\n🔐 Authenticating...")
        creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scopes)
        client = gspread.authorize(creds)
        
        print(f"✅ Authenticated as: {creds.service_account_email}")
        
        # Try to load cached sheet ID
        cached_sheet_id = None
        if os.path.exists(SHEET_ID_CACHE_FILE):
            try:
                with open(SHEET_ID_CACHE_FILE, 'r') as f:
                    cache_data = json.load(f)
                    cached_sheet_id = cache_data.get('sheet_id')
                    print(f"\n✅ Found cached sheet ID: {cached_sheet_id}")
            except:
                pass
        
        # Open or create the spreadsheet
        sheet = None
        spreadsheet = None
        
        if cached_sheet_id:
            # Try to open by cached ID first
            try:
                print(f"\n📂 Opening sheet by cached ID...")
                spreadsheet = client.open_by_key(cached_sheet_id)
                sheet = spreadsheet.sheet1
                print(f"✅ Opened cached sheet: {spreadsheet.title}")
            except Exception as e:
                print(f"⚠️  Cached sheet not accessible: {e}")
                cached_sheet_id = None
        
        if not sheet:
            # Try to open by name
            try:
                print(f"\n📂 Opening sheet by name: {GOOGLE_SHEET_NAME}")
                spreadsheet = client.open(GOOGLE_SHEET_NAME)
                sheet = spreadsheet.sheet1
                print(f"✅ Opened existing sheet: {spreadsheet.title}")
                
                # Cache the sheet ID for next time
                with open(SHEET_ID_CACHE_FILE, 'w') as f:
                    json.dump({'sheet_id': spreadsheet.id, 'sheet_name': spreadsheet.title}, f)
                    print(f"✅ Cached sheet ID for reuse")
                    
            except gspread.exceptions.SpreadsheetNotFound:
                # Create new spreadsheet ONLY if not exists
                print(f"\n📝 Sheet not found, creating new one...")
                spreadsheet = client.create(GOOGLE_SHEET_NAME)
                sheet = spreadsheet.sheet1
                
                # Share with service account email
                spreadsheet.share(creds.service_account_email, perm_type='user', role='writer')
                
                print(f"✅ Created new sheet: {GOOGLE_SHEET_NAME}")
                
                # Cache the sheet ID
                with open(SHEET_ID_CACHE_FILE, 'w') as f:
                    json.dump({'sheet_id': spreadsheet.id, 'sheet_name': spreadsheet.title}, f)
                    print(f"✅ Cached new sheet ID: {spreadsheet.id}")
        
        # Check if header exists, if not add it
        if sheet.row_count == 0 or sheet.cell(1, 1).value != 'Accepted Time':
            header = ['Accepted Time', 'Server Time', 'Broker', 'Symbol', 'Type', 'Percentage', 
                     'Bid', 'Ask', 'Open', 'High', 'Low', 'Close']
            sheet.append_row(header)
            print(f"\n✅ Added header row")
        
        # Prepare rows to append
        rows = []
        for item in sample_data:
            row = [
                datetime.now().strftime('%Y-%m-%d %H:%M:%S'),  # Accepted time
                item.get('server_time', ''),
                item.get('broker', ''),
                item.get('symbol', ''),
                item.get('detection_type', ''),
                item.get('percentage', ''),
                item.get('bid', ''),
                item.get('ask', ''),
                item.get('open', ''),
                item.get('high', ''),
                item.get('low', ''),
                item.get('close', '')
            ]
            rows.append(row)
        
        # Append all rows at once
        print(f"\n📤 Sending {len(rows)} rows to Google Sheets...")
        sheet.append_rows(rows)
        
        # Get spreadsheet URL
        sheet_url = spreadsheet.url
        
        print("\n" + "="*70)
        print("  ✅ SUCCESS!")
        print("="*70)
        print(f"\n📊 Sheet Name: {spreadsheet.title}")
        print(f"📊 Sheet URL: {sheet_url}")
        print(f"📊 Rows Added: {len(rows)}")
        print()
        print("🎉 Bạn có thể mở link trên để xem data!")
        print()
        
        # Show cache info
        if os.path.exists(SHEET_ID_CACHE_FILE):
            print("✅ Sheet ID đã được cache vào file: sheet_id_cache.json")
            print("   Lần sau gửi data sẽ nhanh hơn!")
        
    except Exception as e:
        print("\n" + "="*70)
        print("  ❌ ERROR")
        print("="*70)
        print(f"\nLỗi: {str(e)}")
        print()
        
        # Check for common errors
        error_str = str(e)
        if 'Drive storage quota' in error_str or 'storageQuotaExceeded' in error_str:
            print("⚠️  Lỗi Drive quota!")
            print("   Giải pháp:")
            print("   1. Chạy: python cleanup_selective.py")
            print("   2. Hoặc: python setup_google_sheet.py (dùng Drive của bạn)")
        elif 'Drive API' in error_str or 'drive.googleapis.com' in error_str:
            print("⚠️  Google Drive API chưa enable!")
            print("   Giải pháp:")
            print("   1. Mở: https://console.developers.google.com/apis/api/drive.googleapis.com/overview")
            print("   2. Click 'ENABLE'")
            print("   3. Đợi 1-2 phút, rồi thử lại")
        elif 'Permission denied' in error_str or '403' in error_str:
            print("⚠️  Lỗi permission!")
            print("   Giải pháp:")
            print("   1. Check credentials.json có đúng không")
            print("   2. Check APIs đã enable chưa (Sheets API + Drive API)")

if __name__ == "__main__":
    send_test_data_to_google_sheets()

