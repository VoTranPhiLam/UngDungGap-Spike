#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Script to selectively delete Google Sheets
"""

import gspread
from google.oauth2.service_account import Credentials

CREDENTIALS_FILE = "credentials.json"

# IDs của các sheets CẦN XÓA (test sheets)
SHEETS_TO_DELETE = [
    "1AC7GoD-X8skThindFbaT78H4mjjiUMn4mLRVTiuNxI4",  # Untitled spreadsheet
    "1Ls-qThAqd2ML6YPfv41krsRr5woEPOdN_7TechB2Pz0",  # Bảng tính không có tiêu đề
    "1ob2uL3TXOzOwTA1YvdiB9Cm8fR1AiQ6WAji5amk3b8A",  # Bảng tính không có tiêu đề
    "1L9OuwV9oK1k_ZJvCvTYJaPMF7PVBUY9-FdjOk24LvvY",  # Bảng tính không có tiêu đề
    "1bg3tKXdpV0SrDIHUR3RrjvZ7iV6aHI_FchXvjJHOULs",  # Trang Tính
]

def delete_selected_sheets():
    """Delete only selected test sheets"""
    try:
        # Authenticate
        scopes = [
            'https://www.googleapis.com/auth/spreadsheets',
            'https://www.googleapis.com/auth/drive'
        ]
        
        print("🔐 Authenticating...")
        creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scopes)
        client = gspread.authorize(creds)
        
        print("\n🗑️  Deleting test sheets...\n")
        
        for sheet_id in SHEETS_TO_DELETE:
            try:
                # Get sheet info first
                sheet = client.open_by_key(sheet_id)
                print(f"Deleting: {sheet.title}")
                
                # Delete
                client.del_spreadsheet(sheet_id)
                print(f"✅ Deleted: {sheet.title}\n")
            except Exception as e:
                print(f"❌ Failed to delete {sheet_id}: {e}\n")
        
        print("✅ Cleanup complete!")
        print("\n📊 Sheets KHÔNG bị xóa (giữ nguyên):")
        print("  - Group 7A")
        print("  - Sổ Tài Khoản 5A 2025")
        print("  - Quản Lý TK Tổng Group 5C")
        print("  - 5C")
        print("  - Kèo team 7A")
        print("  - Auto_Euquity")
    
    except FileNotFoundError:
        print(f"❌ Error: {CREDENTIALS_FILE} not found!")
    except Exception as e:
        print(f"❌ Error: {e}")

if __name__ == "__main__":
    print("="*60)
    print("  Selective Google Drive Cleanup")
    print("="*60)
    print("\n⚠️  Will delete 5 test sheets (empty/untitled)")
    print("✅ Will keep all important sheets (Group 7A, Sổ Tài Khoản, etc.)")
    print("\n" + "="*60)
    
    confirm = input("\nContinue? (yes/no): ").strip().lower()
    
    if confirm == 'yes':
        delete_selected_sheets()
    else:
        print("\n❌ Cancelled.")

