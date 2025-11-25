#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Script to clean up old Google Sheets from service account Drive
"""

import gspread
from google.oauth2.service_account import Credentials

CREDENTIALS_FILE = "credentials.json"

def list_and_delete_old_sheets():
    """List all sheets and optionally delete them"""
    try:
        # Authenticate
        scopes = [
            'https://www.googleapis.com/auth/spreadsheets',
            'https://www.googleapis.com/auth/drive'
        ]
        
        print("🔐 Authenticating...")
        creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scopes)
        client = gspread.authorize(creds)
        
        # List all spreadsheets
        print("\n📊 Listing all Google Sheets in service account Drive...\n")
        spreadsheets = client.openall()
        
        if not spreadsheets:
            print("✅ No sheets found. Drive is clean!")
            return
        
        print(f"Found {len(spreadsheets)} spreadsheet(s):\n")
        
        for i, sheet in enumerate(spreadsheets, 1):
            print(f"{i}. {sheet.title}")
            print(f"   ID: {sheet.id}")
            print(f"   URL: {sheet.url}")
            print(f"   Worksheets: {len(sheet.worksheets())}")
            print()
        
        # Ask if user wants to delete
        print("\n" + "="*60)
        print("⚠️  WARNING: Deletion is PERMANENT!")
        print("="*60)
        
        choice = input("\nDo you want to DELETE all sheets? (yes/no): ").strip().lower()
        
        if choice == 'yes':
            print("\n🗑️  Deleting sheets...")
            for sheet in spreadsheets:
                try:
                    client.del_spreadsheet(sheet.id)
                    print(f"✅ Deleted: {sheet.title}")
                except Exception as e:
                    print(f"❌ Failed to delete {sheet.title}: {e}")
            
            print("\n✅ Cleanup complete!")
        else:
            print("\n❌ Deletion cancelled.")
            print("\nℹ️  To delete specific sheets manually:")
            print("   1. Open the URL above")
            print("   2. File → Move to trash")
    
    except FileNotFoundError:
        print(f"❌ Error: {CREDENTIALS_FILE} not found!")
    except Exception as e:
        print(f"❌ Error: {e}")

if __name__ == "__main__":
    print("="*60)
    print("  Google Drive Cleanup Tool for Service Account")
    print("="*60)
    list_and_delete_old_sheets()

