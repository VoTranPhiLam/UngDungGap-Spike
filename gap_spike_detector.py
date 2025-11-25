#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Gap & Spike Detector - Desktop Application
Phát hiện Gap và Spike từ dữ liệu MT4/MT5 EA
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, simpledialog, filedialog
import threading
import json
import time
import sys
from datetime import datetime, timezone
from flask import Flask, request, jsonify
import logging
from collections import defaultdict
import os
import platform
import subprocess
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib.figure import Figure
import matplotlib.dates as mdates
from matplotlib.patches import Rectangle
import numpy as np
from PIL import Image, ImageTk
import glob
import gspread
from google.oauth2.service_account import Credentials
from concurrent.futures import ThreadPoolExecutor

# ===================== CONFIGURATION =====================
HTTP_PORT = 80
HTTP_HOST = '0.0.0.0'

# Cấu hình logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('gap_spike_detector.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# ===================== FLASK APP =====================
app = Flask(__name__)
app.logger.disabled = True
log = logging.getLogger('werkzeug')
log.disabled = True

# ===================== GLOBAL DATA STORAGE =====================
market_data = {}  # {broker: {symbol: data}}
gap_settings = {}  # {symbol: threshold%} or {broker_symbol: threshold%}
spike_settings = {}  # {symbol: threshold%} or {broker_symbol: threshold%}

DEFAULT_GAP_THRESHOLD = 0.3
DEFAULT_SPIKE_THRESHOLD = 1.3
gap_spike_results = {}  # {broker_symbol: {gap_info, spike_info}}
alert_board = {}  # {broker_symbol: {data, last_detected_time, grace_period_start}}
bid_tracking = {}  # {broker_symbol: {last_bid, last_change_time, first_seen_time}}
candle_data = {}  # {broker_symbol: [(timestamp, open, high, low, close), ...]}
manual_hidden_delays = {}  # {broker_symbol: True} - Manually hidden symbols
delay_settings = {
    'threshold': 180,  # Default delay threshold in seconds
    'auto_hide_time': 3600  # Auto hide after 60 minutes
}
screenshot_settings = {
    'enabled': True,  # Auto screenshot when gap/spike detected
    'save_gap': True,  # Save screenshot for gap
    'save_spike': True,  # Save screenshot for spike
    'folder': 'pictures',  # Folder to save screenshots
    'assigned_name': ''  # Selected name for Picture Gallery exports
}

# ===================== AUDIO ALERT SETTINGS =====================
audio_settings = {
    'enabled': True,  # Enable audio alerts
    'gap_sound': 'sounds/Gap.wav',  # Sound file for Gap detection
    'spike_sound': 'sounds/Spike.wav',  # Sound file for Spike detection
    'delay_sound': 'sounds/Delay.wav'  # Sound file for Delay detection
}

# Track which (broker, symbol, type) combinations have already played sound
audio_played_tracking = {}  # {broker_symbol_type: last_played_time}
AUDIO_REPLAY_COOLDOWN = 30  # Only allow replaying the same alert after 30 seconds

symbol_filter_settings = {
    'enabled': False,  # Chỉ xét Gap/Spike cho symbols được chọn khi bật
    'selection': {}    # {broker: [symbol1, symbol2], '*': [...]} - danh sách symbols được bật
}

SYMBOL_FILTER_FILE = 'symbol_filter_settings.json'

PICTURE_ASSIGNEE_CHOICES = [
    '',  # Allow clearing selection
    'Tâm',
    'Phát',
    'Tuấn',
    'Phi',
    'Khang',
    'Lâm'
]
market_open_settings = {
    'only_check_open_market': True,  # Only check gap/spike when market is open - DEFAULT: ON
    'skip_minutes_after_open': 0  # Skip X minutes after market opens (0 = disabled)
}

# Auto-send to Google Sheets settings
auto_send_settings = {
    'enabled': False,  # Enable auto-send when screenshot is captured
    'sheet_url': '',  # Google Sheet URL (user will fill this)
    'sheet_name': '',  # Sheet tab name (e.g., "Sheet1", "Data")
    'start_column': 'A',  # Column to start writing data (e.g., A, B, C)
    'columns': {  # Column mapping - which data to send
        'assignee': True,
        'time': True,
        'broker': True,
        'symbol': True,
        'type': True,  # Gap/Spike/Both
        'percentage': True
    }
}

python_reset_settings = {
    'enabled': False,  # Enable periodic Python reset
    'interval_minutes': 30  # Interval in minutes
}

PYTHON_RESET_SETTINGS_FILE = 'python_reset_settings.json'

# Google Sheets integration
accepted_screenshots = []  # List of accepted screenshots to send to Google Sheets
GOOGLE_SHEET_NAME = "Chấm công TestSanPython"  # Name of the Google Sheet
CREDENTIALS_FILE = "credentials.json"  # Google service account credentials
SHEET_ID_CACHE_FILE = "sheet_id_cache.json"  # Cache sheet ID to reuse (avoid creating duplicates)

data_lock = threading.Lock()

# ===================== THREAD POOL EXECUTORS =====================
# Giới hạn số lượng threads đồng thời để tránh resource exhaustion
audio_executor = ThreadPoolExecutor(max_workers=5, thread_name_prefix='audio')
screenshot_executor = ThreadPoolExecutor(max_workers=3, thread_name_prefix='screenshot')
# Data processing executor - xử lý symbols song song trong Flask endpoint
data_processing_executor = ThreadPoolExecutor(max_workers=4, thread_name_prefix='data_proc')

# ===================== DATE CACHE =====================
# Cache today's date để tránh gọi datetime.now() nhiều lần (system call overhead)
_today_date_cache = {'date': None, 'timestamp': 0}

def get_today_date():
    """
    Get today's date with caching (cache for 60 seconds)
    Tránh gọi datetime.now().date() nhiều lần gây system call overhead
    """
    current_time = time.time()
    if current_time - _today_date_cache['timestamp'] > 60:  # Cache 60 giây
        _today_date_cache['date'] = datetime.now().date()
        _today_date_cache['timestamp'] = current_time
    return _today_date_cache['date']

# ===================== MARKET OPEN HELPER =====================
def is_within_skip_period_after_open(symbol, broker, current_timestamp):
    """
    Kiểm tra xem có đang trong khoảng thời gian skip sau khi market mở cửa không
    
    Args:
        symbol: Symbol name
        broker: Broker name
        current_timestamp: Unix timestamp hiện tại
    
    Returns:
        True nếu đang trong skip period, False nếu không
    """
    try:
        skip_minutes = market_open_settings.get('skip_minutes_after_open', 0)
        if skip_minutes <= 0:
            return False  # Không skip
        
        # Lấy data
        if broker not in market_data or symbol not in market_data[broker]:
            return False
        
        symbol_data = market_data[broker][symbol]
        trade_sessions = symbol_data.get('trade_sessions', {})
        
        if not trade_sessions:
            return False
        
        # Parse current time
        from datetime import datetime as dt_class
        current_dt = server_timestamp_to_datetime(current_timestamp)
        current_day = trade_sessions.get('current_day', '')
        current_hour = current_dt.hour
        current_minute = current_dt.minute
        current_time_minutes = current_hour * 60 + current_minute
        
        # Tìm session hiện tại đang active
        days_data = trade_sessions.get('days', [])
        for day_info in days_data:
            if day_info.get('day') == current_day:
                sessions = day_info.get('sessions', [])
                for session in sessions:
                    start_str = session.get('start', '')  # Format: "HH:MM"
                    end_str = session.get('end', '')      # Format: "HH:MM"
                    
                    if not start_str or not end_str:
                        continue
                    
                    # Parse start/end time
                    start_parts = start_str.split(':')
                    end_parts = end_str.split(':')
                    
                    if len(start_parts) != 2 or len(end_parts) != 2:
                        continue
                    
                    start_hour = int(start_parts[0])
                    start_minute = int(start_parts[1])
                    end_hour = int(end_parts[0])
                    end_minute = int(end_parts[1])
                    
                    start_time_minutes = start_hour * 60 + start_minute
                    end_time_minutes = end_hour * 60 + end_minute
                    
                    # Kiểm tra session có cross midnight không
                    if start_time_minutes <= end_time_minutes:
                        # Normal session (không qua đêm)
                        if start_time_minutes <= current_time_minutes <= end_time_minutes:
                            # Đang trong session này
                            minutes_since_open = current_time_minutes - start_time_minutes
                            if minutes_since_open < skip_minutes:
                                return True  # Đang trong skip period
                    else:
                        # Cross midnight session
                        if current_time_minutes >= start_time_minutes or current_time_minutes <= end_time_minutes:
                            # Đang trong session
                            if current_time_minutes >= start_time_minutes:
                                minutes_since_open = current_time_minutes - start_time_minutes
                            else:
                                minutes_since_open = (24 * 60 - start_time_minutes) + current_time_minutes
                            
                            if minutes_since_open < skip_minutes:
                                return True
        
        return False  # Không trong skip period
        
    except Exception as e:
        logger.error(f"Error checking skip period: {e}")
        return False

# ===================== TIMESTAMP HELPER =====================
def server_timestamp_to_datetime(timestamp):
    """
    Convert server timestamp to datetime WITHOUT local timezone conversion
    
    EA sends TimeCurrent() which is broker's server time as Unix timestamp.
    We keep it as UTC to avoid conversion to local timezone (GMT+7).
    
    Example:
        Server time (marketwatch): 02:30
        Without this: Python converts to local → 09:30 GMT+7 (WRONG!)
        With this: Displays as 02:30 (CORRECT!)
    
    Args:
        timestamp: Unix timestamp from server (seconds since epoch)
    
    Returns:
        datetime object representing server time (UTC-based)
    """
    try:
        # Use timezone.utc to avoid deprecation warning in Python 3.12+
        return datetime.fromtimestamp(timestamp, tz=timezone.utc).replace(tzinfo=None)
    except:
        # Fallback for older Python versions
        return datetime.utcfromtimestamp(timestamp)

# ===================== GOOGLE SHEETS INTEGRATION =====================
def push_to_google_sheets(accepted_items):
    """
    Push accepted screenshot data to Google Sheets (using config from auto_send_settings)
    
    Args:
        accepted_items: List of screenshot data dictionaries
    
    Returns:
        (success: bool, message: str)
    """
    try:
        if not os.path.exists(CREDENTIALS_FILE):
            return False, f"❌ Không tìm thấy file {CREDENTIALS_FILE}"
        
        if not accepted_items:
            return False, "⚠️ Chưa có hình nào được Accept"
        
        # Check if auto_send settings configured
        sheet_url = auto_send_settings.get('sheet_url', '').strip()
        if not sheet_url:
            return False, "⚠️ Chưa cấu hình Google Sheet!\n\nVui lòng vào Settings → Auto-Send Sheets để cấu hình Sheet URL."
        
        # Authenticate with Google Sheets
        scopes = [
            'https://www.googleapis.com/auth/spreadsheets',
            'https://www.googleapis.com/auth/drive'
        ]
        
        logger.info("Authenticating with Google Sheets...")
        creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scopes)
        client = gspread.authorize(creds)
        
        # Extract sheet ID from URL
        import re
        match = re.search(r'/spreadsheets/d/([a-zA-Z0-9-_]+)', sheet_url)
        if not match:
            return False, f"❌ URL không hợp lệ!\n\nURL phải có dạng:\nhttps://docs.google.com/spreadsheets/d/YOUR_SHEET_ID/..."
        
        sheet_id = match.group(1)
        logger.info(f"Opening sheet by ID: {sheet_id}")
        spreadsheet = client.open_by_key(sheet_id)
        
        # Get the specified sheet (tab)
        sheet_name = auto_send_settings.get('sheet_name', '').strip()
        if sheet_name:
            try:
                sheet = spreadsheet.worksheet(sheet_name)
                logger.info(f"Opened sheet tab: {sheet_name}")
            except Exception as e:
                return False, f"❌ Không tìm thấy sheet tab '{sheet_name}'!\n\nVui lòng kiểm tra lại tên sheet tab trong Settings."
        else:
            sheet = spreadsheet.sheet1
            logger.info(f"Opened default sheet tab")
        
        # Build row data based on column mapping
        columns = auto_send_settings.get('columns', {})
        rows = []
        
        for item in accepted_items:
            row = []
            
            if columns.get('assignee', True):
                row.append(item.get('assigned_name', ''))

            if columns.get('time', True):
                # Use server time from item if available
                server_time = item.get('server_time', '')
                if server_time:
                    row.append(server_time)
                else:
                    row.append(datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
            
            if columns.get('broker', True):
                row.append(item.get('broker', ''))
            
            if columns.get('symbol', True):
                row.append(item.get('symbol', ''))
            
            if columns.get('type', True):
                row.append(item.get('detection_type', '').upper())
            
            if columns.get('percentage', True):
                row.append(item.get('percentage', ''))
            
            rows.append(row)
        
        # Append all rows at once (more efficient)
        logger.info(f"Appending {len(rows)} rows to sheet...")
        sheet.append_rows(rows)
        
        logger.info(f"Successfully pushed {len(rows)} items to Google Sheets")
        return True, f"✅ Đã gửi {len(rows)} ảnh lên Google Sheets!\n\n📊 Sheet: {spreadsheet.title}\n🔗 Link: {sheet_url}"
        
    except Exception as e:
        error_msg = f"Lỗi khi gửi lên Google Sheets: {str(e)}"
        logger.error(error_msg, exc_info=True)
        return False, error_msg

# ===================== AUDIO ALERT FUNCTIONS =====================
def play_audio(audio_type, broker, symbol):
    """
    Phát âm thanh cảnh báo cho Gap/Spike/Delay
    
    Args:
        audio_type: 'gap', 'spike', hoặc 'delay'
        broker: Broker name
        symbol: Symbol name
    
    Chỉ phát 1 lần cho mỗi sản phẩm, có cooldown 30 giây trước khi phát lại
    """
    try:
        # Check if audio alerts are enabled
        if not audio_settings.get('enabled', True):
            return
        
        # Get sound file path based on type
        if audio_type == 'gap':
            sound_file = audio_settings.get('gap_sound', 'sounds/Gap.mp3')
        elif audio_type == 'spike':
            sound_file = audio_settings.get('spike_sound', 'sounds/Spike.mp3')
        elif audio_type == 'delay':
            sound_file = audio_settings.get('delay_sound', 'sounds/Delay.mp3')
        else:
            return
        
        # Check if file exists
        if not os.path.exists(sound_file):
            logger.warning(f"Audio file not found: {sound_file}")
            return
        
        # Create tracking key
        tracking_key = f"{broker}_{symbol}_{audio_type}"
        current_time = time.time()
        
        # Check if already played recently (cooldown)
        if tracking_key in audio_played_tracking:
            last_played = audio_played_tracking[tracking_key]
            if current_time - last_played < AUDIO_REPLAY_COOLDOWN:
                # Still in cooldown period
                return
        
        # Mark as played
        audio_played_tracking[tracking_key] = current_time

        # Submit to thread pool (max 5 concurrent audio playbacks)
        audio_executor.submit(_play_audio_thread, sound_file, audio_type, broker, symbol)

        logger.info(f"Playing audio alert: {audio_type} for {broker}_{symbol} ({sound_file})")
        
    except Exception as e:
        logger.error(f"Error playing audio: {e}")

def _play_audio_thread(sound_file, audio_type, broker, symbol):
    """
    Thread function để phát âm thanh (không chặn main thread)
    """
    try:
        if platform.system() == 'Windows':
            # Windows: Sử dụng winsound
            import winsound
            winsound.PlaySound(sound_file, winsound.SND_FILENAME)
        elif platform.system() == 'Darwin':
            # macOS: Sử dụng afplay
            subprocess.run(['afplay', sound_file], check=True)
        else:
            # Linux: Thử ffplay, paplay, hoặc aplay
            try:
                subprocess.run(['ffplay', '-nodisp', '-autoexit', sound_file], 
                             check=True, capture_output=True, timeout=5)
            except (FileNotFoundError, subprocess.TimeoutExpired):
                try:
                    subprocess.run(['paplay', sound_file], 
                                 check=True, capture_output=True, timeout=5)
                except (FileNotFoundError, subprocess.TimeoutExpired):
                    subprocess.run(['aplay', sound_file], 
                                 check=True, capture_output=True, timeout=5)
        
        logger.debug(f"Audio played successfully: {audio_type} for {broker}_{symbol}")
    except Exception as e:
        logger.error(f"Error in audio playback thread: {e}")

def load_audio_settings():
    """Load audio settings from JSON file"""
    global audio_settings
    try:
        if os.path.exists('audio_settings.json'):
            with open('audio_settings.json', 'r', encoding='utf-8') as f:
                audio_settings = json.load(f)
            logger.info(f"Loaded audio settings: enabled={audio_settings.get('enabled', True)}")
        else:
            logger.info("No audio_settings.json found, using defaults")
    except Exception as e:
        logger.error(f"Error loading audio settings: {e}")

def save_audio_settings():
    """Save audio settings to JSON file"""
    try:
        with open('audio_settings.json', 'w', encoding='utf-8') as f:
            json.dump(audio_settings, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved audio settings: enabled={audio_settings.get('enabled', True)}")
    except Exception as e:
        logger.error(f"Error saving audio settings: {e}")

def reset_audio_tracking():
    """Reset audio tracking (allow all sounds to be played again)"""
    global audio_played_tracking
    audio_played_tracking.clear()
    logger.info("Audio tracking reset - all sounds can be played again")

# ===================== LOAD/SAVE SETTINGS =====================
def load_gap_settings():
    """Load gap settings from JSON file"""
    global gap_settings
    try:
        if os.path.exists('gap_settings.json'):
            with open('gap_settings.json', 'r', encoding='utf-8') as f:
                gap_settings = json.load(f)
                logger.info(f"Loaded {len(gap_settings)} gap settings")
        else:
            # Default settings
            gap_settings = {
                "EURUSD": DEFAULT_GAP_THRESHOLD,
                "GBPUSD": DEFAULT_GAP_THRESHOLD,
                "USDJPY": DEFAULT_GAP_THRESHOLD,
                "BTCUSD": 700,
                "XAUUSD": 5
            }
            save_gap_settings()
    except Exception as e:
        logger.error(f"Error loading gap settings: {e}")
        gap_settings = {}

def save_gap_settings():
    """Save gap settings to JSON file"""
    try:
        with open('gap_settings.json', 'w', encoding='utf-8') as f:
            json.dump(gap_settings, f, ensure_ascii=False, indent=2)
        logger.info("Gap settings saved")
    except Exception as e:
        logger.error(f"Error saving gap settings: {e}")

def load_spike_settings():
    """Load spike settings from JSON file"""
    global spike_settings
    try:
        if os.path.exists('spike_settings.json'):
            with open('spike_settings.json', 'r', encoding='utf-8') as f:
                spike_settings = json.load(f)
                logger.info(f"Loaded {len(spike_settings)} spike settings")
        else:
            # Default settings
            spike_settings = {
                "EURUSD": DEFAULT_SPIKE_THRESHOLD,
                "GBPUSD": DEFAULT_SPIKE_THRESHOLD,
                "USDJPY": DEFAULT_SPIKE_THRESHOLD,
                "BTCUSD": DEFAULT_SPIKE_THRESHOLD,
                "XAUUSD": DEFAULT_SPIKE_THRESHOLD
            }
            save_spike_settings()
    except Exception as e:
        logger.error(f"Error loading spike settings: {e}")
        spike_settings = {}

def save_spike_settings():
    """Save spike settings to JSON file"""
    try:
        with open('spike_settings.json', 'w', encoding='utf-8') as f:
            json.dump(spike_settings, f, ensure_ascii=False, indent=2)
        logger.info("Spike settings saved")
    except Exception as e:
        logger.error(f"Error saving spike settings: {e}")

def load_manual_hidden_delays():
    """Load manual hidden delays from JSON file"""
    global manual_hidden_delays
    try:
        if os.path.exists('manual_hidden_delays.json'):
            with open('manual_hidden_delays.json', 'r', encoding='utf-8') as f:
                manual_hidden_delays = json.load(f)
            logger.info(f"Loaded {len(manual_hidden_delays)} manual hidden delays")
    except Exception as e:
        logger.error(f"Error loading manual hidden delays: {e}")
        manual_hidden_delays = {}

def save_manual_hidden_delays():
    """Save manual hidden delays to JSON file"""
    try:
        with open('manual_hidden_delays.json', 'w', encoding='utf-8') as f:
            json.dump(manual_hidden_delays, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved {len(manual_hidden_delays)} manual hidden delays")
    except Exception as e:
        logger.error(f"Error saving manual hidden delays: {e}")

def load_symbol_filter_settings():
    """Load symbol filter settings from JSON file"""
    global symbol_filter_settings
    try:
        if os.path.exists(SYMBOL_FILTER_FILE):
            with open(SYMBOL_FILTER_FILE, 'r', encoding='utf-8') as f:
                loaded = json.load(f) or {}

            enabled = bool(loaded.get('enabled', False))
            raw_selection = loaded.get('selection', {}) or {}
            selection = {}

            if isinstance(raw_selection, dict):
                for broker, symbols in raw_selection.items():
                    if symbols is None:
                        selection[broker] = []
                        continue

                    if isinstance(symbols, list):
                        cleaned = []
                        seen = set()
                        for sym in symbols:
                            if sym is None:
                                continue
                            sym_str = str(sym).strip()
                            if not sym_str:
                                continue
                            if sym_str not in seen:
                                cleaned.append(sym_str)
                                seen.add(sym_str)
                        selection[broker] = cleaned
                    else:
                        # Allow single string value
                        sym_str = str(symbols).strip()
                        selection[broker] = [sym_str] if sym_str else []

            symbol_filter_settings['enabled'] = enabled
            symbol_filter_settings['selection'] = selection

            logger.info(
                "Loaded symbol filter settings: enabled=%s, brokers=%d",
                symbol_filter_settings['enabled'],
                len(symbol_filter_settings['selection'])
            )
        else:
            symbol_filter_settings['enabled'] = False
            symbol_filter_settings['selection'] = {}
            logger.info("No symbol_filter_settings.json found, using defaults")
    except Exception as e:
        logger.error(f"Error loading symbol filter settings: {e}")
        symbol_filter_settings['enabled'] = False
        symbol_filter_settings['selection'] = {}

def save_symbol_filter_settings():
    """Save symbol filter settings to JSON file"""
    try:
        payload = {
            'enabled': bool(symbol_filter_settings.get('enabled', False)),
            'selection': symbol_filter_settings.get('selection', {}) or {}
        }

        with open(SYMBOL_FILTER_FILE, 'w', encoding='utf-8') as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)

        logger.info(
            "Saved symbol filter settings: enabled=%s, brokers=%d",
            payload['enabled'],
            len(payload['selection'])
        )
    except Exception as e:
        logger.error(f"Error saving symbol filter settings: {e}")

# ===================== SYMBOL FILTER HELPERS =====================
def is_symbol_selected_for_detection(broker, symbol):
    """Return True if the symbol should be processed for Gap/Spike detection"""
    try:
        if not symbol_filter_settings.get('enabled', False):
            return True

        selection = symbol_filter_settings.get('selection', {}) or {}
        if not selection:
            # No selection stored → treat as allow all (backward compatible)
            return True

        # Highest priority: broker specific list
        if broker in selection:
            broker_symbols = selection[broker]
            if broker_symbols is None:
                return False
            if not broker_symbols:
                return False
            return symbol in broker_symbols

        # Fallback: wildcard '*' if provided
        wildcard_list = selection.get('*')
        if wildcard_list is not None:
            if not wildcard_list:
                return False
            return symbol in wildcard_list

        # Broker not configured → allow all symbols for that broker by default
        return True
    except Exception as e:
        logger.error(f"Error checking symbol filter for {broker}_{symbol}: {e}")
        return True


def clear_symbol_detection_results(broker, symbol):
    """Remove existing Gap/Spike results and alerts for a symbol"""
    key = f"{broker}_{symbol}"

    if key in gap_spike_results:
        del gap_spike_results[key]

    if key in alert_board:
        del alert_board[key]


def cleanup_unselected_symbol_results():
    """Remove cached data for symbols that are no longer selected"""
    if not symbol_filter_settings.get('enabled', False):
        return

    selection = symbol_filter_settings.get('selection', {}) or {}
    if not selection:
        return

    with data_lock:
        symbols_to_remove = []

        for key, result in list(gap_spike_results.items()):
            broker = result.get('broker')
            symbol = result.get('symbol')
            if broker is None or symbol is None:
                continue

            if not is_symbol_selected_for_detection(broker, symbol):
                symbols_to_remove.append((broker, symbol))

        for broker, symbol in symbols_to_remove:
            clear_symbol_detection_results(broker, symbol)
            combined_key = f"{broker}_{symbol}"
            bid_tracking.pop(combined_key, None)
            candle_data.pop(combined_key, None)


def classify_symbol_group(symbol, group_path=None):
    """Return normalized group name for a symbol using market data + heuristics"""
    try:
        sym_original = (symbol or '').strip()
        if not sym_original:
            return 'Others'

        sym_upper = sym_original.upper()
        group_path = (group_path or '').strip()

        # Normalize Market Watch path if provided
        if group_path:
            normalized = group_path.replace('\\', '/').replace('> ', '/').replace(' >', '/').strip(' /')
            if normalized:
                parts = [p for p in normalized.split('/') if p]
                if parts:
                    top = parts[0].lower()
                    aliases = {
                        'forex': 'Forex',
                        'fx': 'Forex',
                        'currencies': 'Forex',
                        'currency': 'Forex',
                        'metals': 'Metals',
                        'precious metals': 'Metals',
                        'metal': 'Metals',
                        'indices': 'Indices',
                        'index': 'Indices',
                        'stocks': 'Stocks',
                        'shares': 'Stocks',
                        'equities': 'Stocks',
                        'equity': 'Stocks',
                        'us stocks': 'US Stocks',
                        'us shares': 'US Stocks',
                        'us equities': 'US Stocks',
                        'us equity': 'US Stocks',
                        'stocks us': 'US Stocks',
                        'shares us': 'US Stocks',
                        'crypto': 'Crypto',
                        'cryptocurrency': 'Crypto',
                        'energies': 'Energy',
                        'energy': 'Energy',
                        'commodities': 'Commodities',
                        'commodity': 'Commodities',
                        'futures': 'Futures'
                    }

                    if top in aliases:
                        return aliases[top]

                    # Try using second part if top is generic (e.g. "CFD")
                    if len(parts) > 1:
                        sub_top = parts[1].lower()
                        if sub_top in aliases:
                            return aliases[sub_top]
                        if sub_top.startswith('us '):
                            normalized_stock = sub_top[3:]
                            if normalized_stock in aliases:
                                return aliases[normalized_stock]

        forex_codes = {'USD', 'EUR', 'JPY', 'GBP', 'AUD', 'CAD', 'CHF', 'NZD', 'SGD', 'HKD', 'CNH', 'MXN', 'TRY', 'ZAR'}
        metals_prefixes = ('XAU', 'XAG', 'XPT', 'XPD', 'XCU', 'XNI', 'XAL')
        crypto_tokens = ('BTC', 'ETH', 'LTC', 'XRP', 'BCH', 'ADA', 'DOGE', 'SOL', 'DOT', 'BNB', 'SHIB', 'AVAX', 'LINK', 'UNI', 'XLM', 'TRX', 'NEO', 'EOS', 'MATIC')
        energy_keywords = ('OIL', 'BRENT', 'WTI', 'NGAS', 'GAS', 'ENERGY', 'UKOIL', 'USOIL')
        index_keywords = (
            'IDX', 'INDEX', 'US30', 'US500', 'NAS', 'SPX', 'DJI', 'DAX', 'GER', 'UK', 'FTSE',
            'CAC', 'IBEX', 'JP', 'NIK', 'HSI', 'HK', 'CHINA', 'CSI', 'ASX', 'KOSPI'
        )
        stock_suffixes = (
            '.N', '.O', '.A', '.K', '.M', '.P', '.S', '.L', '.DE', '.F', '.PA', '.HK', '.SG', '.AX'
        )

        # Normalize symbol for analysis (remove suffixes like .s, _mini, etc.)
        sym_clean = sym_upper
        for delim in ('.', '_', '-', ' ', '^'):
            if delim in sym_clean:
                sym_clean = sym_clean.split(delim)[0]
                break

        letters_only = ''.join(ch for ch in sym_clean if ch.isalpha())

        if len(letters_only) >= 6:
            for i in range(len(letters_only) - 5):
                base_pair = letters_only[i:i+6]
                base_left = base_pair[:3]
                base_right = base_pair[3:]
                if base_left in forex_codes and base_right in forex_codes:
                    return 'Forex'

        if any(sym_clean.startswith(prefix) for prefix in metals_prefixes):
            return 'Metals'

        if any(token in sym_clean for token in crypto_tokens):
            return 'Crypto'

        if any(keyword in sym_clean for keyword in energy_keywords):
            return 'Energy'

        if any(keyword in sym_clean for keyword in index_keywords) or sym_clean.endswith(
            ('500', '100', '200', '300', '400', '1000', '2000', '3000', '50', '40', '35', '225', '250', '150')):
            return 'Indices'

        for suffix in stock_suffixes:
            if sym_upper.endswith(suffix):
                if suffix in ('.N', '.O', '.A', '.K', '.M', '.P', '.S'):
                    return 'US Stocks'
                return 'Stocks'

        if '.' in sym_upper or '_' in sym_upper:
            return 'Stocks'

        if sym_clean.endswith(('US', 'UK', 'JP', 'DE', 'HK', 'FR')) and not sym_clean.endswith(tuple(forex_codes)):
            return 'Stocks'

        # Identify CFD suffixes e.g., EURUSDM, EURUSDmicro
        if letters_only and len(letters_only) > 6:
            base_pair = letters_only[:6]
            base_left = base_pair[:3]
            base_right = base_pair[3:]
            if base_left in forex_codes and base_right in forex_codes:
                return 'Forex'

        return 'Stocks'
    except Exception:
        return 'Stocks'


def load_delay_settings():
    """Load delay settings from JSON file"""
    global delay_settings
    try:
        if os.path.exists('delay_settings.json'):
            with open('delay_settings.json', 'r', encoding='utf-8') as f:
                loaded = json.load(f)
                delay_settings.update(loaded)
            logger.info(f"Loaded delay settings: threshold={delay_settings['threshold']}s")
    except Exception as e:
        logger.error(f"Error loading delay settings: {e}")

def save_delay_settings():
    """Save delay settings to JSON file"""
    try:
        with open('delay_settings.json', 'w', encoding='utf-8') as f:
            json.dump(delay_settings, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved delay settings: threshold={delay_settings['threshold']}s")
    except Exception as e:
        logger.error(f"Error saving delay settings: {e}")

def load_screenshot_settings():
    """Load screenshot settings from JSON file"""
    global screenshot_settings
    try:
        if os.path.exists('screenshot_settings.json'):
            with open('screenshot_settings.json', 'r', encoding='utf-8') as f:
                loaded = json.load(f)
                screenshot_settings.update(loaded)
            if 'assigned_name' not in screenshot_settings:
                screenshot_settings['assigned_name'] = ''
            logger.info(f"Loaded screenshot settings: enabled={screenshot_settings['enabled']}")
        else:
            logger.info("No screenshot_settings.json found, using defaults")
    except Exception as e:
        logger.error(f"Error loading screenshot settings: {e}")

def save_screenshot_settings():
    """Save screenshot settings to JSON file"""
    try:
        with open('screenshot_settings.json', 'w', encoding='utf-8') as f:
            json.dump(screenshot_settings, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved screenshot settings: enabled={screenshot_settings['enabled']}")
    except Exception as e:
        logger.error(f"Error saving screenshot settings: {e}")

def load_auto_send_settings():
    """Load auto-send Google Sheets settings from JSON file"""
    global auto_send_settings
    try:
        if os.path.exists('auto_send_settings.json'):
            with open('auto_send_settings.json', 'r', encoding='utf-8') as f:
                loaded = json.load(f)
                auto_send_settings.update(loaded)
            # Ensure new column defaults exist
            default_columns = {
                'assignee': True,
                'time': True,
                'broker': True,
                'symbol': True,
                'type': True,
                'percentage': True
            }

            columns = auto_send_settings.get('columns') or {}
            for key, default_value in default_columns.items():
                columns.setdefault(key, default_value)
            auto_send_settings['columns'] = columns

            logger.info(f"Loaded auto-send settings: enabled={auto_send_settings['enabled']}")
        else:
            logger.info("No auto_send_settings.json found, using defaults")
    except Exception as e:
        logger.error(f"Error loading auto-send settings: {e}")

def save_auto_send_settings():
    """Save auto-send Google Sheets settings to JSON file"""
    try:
        with open('auto_send_settings.json', 'w', encoding='utf-8') as f:
            json.dump(auto_send_settings, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved auto-send settings: enabled={auto_send_settings['enabled']}")
    except Exception as e:
        logger.error(f"Error saving auto-send settings: {e}")

def load_python_reset_settings():
    """Load auto Python reset settings"""
    global python_reset_settings
    try:
        if os.path.exists(PYTHON_RESET_SETTINGS_FILE):
            with open(PYTHON_RESET_SETTINGS_FILE, 'r', encoding='utf-8') as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    python_reset_settings.update(loaded)
        interval = int(python_reset_settings.get('interval_minutes', 30) or 30)
        if interval <= 0:
            interval = 30
        python_reset_settings['interval_minutes'] = interval
        python_reset_settings['enabled'] = bool(python_reset_settings.get('enabled', False))
        logger.info(
            "Loaded python reset settings: enabled=%s, interval=%d minutes",
            python_reset_settings['enabled'],
            python_reset_settings['interval_minutes']
        )
    except Exception as e:
        logger.error(f"Error loading python reset settings: {e}")
        python_reset_settings = {
            'enabled': False,
            'interval_minutes': 30
        }

def save_python_reset_settings():
    """Persist auto Python reset settings"""
    try:
        with open(PYTHON_RESET_SETTINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(python_reset_settings, f, ensure_ascii=False, indent=2)
        logger.info(
            "Saved python reset settings: enabled=%s, interval=%d minutes",
            python_reset_settings['enabled'],
            python_reset_settings['interval_minutes']
        )
    except Exception as e:
        logger.error(f"Error saving python reset settings: {e}")

def load_market_open_settings():
    """Load market open settings from JSON file"""
    global market_open_settings
    try:
        if os.path.exists('market_open_settings.json'):
            with open('market_open_settings.json', 'r', encoding='utf-8') as f:
                loaded = json.load(f)
                market_open_settings.update(loaded)
            logger.info(f"Loaded market open settings: only_check_open_market={market_open_settings['only_check_open_market']}")
        else:
            logger.info("No market_open_settings.json found, using defaults")
    except Exception as e:
        logger.error(f"Error loading market open settings: {e}")

def save_market_open_settings():
    """Save market open settings to JSON file"""
    try:
        with open('market_open_settings.json', 'w', encoding='utf-8') as f:
            json.dump(market_open_settings, f, ensure_ascii=False, indent=2)
        logger.info(f"Saved market open settings: only_check_open_market={market_open_settings['only_check_open_market']}")
    except Exception as e:
        logger.error(f"Error saving market open settings: {e}")

# ===================== SCREENSHOT MANAGEMENT =====================
def ensure_pictures_folder():
    """Ensure pictures folder exists"""
    folder = screenshot_settings['folder']
    if not os.path.exists(folder):
        os.makedirs(folder)
        logger.info(f"Created pictures folder: {folder}")

def capture_chart_screenshot(broker, symbol, detection_type, gap_info=None, spike_info=None, server_timestamp=None):
    """
    Capture screenshot of chart when gap/spike detected
    
    Args:
        broker: Broker name
        symbol: Symbol name
        detection_type: 'gap', 'spike', or 'both'
        gap_info: Gap detection info dict
        spike_info: Spike detection info dict
        server_timestamp: Timestamp from server (EA) in seconds since epoch
    """
    try:
        # Check if screenshot is enabled
        if not screenshot_settings['enabled']:
            return
        
        # Check if we should save this type
        if detection_type == 'gap' and not screenshot_settings['save_gap']:
            return
        if detection_type == 'spike' and not screenshot_settings['save_spike']:
            return
        
        # Ensure folder exists
        ensure_pictures_folder()
        
        # Get candle data
        key = f"{broker}_{symbol}"
        with data_lock:
            candles = candle_data.get(key, [])
            if not candles:
                logger.warning(f"No candle data for screenshot: {key}")
                return
            
            # Get current bid/ask
            bid = 0
            ask = 0
            if broker in market_data and symbol in market_data[broker]:
                bid = market_data[broker][symbol].get('bid', 0)
                ask = market_data[broker][symbol].get('ask', 0)
        
        # Create figure with Agg backend (non-interactive, thread-safe)
        fig = Figure(figsize=(12, 6), facecolor='#1e1e1e')
        canvas = FigureCanvasAgg(fig)
        ax = fig.add_subplot(111)
        ax.set_facecolor('#2d2d30')
        
        # Prepare candlestick data
        times = [mdates.date2num(server_timestamp_to_datetime(c[0])) for c in candles]
        opens = [c[1] for c in candles]
        highs = [c[2] for c in candles]
        lows = [c[3] for c in candles]
        closes = [c[4] for c in candles]
        
        # Draw candlesticks
        for i in range(len(candles)):
            color = '#26a69a' if closes[i] >= opens[i] else '#ef5350'
            
            # Candle body
            height = abs(closes[i] - opens[i])
            if height == 0:
                height = 0.00001
            bottom = min(opens[i], closes[i])
            rect = Rectangle((times[i] - 0.0003, bottom), 0.0006, height,
                           facecolor=color, edgecolor=color, alpha=0.8)
            ax.add_patch(rect)
            
            # Wick
            ax.plot([times[i], times[i]], [lows[i], highs[i]], 
                   color=color, linewidth=1, alpha=0.8)
        
        # Draw bid/ask lines
        if bid > 0 and ask > 0:
            ax.axhline(y=bid, color='#ef5350', linestyle='--', linewidth=1.5, 
                      alpha=0.8, label=f'Bid: {bid:.5f}')
            ax.axhline(y=ask, color='#26a69a', linestyle='--', linewidth=1.5, 
                      alpha=0.8, label=f'Ask: {ask:.5f}')
        
        # Title with detection info
        title_parts = [f'{broker} - {symbol}']
        if gap_info and gap_info.get('detected'):
            gap_pct = gap_info.get('percentage', 0)
            gap_dir = gap_info.get('direction', '').upper()
            title_parts.append(f'GAP {gap_dir}: {gap_pct:.3f}%')
        if spike_info and spike_info.get('detected'):
            spike_pct = spike_info.get('strength', 0)
            spike_type = spike_info.get('spike_type', '')
            title_parts.append(f'SPIKE {spike_type}: {spike_pct:.3f}%')
        
        ax.set_title(' | '.join(title_parts), color='white', fontsize=14, fontweight='bold')
        ax.set_xlabel('Time', color='white')
        ax.set_ylabel('Price', color='white')
        ax.tick_params(colors='white')
        ax.grid(True, alpha=0.2, color='gray')
        ax.legend(loc='upper left', facecolor='#2d2d30', edgecolor='#404040', 
                 labelcolor='white')
        
        # Format x-axis
        ax.xaxis.set_major_formatter(mdates.DateFormatter('%H:%M'))
        ax.xaxis.set_major_locator(mdates.MinuteLocator(interval=10))
        for tick in ax.get_xticklabels():
            tick.set_rotation(45)
        
        # Auto scale
        if highs and lows:
            y_min = min(lows) * 0.9999
            y_max = max(highs) * 1.0001
            ax.set_ylim(y_min, y_max)
        
        # Generate filename with server timestamp (from EA/sàn)
        if server_timestamp:
            # Use server time from EA (thời gian thực tế của sàn - không convert timezone)
            dt = server_timestamp_to_datetime(server_timestamp)
            timestamp_str = dt.strftime('%Y%m%d_%H%M%S')
            server_time_str = dt.strftime('%Y-%m-%d %H:%M:%S')
            server_timestamp_value = int(server_timestamp)
        else:
            # Fallback to local time if no server timestamp
            dt = datetime.now()
            timestamp_str = dt.strftime('%Y%m%d_%H%M%S')
            server_time_str = dt.strftime('%Y-%m-%d %H:%M:%S')
            server_timestamp_value = None
        
        filename = f"{broker}_{symbol}_{detection_type}_{timestamp_str}.png"
        filepath = os.path.join(screenshot_settings['folder'], filename)
        
        # Save figure using Agg backend
        fig.tight_layout()
        canvas.print_png(filepath)
        
        logger.info(f"Captured screenshot: {filepath}")

        # Save metadata for later export (Accept → Google Sheets)
        try:
            gap_meta = {
                'detected': bool(gap_info.get('detected')) if gap_info else False,
                'direction': gap_info.get('direction') if gap_info else None,
                'percentage': float(gap_info.get('percentage')) if gap_info and gap_info.get('percentage') is not None else None,
                'message': gap_info.get('message') if gap_info else '',
                'threshold': gap_info.get('threshold') if gap_info else None
            }

            spike_meta = {
                'detected': bool(spike_info.get('detected')) if spike_info else False,
                'spike_type': spike_info.get('spike_type') if spike_info else None,
                'strength': float(spike_info.get('strength')) if spike_info and spike_info.get('strength') is not None else None,
                'message': spike_info.get('message') if spike_info else '',
                'threshold': spike_info.get('threshold') if spike_info else None
            }

            metadata = {
                'broker': broker,
                'symbol': symbol,
                'detection_type': detection_type,
                'server_timestamp': server_timestamp_value,
                'server_time': server_time_str,
                'gap': gap_meta,
                'spike': spike_meta,
                'created_at': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }

            metadata_path = os.path.splitext(filepath)[0] + '.json'
            with open(metadata_path, 'w', encoding='utf-8') as meta_file:
                json.dump(metadata, meta_file, ensure_ascii=False, indent=2)

            logger.debug(f"Saved screenshot metadata: {metadata_path}")
        except Exception as meta_err:
            logger.error(f"Error saving screenshot metadata for {filename}: {meta_err}")
        
    except Exception as e:
        logger.error(f"Error capturing screenshot: {e}", exc_info=True)

# ===================== ALERT BOARD MANAGEMENT =====================
def update_alert_board(key, result):
    """Update Alert Board (Bảng Kèo) với logic xóa sau 15s"""
    gap_detected = result.get('gap', {}).get('detected', False)
    spike_detected = result.get('spike', {}).get('detected', False)
    is_alert = gap_detected or spike_detected
    
    current_time = time.time()
    
    if is_alert:
        # Có alert → Thêm hoặc cập nhật vào bảng kèo
        if key in alert_board:
            # Đã có trong bảng → Cập nhật data và reset grace period
            alert_board[key]['data'] = result
            alert_board[key]['last_detected_time'] = current_time
            alert_board[key]['grace_period_start'] = None
            # Keep screenshot_captured flag (don't reset it)
        else:
            # Chưa có → Thêm mới
            alert_board[key] = {
                'data': result,
                'last_detected_time': current_time,
                'grace_period_start': None,
                'screenshot_captured': False  # New flag to track screenshot
            }
        
        # Capture screenshot - CHỈ nếu chưa chụp
        if not alert_board[key]['screenshot_captured']:
            try:
                # Check if screenshot is enabled
                if not screenshot_settings.get('enabled', True):
                    return
                
                broker = result.get('broker', '')
                symbol = result.get('symbol', '')
                gap_info = result.get('gap', {})
                spike_info = result.get('spike', {})
                server_timestamp = result.get('timestamp', None)  # Lấy timestamp từ sàn
                
                # Determine detection type
                if gap_detected and spike_detected:
                    detection_type = 'both'
                elif gap_detected:
                    detection_type = 'gap'
                    if not screenshot_settings.get('save_gap', True):
                        return
                else:
                    detection_type = 'spike'
                    if not screenshot_settings.get('save_spike', True):
                        return
                
                # Submit to screenshot thread pool (max 3 concurrent captures)
                screenshot_executor.submit(
                    capture_chart_screenshot,
                    broker, symbol, detection_type, gap_info, spike_info, server_timestamp
                )

                # Mark as captured
                alert_board[key]['screenshot_captured'] = True
                logger.info(f"Screenshot queued for {key} ({detection_type})")
                
            except Exception as e:
                logger.error(f"Error starting screenshot thread: {e}")
    else:
        # Không còn alert
        if key in alert_board:
            # Bắt đầu grace period nếu chưa có
            if alert_board[key]['grace_period_start'] is None:
                alert_board[key]['grace_period_start'] = current_time
            else:
                # Kiểm tra đã hết grace period chưa (15s)
                elapsed = current_time - alert_board[key]['grace_period_start']
                if elapsed >= 15:
                    # Xóa khỏi bảng kèo
                    del alert_board[key]

def cleanup_stale_data():
    """
    Xóa dữ liệu cũ của brokers/symbols không còn active
    Cleanup sau 30 giây không nhận data
    """
    current_time = time.time()
    stale_threshold = 30  # 30 giây
    
    # Cleanup market_data - Xóa brokers không còn active
    brokers_to_remove = []
    for broker, symbols in list(market_data.items()):
        # Tìm timestamp mới nhất của broker
        latest_timestamp = 0
        for symbol_data in symbols.values():
            ts = symbol_data.get('timestamp', 0)
            if ts > latest_timestamp:
                latest_timestamp = ts
        
        # Nếu broker không gửi data >30s → Xóa
        if current_time - latest_timestamp > stale_threshold:
            brokers_to_remove.append(broker)
            logger.info(f"Cleanup: Removing stale broker '{broker}' (no data for {int(current_time - latest_timestamp)}s)")
    
    for broker in brokers_to_remove:
        del market_data[broker]
    
    # Cleanup gap_spike_results - Xóa keys không còn trong market_data
    keys_to_remove = []
    for key in list(gap_spike_results.keys()):
        broker, symbol = key.split('_', 1)
        if broker not in market_data or symbol not in market_data.get(broker, {}):
            keys_to_remove.append(key)
    
    for key in keys_to_remove:
        del gap_spike_results[key]
        logger.debug(f"Cleanup: Removed gap_spike_result for '{key}'")
    
    # Cleanup alert_board - Xóa keys không còn trong market_data
    keys_to_remove = []
    for key in list(alert_board.keys()):
        broker, symbol = key.split('_', 1)
        if broker not in market_data or symbol not in market_data.get(broker, {}):
            keys_to_remove.append(key)
    
    for key in keys_to_remove:
        del alert_board[key]
        logger.debug(f"Cleanup: Removed alert_board for '{key}'")
    
    # Cleanup bid_tracking - Xóa keys không còn trong market_data
    keys_to_remove = []
    for key in list(bid_tracking.keys()):
        broker, symbol = key.split('_', 1)
        if broker not in market_data or symbol not in market_data.get(broker, {}):
            keys_to_remove.append(key)
    
    for key in keys_to_remove:
        del bid_tracking[key]
        logger.debug(f"Cleanup: Removed bid_tracking for '{key}'")

# ===================== GAP & SPIKE CALCULATION =====================
def get_threshold(broker, symbol, threshold_type):
    """
    Get threshold with proper priority logic:
    Priority: Broker_Symbol > Broker_* > Symbol > * > Default
    """
    settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
    key = f"{broker}_{symbol}"
    
    # Priority 1: Broker_Symbol (VD: Exness_EURUSD)
    if key in settings_dict:
        return settings_dict[key]
    
    # Priority 2: Broker_* (VD: Exness_*)
    broker_wildcard = f"{broker}_*"
    if broker_wildcard in settings_dict:
        return settings_dict[broker_wildcard]
    
    # Priority 3: Symbol (VD: EURUSD)
    if symbol in settings_dict:
        return settings_dict[symbol]
    
    # Priority 4: Wildcard (*)
    if '*' in settings_dict:
        return settings_dict['*']
    
    # Priority 5: Default
    return DEFAULT_GAP_THRESHOLD if threshold_type == 'gap' else DEFAULT_SPIKE_THRESHOLD

def get_threshold_for_display(broker, symbol, threshold_type):
    """Return numeric threshold only (float), not tuple!!"""

    settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
    key1 = f"{broker}_{symbol}"     # Broker_Symbol
    key2 = f"{broker}_*"            # Broker_*
    key3 = symbol                   # Symbol
    key4 = '*'                      # Global wildcard

    # Priority 1: broker_symbol
    if key1 in settings_dict:
        return float(settings_dict[key1])

    # Priority 2: broker_*
    if key2 in settings_dict:
        return float(settings_dict[key2])

    # Priority 3: symbol
    if key3 in settings_dict:
        return float(settings_dict[key3])

    # Priority 4: *
    if key4 in settings_dict:
        return float(settings_dict[key4])

    # Priority 5: Default
    return DEFAULT_GAP_THRESHOLD if threshold_type == 'gap' else DEFAULT_SPIKE_THRESHOLD


def get_threshold_source(broker, symbol, threshold_type):
    """Get source of threshold (for display)"""
    settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
    key = f"{broker}_{symbol}"
    
    if key in settings_dict:
        return f"Custom ({broker}_{symbol})"
    
    broker_wildcard = f"{broker}_*"
    if broker_wildcard in settings_dict:
        return f"Broker wildcard ({broker}_*)"
    
    if symbol in settings_dict:
        return f"Symbol ({symbol})"
    
    if '*' in settings_dict:
        return "Global wildcard (*)"
    
    return "default"

def calculate_gap(symbol, broker, data):
    """
    Tính toán GAP theo công thức:
    Gap% = (Open_hiện_tại - Close_trước) / Close_trước × 100
    
    Điều kiện gap down hợp lệ:
    - Gap down % >= ngưỡng
    - Giá ASK hiện tại < Close nến trước
    """
    try:
        prev_ohlc = data.get('prev_ohlc', {})
        current_ohlc = data.get('current_ohlc', {})
        
        prev_close = float(prev_ohlc.get('close', 0))
        current_open = float(current_ohlc.get('open', 0))
        
        # Lấy bid/ask hiện tại
        current_ask = float(data.get('ask', 0))
        current_bid = float(data.get('bid', 0))
        spread_percent = 0.0
        if current_bid > 0:
            try:
                spread_percent = abs(current_ask - current_bid) / current_bid * 100
            except ZeroDivisionError:
                spread_percent = 0.0
        
        if prev_close == 0:
            return {
                'detected': False,
                'direction': 'none',
                'percentage': 0.0,
                'previous_close': 0,
                'current_open': 0,
                'current_ask': 0,
                'message': 'Chưa đủ dữ liệu'
            }
        
        # ✅ KIỂM TRA NGÀY: Nến trước đó và nến gap phải cùng ngày
        prev_timestamp = prev_ohlc.get('timestamp', 0)
        current_timestamp = current_ohlc.get('timestamp', 0)
        
        if prev_timestamp > 0 and current_timestamp > 0:
            prev_dt = server_timestamp_to_datetime(prev_timestamp)
            current_dt = server_timestamp_to_datetime(current_timestamp)
            
            # Kiểm tra xem nến trước và nến gap có cùng ngày không
            prev_date = prev_dt.date()  # YYYY-MM-DD
            current_date = current_dt.date()  # YYYY-MM-DD
            
            if prev_date != current_date:
                # Nến trước đó không cùng ngày → Không phải gap hợp lệ
                return {
                    'detected': False,
                    'direction': 'none',
                    'percentage': 0.0,
                    'previous_close': prev_close,
                    'current_open': current_open,
                    'current_ask': current_ask,
                    'message': f'❌ Nến trước {prev_date} không cùng ngày với nến gap {current_date} - Bỏ qua'
                }
            
            # ✅ KIỂM TRA NGÀY: Nến gap phải cùng ngày với hôm nay
            today_date = get_today_date()  # Use cached date
            if current_date != today_date:
                # Nến gap không phải hôm nay → Không phải gap mới
                return {
                    'detected': False,
                    'direction': 'none',
                    'percentage': 0.0,
                    'previous_close': prev_close,
                    'current_open': current_open,
                    'current_ask': current_ask,
                    'message': f'❌ Nến gap {current_date} không phải hôm nay {today_date} - Bỏ qua'
                }
            return {
                'detected': False,
                'direction': 'none',
                'percentage': 0.0,
                'previous_close': 0,
                'current_open': 0,
                'current_ask': 0,
                'message': 'Chưa đủ dữ liệu'
            }
        
        # Lấy ngưỡng gap với priority logic đúng
        gap_threshold = get_threshold(broker, symbol, 'gap')
        
        # Tính Gap%
        gap_percentage = ((current_open - prev_close) / prev_close * 100)
        gap_percentage_abs = abs(gap_percentage)
        
        # Xác định hướng
        direction = 'up' if gap_percentage > 0 else ('down' if gap_percentage < 0 else 'none')
        
        # Kiểm tra vượt ngưỡng với điều kiện bổ sung
        gap_up_threshold_met = gap_percentage_abs >= gap_threshold if direction == 'up' else False
        gap_up_spread_met = gap_percentage_abs > spread_percent if direction == 'up' else False

        if direction == 'up':
            detected = gap_up_threshold_met and gap_up_spread_met
        elif direction == 'down':
            # Gap Down: Kiểm tra % VÀ Ask < Close_prev
            detected = (gap_percentage_abs >= gap_threshold) and (current_ask < prev_close)
        else:
            # No gap
            detected = False
        
        # Tạo message chi tiết
        if detected:
            if direction == 'down':
                message = (
                    f"GAP DOWN: {gap_percentage_abs:.3f}% (Open: {current_open:.5f}, Ask: {current_ask:.5f} < Close_prev: {prev_close:.5f}, "
                    f"ngưỡng: {gap_threshold}%)"
                )
            else:
                message = (
                    f"GAP UP: {gap_percentage_abs:.3f}% (Open: {current_open:.5f}, Close_prev: {prev_close:.5f}, "
                    f"ngưỡng: {gap_threshold}% / spread: {spread_percent:.3f}%)"
                )
        else:
            if direction == 'up' and gap_up_threshold_met and not gap_up_spread_met:
                message = (
                    f"Gap Up: {gap_percentage_abs:.3f}% <= Spread {spread_percent:.3f}% - Không hợp lệ"
                )
            elif direction == 'down' and gap_percentage_abs >= gap_threshold and current_ask >= prev_close:
                message = f"Gap Down: {gap_percentage_abs:.3f}% (Ask {current_ask:.5f} >= Close_prev {prev_close:.5f} - Không hợp lệ)"
            else:
                message = f"Gap: {gap_percentage_abs:.3f}%"
        
        result = {
            'detected': detected,
            'direction': direction,
            'percentage': gap_percentage_abs,
            'previous_close': prev_close,
            'current_open': current_open,
            'current_ask': current_ask,
            'threshold': gap_threshold,
            'message': message
        }
        
        return result
        
    except Exception as e:
        logger.error(f"Error calculating gap for {symbol}: {e}")
        return {
            'detected': False,
            'direction': 'none',
            'percentage': 0.0,
            'message': f'Lỗi: {str(e)}'
        }

def calculate_spike(symbol, broker, data):
    """
    Tính toán SPIKE 2 chiều (bidirectional):
    
    Spike Up = (High_hiện_tại - Close_trước) / Close_trước × 100
    Spike Down = (Close_trước - Low_hiện_tại) / Close_trước × 100
    
    Điều kiện spike down hợp lệ:
    - Spike down % >= ngưỡng
    - Giá ASK hiện tại < Close nến trước
    
    Công thức này phát hiện cả:
    - Biến động tăng mạnh (High cao hơn Close trước nhiều)
    - Biến động giảm mạnh (Low thấp hơn Close trước nhiều) + Ask < Close_prev
    """
    try:
        prev_ohlc = data.get('prev_ohlc', {})
        current_ohlc = data.get('current_ohlc', {})
        
        prev_close = float(prev_ohlc.get('close', 0))
        current_high = float(current_ohlc.get('high', 0))
        current_low = float(current_ohlc.get('low', 0))
        
        # Lấy giá bid/ask hiện tại (cho điều kiện spike down và spread)
        current_ask = float(data.get('ask', 0))
        current_bid = float(data.get('bid', 0))
        spread_percent = 0.0
        if current_bid > 0:
            try:
                spread_percent = abs(current_ask - current_bid) / current_bid * 100
            except ZeroDivisionError:
                spread_percent = 0.0
        
        # Kiểm tra dữ liệu hợp lệ
        if prev_close == 0:
            return {
                'detected': False,
                'strength': 0.0,
                'message': 'Không có dữ liệu prev_close'
            }
        
        if current_high == 0 or current_low == 0:
            return {
                'detected': False,
                'strength': 0.0,
                'message': 'Không có dữ liệu current OHLC'
            }
        
        # Lấy ngưỡng spike với priority logic đúng
        spike_threshold = get_threshold(broker, symbol, 'spike')
        
        # Tính Spike Up = (High - Close_prev) / Close_prev * 100
        spike_up = ((current_high - prev_close) / prev_close * 100)
        
        # Tính Spike Down = (Close_prev - Low) / Close_prev * 100
        spike_down = ((prev_close - current_low) / prev_close * 100)
        
        # Lấy giá trị tuyệt đối
        spike_up_abs = abs(spike_up)
        spike_down_abs = abs(spike_down)
        
        # Kiểm tra spike up
        spike_up_threshold_met = spike_up_abs >= spike_threshold
        spike_up_spread_met = spike_up_abs > spread_percent
        spike_up_detected = spike_up_threshold_met and spike_up_spread_met
        
        # Kiểm tra spike down với điều kiện BỔ SUNG: Ask < Close_prev
        spike_down_detected = (spike_down_abs >= spike_threshold) and (current_ask < prev_close)
        
        detected = spike_up_detected or spike_down_detected
        
        # Xác định spike mạnh nhất và hướng
        # Ưu tiên spike nào DETECTED (thỏa điều kiện)
        if spike_up_detected and spike_down_detected:
            # Cả 2 đều detected → Chọn spike mạnh hơn
            if spike_up_abs > spike_down_abs:
                spike_type = "UP"
                spike_value = spike_up
                spike_abs = spike_up_abs
                price_detail = f"High: {current_high:.5f}"
            else:
                spike_type = "DOWN"
                spike_value = spike_down
                spike_abs = spike_down_abs
                price_detail = f"Low: {current_low:.5f}, Ask: {current_ask:.5f} < Close_prev: {prev_close:.5f}"
        elif spike_up_detected:
            spike_type = "UP"
            spike_value = spike_up
            spike_abs = spike_up_abs
            price_detail = f"High: {current_high:.5f}, Spread: {spread_percent:.3f}%"
        elif spike_down_detected:
            spike_type = "DOWN"
            spike_value = spike_down
            spike_abs = spike_down_abs
            price_detail = f"Low: {current_low:.5f}, Ask: {current_ask:.5f} < Close_prev: {prev_close:.5f}"
        else:
            # Không detected → Chọn spike lớn hơn để hiển thị
            if spike_up_abs > spike_down_abs:
                spike_type = "UP"
                spike_value = spike_up
                spike_abs = spike_up_abs
                if spike_up_threshold_met and not spike_up_spread_met:
                    price_detail = f"High: {current_high:.5f}, Spread {spread_percent:.3f}% >= Spike"
                else:
                    price_detail = f"High: {current_high:.5f}"
            else:
                spike_type = "DOWN"
                spike_value = spike_down
                spike_abs = spike_down_abs
                # Hiển thị lý do không detected
                if current_ask >= prev_close:
                    price_detail = f"Low: {current_low:.5f}, Ask: {current_ask:.5f} >= Close_prev: {prev_close:.5f} (Không hợp lệ)"
                else:
                    price_detail = f"Low: {current_low:.5f}"
        
        if detected:
            message = f"SPIKE {spike_type}: {spike_abs:.3f}% ({price_detail}, ngưỡng: {spike_threshold}%)"
        else:
            if spike_up_threshold_met and not spike_up_spread_met:
                message = f"Spike Up: {spike_up_abs:.3f}% <= Spread {spread_percent:.3f}% - Không hợp lệ"
            elif spike_down_abs >= spike_threshold and current_ask >= prev_close:
                message = (
                    f"Spike Down: {spike_down_abs:.3f}% (Ask {current_ask:.5f} >= Close_prev {prev_close:.5f} - Không hợp lệ)"
                )
            else:
                message = f"Spike: Up {spike_up_abs:.3f}% / Down {spike_down_abs:.3f}%"

        result = {
            'detected': detected,
            'strength': spike_abs,  # Giá trị tuyệt đối lớn nhất
            'spike_up': spike_up,
            'spike_down': spike_down,
            'spike_up_abs': spike_up_abs,
            'spike_down_abs': spike_down_abs,
            'spike_type': spike_type,
            'previous_close': prev_close,
            'current_high': current_high,
            'current_low': current_low,
            'current_ask': current_ask,
            'threshold': spike_threshold,
            'message': message
        }
        
        return result
        
    except Exception as e:
        logger.error(f"Error calculating spike for {symbol}: {e}")
        return {
            'detected': False,
            'strength': 0.0,
            'message': f'Lỗi: {str(e)}'
        }

# ===================== FLASK ENDPOINTS =====================
@app.route('/api/receive_data', methods=['POST'])
def receive_data():
    """Nhận dữ liệu từ EA MT4/MT5"""
    try:
        data = request.get_json(force=True)
        broker = data.get('broker', 'Unknown')
        timestamp = data.get('timestamp', int(time.time()))
        symbols_data = data.get('data', [])
        
        with data_lock:
            # Optimize: Use setdefault() instead of if-check (faster dict access)
            broker_data = market_data.setdefault(broker, {})

            for symbol_data in symbols_data:
                symbol = symbol_data.get('symbol', '')
                if not symbol:
                    continue
                
                # Lưu dữ liệu market
                current_bid = symbol_data.get('bid', 0)
                broker_data[symbol] = {
                    'timestamp': timestamp,
                    'bid': current_bid,
                    'ask': symbol_data.get('ask', 0),
                    'digits': symbol_data.get('digits', 5),
                    'points': symbol_data.get('points', 0.00001),
                    'isOpen': symbol_data.get('isOpen', True),
                    'prev_ohlc': symbol_data.get('prev_ohlc', {}),
                    'current_ohlc': symbol_data.get('current_ohlc', {}),
                    'trade_sessions': symbol_data.get('trade_sessions', {}),
                    'group': symbol_data.get('group', '')
                }
                
                key = f"{broker}_{symbol}"

                # Bỏ qua symbol nếu không nằm trong danh sách được chọn
                if not is_symbol_selected_for_detection(broker, symbol):
                    clear_symbol_detection_results(broker, symbol)
                    bid_tracking.pop(key, None)
                    candle_data.pop(key, None)
                    continue

                # Track bid changes for delay detection
                current_time = time.time()

                # Optimize: Check if symbol exists first
                if key in bid_tracking:
                    # Existing symbol - check if bid changed
                    if bid_tracking[key]['last_bid'] != current_bid:
                        bid_tracking[key]['last_bid'] = current_bid
                        bid_tracking[key]['last_change_time'] = current_time
                else:
                    # First time seeing this symbol - initialize
                    bid_tracking[key] = {
                        'last_bid': current_bid,
                        'last_change_time': current_time,
                        'first_seen_time': current_time
                    }
                
                # Store candle data for charting (M1 candles)
                current_ohlc = symbol_data.get('current_ohlc', {})
                
                # IMPORTANT: Check for historical_candles FIRST (populate on chart open)
                historical_candles = symbol_data.get('historical_candles', [])
                if historical_candles and len(historical_candles) > 0 and key not in candle_data:
                    # First time receiving this symbol - restore from historical data
                    try:
                        candle_data[key] = []
                        for candle in historical_candles:
                            if isinstance(candle, (list, tuple)) and len(candle) >= 5:
                                ts = int(candle[0])
                                o = float(candle[1])
                                h = float(candle[2])
                                l = float(candle[3])
                                c = float(candle[4])
                                candle_data[key].append((ts, o, h, l, c))
                        
                        if len(candle_data[key]) > 0:
                            logger.info(f"Restored {len(candle_data[key])} historical candles for {key}")
                    except Exception as e:
                        logger.error(f"Error processing historical_candles for {key}: {e}")
                        candle_data[key] = []
                
                # Then accumulate current candle data (as before)
                if current_ohlc.get('open') and current_ohlc.get('close'):
                    # Round timestamp về đầu phút (M1 = 60s)
                    # VD: 14:30:45 → 14:30:00
                    candle_time = (timestamp // 60) * 60
                    
                    o = float(current_ohlc.get('open', 0))
                    h = float(current_ohlc.get('high', 0))
                    l = float(current_ohlc.get('low', 0))
                    c = float(current_ohlc.get('close', 0))
                    
                    # ✅ FIX: LUÔN đảm bảo list được khởi tạo (không chỉ lần đầu)
                    # Nếu key chưa tồn tại HOẶC list bị xóa, khởi tạo lại
                    if key not in candle_data or not isinstance(candle_data[key], list):
                        candle_data[key] = []
                    
                    # Kiểm tra nến cuối cùng
                    if candle_data[key]:
                        last_candle = candle_data[key][-1]
                        last_time = last_candle[0]

                        if last_time == candle_time:
                            # Cùng phút → Update nến hiện tại
                            # Update High/Low nếu cần
                            last_o, last_h, last_l, last_c = last_candle[1], last_candle[2], last_candle[3], last_candle[4]
                            new_h = max(last_h, h)
                            new_l = min(last_l, l)

                            # Update nến
                            candle_data[key][-1] = (candle_time, last_o, new_h, new_l, c)
                        else:
                            # Phút mới → CHỈ thêm nến mới nếu có thay đổi giá (giống MT4/MT5)
                            # Lấy Close của nến cuối cùng
                            last_c = last_candle[4]

                            # Kiểm tra xem có thay đổi giá không
                            # Nếu OHLC đều bằng Close của nến cuối → Delay (không có tick mới)
                            has_price_change = not (o == last_c and h == last_c and l == last_c and c == last_c)

                            if has_price_change:
                                # Có thay đổi giá → Tạo nến mới
                                candle_data[key].append((candle_time, o, h, l, c))
                            # Nếu không có thay đổi → KHÔNG tạo nến mới (giống MT4/MT5 khi delay)
                    else:
                        # Nến đầu tiên (list trống)
                        candle_data[key].append((candle_time, o, h, l, c))
                    
                    # Giữ tối đa 200 nến (để chart load nhanh)
                    if len(candle_data[key]) > 200:
                        candle_data[key] = candle_data[key][-200:]

                # Tính toán Gap và Spike
                # Kiểm tra nếu setting "only_check_open_market" được bật
                should_calculate = True
                skip_reason = ""

                # Optimize: Reuse broker_data[symbol] instead of market_data[broker][symbol]
                symbol_market_data = broker_data[symbol]

                if market_open_settings.get('only_check_open_market', False):
                    # Chỉ tính nếu market đang mở
                    is_market_open = symbol_market_data.get('isOpen', True)
                    if not is_market_open:
                        should_calculate = False
                        skip_reason = "Market đóng cửa"

                # Kiểm tra skip period sau khi market mở
                if should_calculate and is_within_skip_period_after_open(symbol, broker, timestamp):
                    should_calculate = False
                    skip_minutes = market_open_settings.get('skip_minutes_after_open', 0)
                    skip_reason = f"Bỏ {skip_minutes} phút đầu sau khi mở cửa"

                if should_calculate:
                    gap_info = calculate_gap(symbol, broker, symbol_market_data)
                    spike_info = calculate_spike(symbol, broker, symbol_market_data)
                else:
                    # Không tính gap/spike (do market đóng hoặc skip period)
                    gap_info = {
                        'detected': False,
                        'strength': 0.0,
                        'message': f'{skip_reason} - Không xét gap/spike'
                    }
                    spike_info = {
                        'detected': False,
                        'strength': 0.0,
                        'message': f'{skip_reason} - Không xét gap/spike'
                    }
                
                # Lưu kết quả
                key = f"{broker}_{symbol}"
                gap_spike_results[key] = {
                    'symbol': symbol,
                    'broker': broker,
                    'timestamp': timestamp,
                    'price': (symbol_market_data['bid'] + symbol_market_data['ask']) / 2,
                    'gap': gap_info,
                    'spike': spike_info
                }

                # Update Alert Board (Bảng Kèo)
                update_alert_board(key, gap_spike_results[key])
                
                # 🔊 PHÁT ÂM THANH CẢnh báo khi phát hiện Gap/Spike/Delay
                # Gap alert
                if gap_info.get('detected'):
                    play_audio('gap', broker, symbol)
                
                # Spike alert
                if spike_info.get('detected'):
                    play_audio('spike', broker, symbol)
                
                # Delay alert
                if key in bid_tracking:
                    delay_duration = current_time - bid_tracking[key]['last_change_time']
                    delay_threshold = delay_settings.get('threshold', 180)
                    if delay_duration >= delay_threshold:
                        play_audio('delay', broker, symbol)
        
        # Cleanup old/stale data (brokers không còn gửi data)
        cleanup_stale_data()
        
        logger.info(f"Received data from {broker}: {len(symbols_data)} symbols")
        return jsonify({"ok": True, "message": "Data received"})
        
    except Exception as e:
        logger.error(f"Error receiving data: {e}")
        return jsonify({"ok": False, "error": str(e)}), 500

@app.route('/api/receive_positions', methods=['POST'])
def receive_positions():
    """Nhận dữ liệu positions từ EA (optional, để tương thích)"""
    try:
        data = request.get_json(force=True)
        broker = data.get('broker', 'Unknown')
        logger.info(f"Received positions from {broker}")
        return jsonify({"ok": True, "message": "Positions received"})
    except Exception as e:
        logger.error(f"Error receiving positions: {e}")
        return jsonify({"ok": False, "error": str(e)}), 500

@app.route('/api/get_signal', methods=['GET'])
def get_signal():
    """Endpoint để EA poll lệnh (tương thích, trả về empty)"""
    return jsonify({})

@app.route('/health', methods=['GET'])
def health():
    """Health check endpoint"""
    return jsonify({
        "status": "running",
        "brokers": list(market_data.keys()),
        "total_symbols": sum(len(symbols) for symbols in market_data.values())
    })

# ===================== GUI APPLICATION =====================
class GapSpikeDetectorGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Gap & Spike Detector v2.14.0 - MT4/MT5")
        self.root.geometry("1400x800")
        
        # Configure styles
        style = ttk.Style()
        style.configure('Accent.TButton', 
                       foreground='#0066cc', 
                       font=('Arial', 9, 'bold'))
        
        # Variables
        self.filter_gap_only = tk.BooleanVar(value=False)
        self.filter_spike_only = tk.BooleanVar(value=False)
        self.auto_scroll = tk.BooleanVar(value=True)
        self.delay_threshold = tk.IntVar(value=delay_settings['threshold'])  # Load from settings
        self.python_reset_job = None
        
        self.setup_ui()
        self.update_display()
        self.update_python_reset_schedule(log_message=False)
        
    def setup_ui(self):
        """Thiết lập giao diện"""
        # Top Frame - Controls
        control_frame = ttk.Frame(self.root, padding="10")
        control_frame.pack(fill=tk.X)
        
        ttk.Label(control_frame, text="Gap & Spike Detector", font=('Arial', 16, 'bold')).pack(side=tk.LEFT, padx=10)

        # Filters
        ttk.Checkbutton(control_frame, text="Chỉ hiển thị GAP", variable=self.filter_gap_only).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(control_frame, text="Chỉ hiển thị SPIKE", variable=self.filter_spike_only).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(control_frame, text="Tự động cuộn", variable=self.auto_scroll).pack(side=tk.LEFT, padx=5)
        
        # Delay threshold config (moved to Settings, keep here for quick view/adjust)
        ttk.Label(control_frame, text="Delay (s):").pack(side=tk.LEFT, padx=(20, 5))
        delay_spinbox = ttk.Spinbox(control_frame, from_=30, to=600, textvariable=self.delay_threshold, width=8)
        delay_spinbox.pack(side=tk.LEFT, padx=5)
        ttk.Label(control_frame, text="(⚙️ Cài đặt để xem thêm)", foreground='gray', font=('Arial', 8)).pack(side=tk.LEFT, padx=2)

        ttk.Button(control_frame, text="Cài đặt", command=self.open_settings).pack(side=tk.RIGHT, padx=5)
        ttk.Button(control_frame, text="📸 Hình ảnh", command=self.open_picture_gallery).pack(side=tk.RIGHT, padx=5)
        ttk.Button(control_frame, text="Kết nối", command=self.open_connected_brokers).pack(side=tk.RIGHT, padx=5)
        ttk.Button(control_frame, text="🔄 Khởi động lại Python", command=self.reset_python_connection,
                  style='Accent.TButton').pack(side=tk.RIGHT, padx=5)
        ttk.Button(control_frame, text="Xóa cảnh báo", command=self.clear_alerts).pack(side=tk.RIGHT, padx=5)
        
        # Connection Status Warning Frame
        self.connection_warning_frame = ttk.Frame(self.root)
        self.connection_warning_frame.pack(fill=tk.X, padx=10, pady=2)
        
        self.connection_warning_label = ttk.Label(
            self.connection_warning_frame, 
            text="", 
            font=('Arial', 10, 'bold'),
            foreground='red',
            background='#ffcccc',
            padding=5
        )
        # Initially hidden
        
        # Delay Board Frame (replaces Connected Brokers)
        delay_frame = ttk.LabelFrame(self.root, text="⏱️ Delay Alert (Bid không đổi)", padding="10")
        delay_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Create Treeview for delays
        delay_columns = ('Broker', 'Symbol', 'Bid', 'Last Change', 'Delay Time', 'Status')
        self.delay_tree = ttk.Treeview(delay_frame, columns=delay_columns, show='headings', height=4)
        
        self.delay_tree.heading('Broker', text='Broker')
        self.delay_tree.heading('Symbol', text='Symbol')
        self.delay_tree.heading('Bid', text='Bid Price')
        self.delay_tree.heading('Last Change', text='Thay đổi lần cuối')
        self.delay_tree.heading('Delay Time', text='Thời gian Delay')
        self.delay_tree.heading('Status', text='Trạng thái')
        
        self.delay_tree.column('Broker', width=150)
        self.delay_tree.column('Symbol', width=100)
        self.delay_tree.column('Bid', width=100)
        self.delay_tree.column('Last Change', width=120)
        self.delay_tree.column('Delay Time', width=100)
        self.delay_tree.column('Status', width=200)
        
        self.delay_tree.pack(fill=tk.X, pady=5)
        
        # Tags for delay status
        self.delay_tree.tag_configure('delay_warning', background='#fff4cc')  # Yellow
        self.delay_tree.tag_configure('delay_critical', background='#ffcccc')  # Red
        
        # Bind double-click to open chart
        self.delay_tree.bind('<Double-Button-1>', self.on_delay_double_click)
        
        # Bind right-click for context menu
        self.delay_tree.bind('<Button-3>', self.show_delay_context_menu)
        
        # Stats Frame
        stats_frame = ttk.LabelFrame(self.root, text="Thống kê", padding="10")
        stats_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.stats_label = ttk.Label(stats_frame, text="Đang chờ dữ liệu...", font=('Arial', 10))
        self.stats_label.pack()
        
        # Alert Board (Bảng Kèo)
        alert_frame = ttk.LabelFrame(self.root, text="🔔 Bảng Kèo (Gap/Spike Alert)", padding="10")
        alert_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Control frame for checkbox and settings
        alert_control_frame = ttk.Frame(alert_frame)
        alert_control_frame.pack(fill=tk.X, pady=(0, 5))
        
        # Checkbox: Only check gap/spike when market is open
        self.only_check_open_var = tk.BooleanVar(value=market_open_settings.get('only_check_open_market', False))
        self.only_check_open_checkbox = ttk.Checkbutton(
            alert_control_frame,
            text="⏰ Chỉ xét gap/spike khi sản phẩm mở cửa",
            variable=self.only_check_open_var,
            command=self.toggle_only_check_open_market
        )
        self.only_check_open_checkbox.pack(side=tk.LEFT, padx=5)
        
        # Skip minutes after market open
        ttk.Label(alert_control_frame, text=" | Bỏ").pack(side=tk.LEFT, padx=(10, 2))
        self.skip_minutes_var = tk.IntVar(value=market_open_settings.get('skip_minutes_after_open', 0))
        skip_spinbox = ttk.Spinbox(
            alert_control_frame,
            from_=0,
            to=60,
            textvariable=self.skip_minutes_var,
            width=5,
            command=self.update_skip_minutes
        )
        skip_spinbox.pack(side=tk.LEFT, padx=2)
        skip_spinbox.bind('<FocusOut>', lambda e: self.update_skip_minutes())
        skip_spinbox.bind('<Return>', lambda e: self.update_skip_minutes())
        ttk.Label(alert_control_frame, text="phút sau khi sản phẩm mở cửa không xét gap/spike (0 = tắt)").pack(side=tk.LEFT, padx=2)
        
        # Create Treeview for alerts
        alert_columns = ('Broker', 'Symbol', 'Price', 'Gap %', 'Spike %', 'Alert Type', 'Time', 'Grace')
        self.alert_tree = ttk.Treeview(alert_frame, columns=alert_columns, show='headings', height=5)
        
        self.alert_tree.heading('Broker', text='Broker')
        self.alert_tree.heading('Symbol', text='Symbol')
        self.alert_tree.heading('Price', text='Price')
        self.alert_tree.heading('Gap %', text='Gap %')
        self.alert_tree.heading('Spike %', text='Spike %')
        self.alert_tree.heading('Alert Type', text='Loại cảnh báo')
        self.alert_tree.heading('Time', text='Thời gian')
        self.alert_tree.heading('Grace', text='Thời gian chờ')
        
        self.alert_tree.column('Broker', width=120)
        self.alert_tree.column('Symbol', width=100)
        self.alert_tree.column('Price', width=100)
        self.alert_tree.column('Gap %', width=80)
        self.alert_tree.column('Spike %', width=80)
        self.alert_tree.column('Alert Type', width=120)
        self.alert_tree.column('Time', width=80)
        self.alert_tree.column('Grace', width=100)
        
        # Scrollbar for alert board
        alert_vsb = ttk.Scrollbar(alert_frame, orient="vertical", command=self.alert_tree.yview)
        self.alert_tree.configure(yscrollcommand=alert_vsb.set)
        
        self.alert_tree.pack(side=tk.LEFT, fill=tk.X, expand=True)
        alert_vsb.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Tags for alert board
        self.alert_tree.tag_configure('gap', background='#ffcccc')
        self.alert_tree.tag_configure('spike', background='#ccffcc')
        self.alert_tree.tag_configure('both', background='#ffffcc')
        self.alert_tree.tag_configure('grace', background='#e0e0e0')
        
        # Bind double-click to open chart
        self.alert_tree.bind('<Double-Button-1>', self.on_alert_double_click)
        
        # Main Table Frame
        table_frame = ttk.LabelFrame(self.root, text="Kết quả phát hiện Gap & Spike", padding="10")
        table_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Search/Filter Frame
        search_frame = ttk.Frame(table_frame)
        search_frame.pack(fill=tk.X, pady=(0, 5))
        
        ttk.Label(search_frame, text="🔍 Tìm kiếm sản phẩm:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.search_symbol_var = tk.StringVar()
        self.search_symbol_var.trace('w', lambda *args: self.filter_symbols_by_search())
        
        search_entry = ttk.Entry(search_frame, textvariable=self.search_symbol_var, width=25)
        search_entry.pack(side=tk.LEFT, padx=5)
        ttk.Label(search_frame, text="(Nhập tên sản phẩm để lọc)", foreground='gray', font=('Arial', 8)).pack(side=tk.LEFT, padx=5)
    
        # Clear search button
        ttk.Button(search_frame, text="✕ Clear", command=lambda: self.search_symbol_var.set("")).pack(side=tk.LEFT, padx=2)
        
        # Treeview - XÓA cột Gap % và Spike %
        columns = ('Time', 'Broker', 'Symbol', 'Price', 'Gap Threshold', 'Spike Threshold', 'Status')
        self.tree = ttk.Treeview(table_frame, columns=columns, show='headings', height=20)

        self.filter_symbols_by_search()
        # Column headings
        self.tree.heading('Time', text='Thời gian')
        self.tree.heading('Broker', text='Broker')
        self.tree.heading('Symbol', text='Symbol')
        self.tree.heading('Price', text='Price')
        self.tree.heading('Gap Threshold', text='Ngưỡng Gap (%)')
        self.tree.heading('Spike Threshold', text='Ngưỡng Spike (%)')
        self.tree.heading('Status', text='Trạng thái')
        
        # Column widths
        self.tree.column('Time', width=70)
        self.tree.column('Broker', width=100)
        self.tree.column('Symbol', width=80)
        self.tree.column('Price', width=85)
        self.tree.column('Gap Threshold', width=120)
        self.tree.column('Spike Threshold', width=130)
        self.tree.column('Status', width=80)
        
        # Scrollbars
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        # Use pack() instead of grid() for consistency with parent container
        self.tree.pack(fill=tk.BOTH, expand=True, side=tk.TOP)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        
        table_frame.grid_rowconfigure(0, weight=1)
        table_frame.grid_columnconfigure(0, weight=1)
        
        # Tags for colors
        self.tree.tag_configure('gap_detected', background='#ffcccc')
        self.tree.tag_configure('spike_detected', background='#ccffcc')
        self.tree.tag_configure('both_detected', background='#ffffcc')
        
        # Bind double-click to edit threshold (Gap Threshold or Spike Threshold columns)
        self.tree.bind('<Double-Button-1>', self.on_symbol_double_click)
        
        # Store for search filtering
        self.last_search_term = ""
        
        # Log Frame
        log_frame = ttk.LabelFrame(self.root, text="Nhật ký hoạt động", padding="10")
        log_frame.pack(fill=tk.BOTH, expand=False, padx=10, pady=5)
        
        self.log_text = scrolledtext.ScrolledText(log_frame, height=8, wrap=tk.WORD)
        self.log_text.pack(fill=tk.BOTH, expand=True)
        
    def update_display(self):
        """Cập nhật hiển thị dữ liệu"""
        try:
            with data_lock:
                # Update connection status warning
                self.update_connection_warning()
                
                # Update delay board
                self.update_delay_board_display()
                
                # Update alert board
                self.update_alert_board_display()
                
                # Clear existing items
                for item in self.tree.get_children():
                    self.tree.delete(item)
                
                # Statistics
                total_symbols = 0
                total_gaps = 0
                total_spikes = 0
                brokers = set()
                
                # Sort by broker name first, then timestamp descending
                sorted_results = sorted(
                    gap_spike_results.items(),
                    key=lambda x: (x[1].get('broker', ''), -x[1].get('timestamp', 0))
                )
                
                for key, result in sorted_results:
                    symbol = result.get('symbol', '')
                    broker = result.get('broker', '')
                    timestamp = result.get('timestamp', 0)
                    price = result.get('price', 0)
                    gap_info = result.get('gap', {})
                    spike_info = result.get('spike', {})
                    
                    gap_detected = gap_info.get('detected', False)
                    spike_detected = spike_info.get('detected', False)
                    
                    # Apply filters
                    if self.filter_gap_only.get() and not gap_detected:
                        continue
                    if self.filter_spike_only.get() and not spike_detected:
                        continue
                    
                    total_symbols += 1
                    brokers.add(broker)
                    if gap_detected:
                        total_gaps += 1
                    if spike_detected:
                        total_spikes += 1
                    
                    # Format data (server time - không convert timezone)
                    time_str = server_timestamp_to_datetime(timestamp).strftime('%H:%M:%S')

                    # Hướng gap (để dùng trong Status)
                    gap_dir = gap_info.get('direction', 'none').upper()
    
                    # Lấy ngưỡng từ settings (Broker_Symbol > Broker_* > Symbol > * > default)
                    gap_threshold = get_threshold_for_display(broker, symbol, 'gap')
                    spike_threshold = get_threshold_for_display(broker, symbol, 'spike')
    
                    # Status
                    status_parts = []
                    if gap_detected:
                        status_parts.append(f"GAP {gap_dir}")
                    if spike_detected:
                        status_parts.append("SPIKE")
                    status = " + ".join(status_parts) if status_parts else "Normal"

                    # Determine tag
                    tag = ''
                    if gap_detected and spike_detected:
                        tag = 'both_detected'
                    elif gap_detected:
                        tag = 'gap_detected'
                    elif spike_detected:
                        tag = 'spike_detected'

                    # Insert row  (các cột: Time, Broker, Symbol, Price, Gap Threshold, Spike Threshold, Status)
                    self.tree.insert('', 'end', values=(
                        time_str,
                        broker,
                        symbol,
                        f"{price:.5f}",
                        f"{gap_threshold:.3f}%" if gap_threshold is not None else "",
                        f"{spike_threshold:.3f}%" if spike_threshold is not None else "",
                        status
                    ), tags=(tag,))

                
                # Update statistics
                stats_text = f"Brokers: {len(brokers)} | Symbols: {total_symbols} | GAPs: {total_gaps} | SPIKEs: {total_spikes}"
                self.stats_label.config(text=stats_text)
                
                # Sau khi fill xong, nếu đang có keyword search thì áp dụng lại filter
                if hasattr(self, 'search_symbol_var'):
                    current_search = self.search_symbol_var.get().strip()
                    if current_search:
                        try:
                            self.filter_symbols_by_search()
                        except Exception as _e:
                            logger.error(f"Error reapplying search filter: {_e}")
                    else:
                        # Không search thì auto scroll về đầu nếu bật
                        if self.auto_scroll.get() and self.tree.get_children():
                            self.tree.see(self.tree.get_children()[0])
                else:
                    # Trường hợp hiếm: chưa có search_symbol_var
                    if self.auto_scroll.get() and self.tree.get_children():
                        self.tree.see(self.tree.get_children()[0])
                    
        except Exception as e:
            logger.error(f"Error updating display: {e}")
        
        # Schedule next update
        self.root.after(1000, self.update_display)
    
    def update_connection_warning(self):
        """Check and update connection status warning"""
        try:
            current_time = time.time()
            connection_timeout = 20  # 20 seconds
            
            # Check each broker's connection status
            broker_statuses = {}
            
            for broker in market_data.keys():
                # Get all symbols for this broker
                broker_symbols = list(market_data[broker].keys())
                
                if not broker_symbols:
                    broker_statuses[broker] = 'disconnected'
                    continue
                
                # Check if ANY symbol is still updating (< 20s delay)
                has_active_symbol = False
                
                for symbol in broker_symbols:
                    key = f"{broker}_{symbol}"
                    if key in bid_tracking:
                        last_change_time = bid_tracking[key]['last_change_time']
                        delay_duration = current_time - last_change_time
                        
                        if delay_duration < connection_timeout:
                            has_active_symbol = True
                            break
                
                broker_statuses[broker] = 'connected' if has_active_symbol else 'disconnected'
            
            # Determine overall status
            disconnected_brokers = [b for b, s in broker_statuses.items() if s == 'disconnected']
            connected_brokers = [b for b, s in broker_statuses.items() if s == 'connected']
            
            # Update warning display
            if not broker_statuses:
                # No brokers at all
                warning_text = "⚠️ PYTHON MẤT KẾT NỐI - Không có dữ liệu từ EA"
                self.connection_warning_label.config(text=warning_text, background='#ff9999')
                self.connection_warning_label.pack(fill=tk.X, pady=2)
            elif not connected_brokers:
                # All brokers disconnected
                warning_text = "⚠️ PYTHON MẤT KẾT NỐI - Tất cả sàn không gửi dữ liệu (>20s)"
                self.connection_warning_label.config(text=warning_text, background='#ff9999')
                self.connection_warning_label.pack(fill=tk.X, pady=2)
            elif disconnected_brokers:
                # Some brokers disconnected
                broker_list = ", ".join(disconnected_brokers)
                warning_text = f"⚠️ MẤT KẾT NỐI SÀN: {broker_list} (Tất cả sản phẩm delay >20s)"
                self.connection_warning_label.config(text=warning_text, background='#ffcc99')
                self.connection_warning_label.pack(fill=tk.X, pady=2)
            else:
                # All OK - hide warning
                self.connection_warning_label.pack_forget()
            
        except Exception as e:
            logger.error(f"Error updating connection warning: {e}")
    
    def update_delay_board_display(self):
        """Cập nhật hiển thị Delay Board"""
        # Clear existing delay items
        for item in self.delay_tree.get_children():
            self.delay_tree.delete(item)
        
        current_time = time.time()
        delay_threshold = self.delay_threshold.get()
        
        # Find symbols with delayed bid
        delayed_symbols = []
        hidden_count = 0  # Count hidden symbols (>60 minutes or manually hidden)
        manually_hidden_count = 0  # Count manually hidden
        
        for key, tracking_info in bid_tracking.items():
            last_change_time = tracking_info['last_change_time']
            delay_duration = current_time - last_change_time
            
            # Only show if delay >= threshold
            if delay_duration >= delay_threshold:
                broker, symbol = key.split('_', 1)
                
                # 🔒 Skip nếu bị hide thủ công
                if key in manual_hidden_delays:
                    manually_hidden_count += 1
                    hidden_count += 1
                    continue
                
                # Get current data from market_data
                if broker in market_data and symbol in market_data[broker]:
                    symbol_data = market_data[broker][symbol]
                    current_bid = symbol_data.get('bid', 0)
                    is_open = symbol_data.get('isOpen', False)
                    
                    # ⚠️ CHỈ HIỂN thị delay nếu đang trong giờ giao dịch
                    if not is_open:
                        continue  # Bỏ qua nếu thị trường đóng cửa
                    
                    # 🔒 Ẩn nếu delay quá 60 phút (3600 giây) - auto hide
                    auto_hide_time = delay_settings.get('auto_hide_time', 3600)
                    if delay_duration >= auto_hide_time:
                        hidden_count += 1
                        continue  # Ẩn khỏi bảng chính, chỉ hiển thị trong Hidden window
                    
                    delayed_symbols.append({
                        'broker': broker,
                        'symbol': symbol,
                        'bid': current_bid,
                        'last_change_time': last_change_time,
                        'delay_duration': delay_duration
                    })
        
        # Sort by delay duration (longest first)
        delayed_symbols.sort(key=lambda x: x['delay_duration'], reverse=True)
        
        # Add to tree
        for item in delayed_symbols:
            broker = item['broker']
            symbol = item['symbol']
            bid = item['bid']
            last_change_time = item['last_change_time']
            delay_duration = item['delay_duration']
            
            # Format display
            last_change_str = server_timestamp_to_datetime(last_change_time).strftime('%H:%M:%S')
            delay_minutes = int(delay_duration / 60)
            delay_seconds = int(delay_duration % 60)
            delay_str = f"{delay_minutes}m {delay_seconds}s"
            
            # Determine tag/status
            if delay_duration >= delay_threshold * 2:
                tag = 'delay_critical'
                status = f"🔴 CRITICAL DELAY ({delay_str})"
            else:
                tag = 'delay_warning'
                status = f"⚠️ DELAYED ({delay_str})"
            
            # Insert row
            self.delay_tree.insert('', 'end', values=(
                broker,
                symbol,
                f"{bid:.5f}",
                last_change_str,
                delay_str,
                status
            ), tags=(tag,))
        
        # If no delays, show message
        if not delayed_symbols and hidden_count == 0:
            self.delay_tree.insert('', 'end', values=(
                'No delays detected',
                '-',
                '-',
                '-',
                '-',
                f'✅ All trading symbols updating (threshold: {delay_threshold}s)'
            ))
        elif not delayed_symbols and hidden_count > 0:
            # Có delays nhưng tất cả đều bị ẩn
            self.delay_tree.insert('', 'end', values=(
                'No active delays',
                '-',
                '-',
                '-',
                '-',
                f'🔒 {hidden_count} symbol(s) hidden (>60 min) - Click "Hidden" to view'
            ))
    
    def update_alert_board_display(self):
        """Cập nhật hiển thị Bảng Kèo"""
        # Clear existing alert items
        for item in self.alert_tree.get_children():
            self.alert_tree.delete(item)
        
        current_time = time.time()
        
        # Sort by broker name
        sorted_alerts = sorted(
            alert_board.items(),
            key=lambda x: (x[1]['data'].get('broker', ''), x[1]['data'].get('symbol', ''))
        )
        
        for key, alert_info in sorted_alerts:
            result = alert_info['data']
            grace_start = alert_info['grace_period_start']
            
            symbol = result.get('symbol', '')
            broker = result.get('broker', '')
            timestamp = result.get('timestamp', 0)
            price = result.get('price', 0)
            gap_info = result.get('gap', {})
            spike_info = result.get('spike', {})
            
            gap_detected = gap_info.get('detected', False)
            spike_detected = spike_info.get('detected', False)
            
            gap_pct = f"{gap_info.get('percentage', 0):.3f}%"
            spike_pct = f"{spike_info.get('strength', 0):.3f}%"
            
            # Determine alert type
            alert_type_parts = []
            if gap_detected:
                gap_dir = gap_info.get('direction', 'none').upper()
                alert_type_parts.append(f"GAP {gap_dir}")
            if spike_detected:
                alert_type_parts.append("SPIKE")
            alert_type = " + ".join(alert_type_parts) if alert_type_parts else "Ending..."
            
            # Time
            time_str = server_timestamp_to_datetime(timestamp).strftime('%H:%M:%S')
            
            # Grace period
            if grace_start is not None:
                elapsed = current_time - grace_start
                remaining = max(0, 15 - int(elapsed))
                grace_str = f"Xóa sau {remaining}s"
                tag = 'grace'
            else:
                grace_str = "Active"
                # Determine tag
                if gap_detected and spike_detected:
                    tag = 'both'
                elif gap_detected:
                    tag = 'gap'
                elif spike_detected:
                    tag = 'spike'
                else:
                    tag = 'grace'
            
            # Insert row
            self.alert_tree.insert('', 'end', values=(
                broker,
                symbol,
                f"{price:.5f}",
                gap_pct,
                spike_pct,
                alert_type,
                time_str,
                grace_str
            ), tags=(tag,))
        
        # If no alerts, show message
        if not alert_board:
            self.alert_tree.insert('', 'end', values=(
                'Không có kèo',
                '-',
                '-',
                '-',
                '-',
                'Chờ phát hiện Gap/Spike...',
                '-',
                '-'
            ))
    
    def clear_alerts(self):
        """Xóa tất cả alerts"""
        with data_lock:
            gap_spike_results.clear()
            alert_board.clear()
        self.log("Đã xóa tất cả alerts và bảng kèo")
    
    def reset_python_connection(self):
        """Reset Python connection - manual trigger"""
        self.perform_python_reset(
            skip_confirmation=False,
            show_message=True,
            reason="manual",
            reschedule_after=True
        )
    
    def perform_python_reset(self, skip_confirmation=False, show_message=True, reason="manual", reschedule_after=True):
        """Core logic to reset Python connection (shared by manual & auto)"""
        reset_executed = False
        try:
            if not skip_confirmation:
                confirm = messagebox.askyesno(
                    "Reset Python Connection",
                    "🔄 Reset Python Connection?\n\n"
                    "Hành động này sẽ:\n"
                    "• Xóa dữ liệu kết nối & Gap/Spike hiện tại\n"
                    "• Clear connection cache\n"
                    "• Chờ EAs gửi dữ liệu mới\n\n"
                    "✅ Dữ liệu Chart sẽ được GIỮ NGUYÊN\n"
                    "⚠️ Các sàn sẽ tự động kết nối lại khi EA gửi data\n\n"
                    "Continue?"
                )

                if not confirm:
                    return False

            reset_executed = True
            if skip_confirmation:
                self.log("🔄 Auto reset Python connection (giữ chart data)...")
            else:
                self.log("🔄 Đang reset Python connection (giữ chart data)...")

            with data_lock:
                market_data.clear()
                gap_spike_results.clear()
                alert_board.clear()
                bid_tracking.clear()
                # candle_data.clear()  # ← KHÔNG xóa để giữ lại chart data
            
            self.tree.delete(*self.tree.get_children())
            self.alert_tree.delete(*self.alert_tree.get_children())
            self.delay_tree.delete(*self.delay_tree.get_children())
            self.connection_warning_label.pack_forget()
            
            if show_message:
                messagebox.showinfo(
                    "Reset Successful",
                    "✅ Python connection đã được reset!\n\n"
                    "📡 Server đang chờ dữ liệu từ EAs\n"
                    "🔌 Các sàn sẽ tự động kết nối lại\n"
                    "📊 Chart data đã được GIỮ NGUYÊN\n\n"
                    "Không cần restart EAs, chỉ cần chờ data được gửi."
                )
            
            if skip_confirmation:
                self.log("✅ Auto reset Python connection (chart data được giữ).")
            else:
                self.log("✅ Reset thành công (chart data được giữ)!")
            self.log("⏳ Đang chờ EAs gửi dữ liệu mới...")
            self.log("📡 Flask server vẫn đang chạy trên port 80")
            self.log("🔌 Các sàn sẽ tự động kết nối khi EA gửi data")
            self.log("📊 Dữ liệu Chart vẫn được giữ nguyên")
            
            logger.info(f"Python connection reset ({reason})")
            return True
        
        except Exception as e:
            logger.error(f"Error resetting Python connection: {e}", exc_info=True)
            if show_message:
                messagebox.showerror("Error", f"Lỗi reset connection: {str(e)}")
            else:
                self.log(f"❌ Auto reset Python thất bại: {e}")
            return False
        
        finally:
            if reschedule_after and reset_executed and python_reset_settings.get('enabled', False):
                self.update_python_reset_schedule(log_message=False)
    
    def update_python_reset_schedule(self, log_message=True):
        """Schedule or cancel automatic Python reset"""
        if self.python_reset_job:
            try:
                self.root.after_cancel(self.python_reset_job)
            except Exception:
                pass
            self.python_reset_job = None
        
        enabled = python_reset_settings.get('enabled', False)
        interval_minutes = max(1, int(python_reset_settings.get('interval_minutes', 30) or 30))
        
        if enabled:
            interval_ms = interval_minutes * 60 * 1000
            self.python_reset_job = self.root.after(interval_ms, self._auto_reset_python)
            if log_message:
                self.log(f"⏱️ Auto reset Python: {interval_minutes} phút/lần")
        else:
            if log_message:
                self.log("⏹️ Auto reset Python đã tắt")
    
    def _auto_reset_python(self):
        """Callback thực hiện reset định kỳ"""
        self.python_reset_job = None
        executed = self.perform_python_reset(
            skip_confirmation=True,
            show_message=False,
            reason="auto",
            reschedule_after=False
        )
        if python_reset_settings.get('enabled', False):
            self.update_python_reset_schedule(log_message=False)
        if executed:
            interval = python_reset_settings.get('interval_minutes', 30)
            self.log(f"⏱️ Auto reset Python hoàn tất (chu kỳ {interval} phút)")
    
    def log(self, message):
        """Thêm log message"""
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_text.see(tk.END)
    
    def filter_symbols_by_search(self):
        """Tìm kiếm sản phẩm với sắp xếp theo độ khớp
        
        Độ ưu tiên (từ cao đến thấp):
        1. Khớp hoàn toàn (exact match)
        2. Khớp từ đầu (starts with)
        3. Chứa chuỗi tìm (contains)
        4. Không khớp (hidden)
        """
        search_term = self.search_symbol_var.get().strip().upper()
        
        # Lấy tất cả items hiện tại trong tree
        all_items = self.tree.get_children()
        
        if not search_term:
            # Không có từ tìm → hiển thị tất cả
            for item in all_items:
                self.tree.item(item, tags=self.tree.item(item, 'tags'))  # Giữ nguyên
            return
        
        # Phân loại items theo độ khớp
        exact_matches = []      # Khớp hoàn toàn
        starts_matches = []     # Khớp từ đầu
        contains_matches = []   # Chứa chuỗi
        no_matches = []         # Không khớp
        
        for item in all_items:
            values = self.tree.item(item, 'values')
            if not values or len(values) < 3:
                continue
            
            # Lấy symbol từ column Symbol (index 2)
            symbol = str(values[2]).upper()
            broker = str(values[1]).upper()
            
            # Kiểm tra độ khớp
            if symbol == search_term or broker == search_term:
                # Khớp hoàn toàn
                exact_matches.append(item)
            elif symbol.startswith(search_term) or broker.startswith(search_term):
                # Khớp từ đầu
                starts_matches.append(item)
            elif search_term in symbol or search_term in broker:
                # Chứa chuỗi
                contains_matches.append(item)
            else:
                # Không khớp
                no_matches.append(item)
        
        # Sắp xếp và hiển thị
        sorted_items = exact_matches + starts_matches + contains_matches
        
        # Ẩn items không khớp
        for item in no_matches:
            self.tree.detach(item)
        
        # Hiển thị items khớp
        for idx, item in enumerate(sorted_items):
            self.tree.reattach(item, '', idx)
        
        # Auto scroll to first match
        if sorted_items:
            self.tree.see(sorted_items[0])

    def open_settings(self):
        """Mở cửa sổ settings"""
        SettingsWindow(self.root, self)
    
    def open_trading_hours(self):
        """Mở cửa sổ Trading Hours"""
        TradingHoursWindow(self.root, self)
    
    def open_connected_brokers(self):
        """Mở cửa sổ Connected Brokers"""
        ConnectedBrokersWindow(self.root, self)
    
    def open_raw_data_viewer(self):
        """Mở cửa sổ Raw Data Viewer"""
        RawDataViewerWindow(self.root, self)
    
    def open_picture_gallery(self):
        """Mở cửa sổ Picture Gallery"""
        PictureGalleryWindow(self.root, self)
    
    def toggle_only_check_open_market(self):
        """Toggle setting: Only check gap/spike when market is open"""
        try:
            new_value = self.only_check_open_var.get()
            with data_lock:
                market_open_settings['only_check_open_market'] = new_value
                save_market_open_settings()
            
            status = "BẬT" if new_value else "TẮT"
            logger.info(f"Only check open market: {status}")
            messagebox.showinfo(
                "Cập nhật thành công",
                f"Chỉ xét gap/spike khi sản phẩm mở cửa: {status}\n\n"
                f"{'✅ Sẽ chỉ tính gap/spike cho sản phẩm đang trong giờ trade' if new_value else '❌ Sẽ tính gap/spike cho tất cả sản phẩm bất kể giờ trade'}"
            )
        except Exception as e:
            logger.error(f"Error toggling only check open market: {e}")
            messagebox.showerror("Lỗi", f"Không thể cập nhật setting: {e}")
    
    def update_skip_minutes(self):
        """Update skip minutes after market open setting"""
        try:
            skip_minutes = self.skip_minutes_var.get()
            with data_lock:
                market_open_settings['skip_minutes_after_open'] = skip_minutes
                save_market_open_settings()
            
            logger.info(f"Skip minutes after market open: {skip_minutes}")
            if skip_minutes > 0:
                messagebox.showinfo(
                    "Cập nhật thành công",
                    f"Bỏ {skip_minutes} phút đầu sau khi sản phẩm mở cửa\n\n"
                    f"✅ Không xét gap/spike trong {skip_minutes} phút đầu mỗi session\n"
                    f"✅ Ví dụ: Session 2h-9h → Gap/Spike hoạt động từ 2h{skip_minutes:02d}p - 9h"
                )
            else:
                messagebox.showinfo(
                    "Cập nhật thành công",
                    f"Tắt chức năng bỏ phút đầu\n\n"
                    f"✅ Gap/Spike sẽ hoạt động ngay khi session mở cửa"
                )
        except Exception as e:
            logger.error(f"Error updating skip minutes: {e}")
            messagebox.showerror("Lỗi", f"Không thể cập nhật setting: {e}")
    
    def open_hidden_delays(self):
        """Mở cửa sổ Hidden Delays"""
        HiddenDelaysWindow(self.root, self)
    
    def on_symbol_double_click(self, event):
            global gap_settings, spike_settings 
            """Double-click trên bảng chính:
            - Nếu click vào cột Gap/Spike Threshold -> chỉnh ngưỡng
            - Nếu click vào cột khác -> mở chart như cũ
            """
            try:
                # Lấy item được click
                item = self.tree.selection()[0]
            except IndexError:
                # Không chọn dòng nào
                return

            try:
                values = self.tree.item(item, 'values')
                if not values or len(values) < 3:
                    return

                # Cột được click (#1..#7)
                column = self.tree.identify_column(event.x)

                # Values: (Time, Broker, Symbol, Price, Gap Threshold, Spike Threshold, Status)
                broker = values[1]
                symbol = values[2]

                # Nếu double-click vào cột Gap / Spike Threshold -> edit
                if column in ('#5', '#6') and broker and symbol:
                    threshold_type = 'gap' if column == '#5' else 'spike'
                    col_label = "Gap" if threshold_type == 'gap' else "Spike"

                    # Ngưỡng hiện tại
                    current_threshold = get_threshold_for_display(broker, symbol, threshold_type)
                    initial = f"{current_threshold:.3f}" if current_threshold is not None else ""

                    new_value = simpledialog.askstring(
                        f"Edit {col_label} Threshold",
                        f"{broker} {symbol}\nCurrent {col_label}: {initial}%\n\n"
                        f"Nhập {col_label} threshold mới (%):\n"
                        f"(Để trống = dùng lại rule default/wildcard)",
                        initialvalue=initial,
                        parent=self.root
                    )
                    if new_value is None:
                        return

                    new_value = new_value.strip()

                    # Cập nhật settings
                    global gap_settings, spike_settings
                    settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
                    key = f"{broker}_{symbol}"

                    if new_value == "":
                        # Xóa override riêng -> quay về dùng wildcard/default
                        if key in settings_dict:
                            del settings_dict[key]
                    else:
                        try:
                            threshold = float(new_value)
                        except ValueError:
                            messagebox.showerror("Error", "Vui lòng nhập số hợp lệ")
                            return
                        settings_dict[key] = threshold

                    # Lưu ra file
                    if threshold_type == 'gap':
                        save_gap_settings()
                    else:
                        save_spike_settings()

                    # Cập nhật cell hiển thị
                    updated_threshold = get_threshold_for_display(broker, symbol, threshold_type)
                    current_threshold = self.get_threshold_for_display(broker, symbol, threshold_type)
                    initial = f"{current_threshold:.3f}" if current_threshold is not None else ""

                    new_value = simpledialog.askstring(
                        f"Edit {col_label} Threshold",
                        f"{broker} {symbol}\nCurrent {col_label}: {initial}%\n\n"
                        f"Nhập {col_label} threshold mới (%):\n"
                        f"(Để trống = dùng lại rule default/wildcard)",
                        initialvalue=initial,
                        parent=self.root
                    )
                    if new_value is None:
                        return

                    new_value = new_value.strip()

                    # Cập nhật settings
                    settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
                    key = f"{broker}_{symbol}"

                    if new_value == "":
                        # Xóa override riêng -> quay về dùng wildcard/default
                        if key in settings_dict:
                            del settings_dict[key]
                    else:
                        try:
                            threshold = float(new_value)
                        except ValueError:
                            messagebox.showerror("Error", "Vui lòng nhập số hợp lệ")
                            return
                        settings_dict[key] = threshold

                    # Lưu ra file
                    if threshold_type == 'gap':
                        save_gap_settings()
                    else:
                        save_spike_settings()

                    # Cập nhật cell hiển thị
                    updated_threshold = self.get_threshold_for_display(broker, symbol, threshold_type)
                    display_val = f"{updated_threshold:.3f}%" if updated_threshold is not None else ""
                    if threshold_type == 'gap':
                        self.tree.set(item, 'Gap Threshold', display_val)
                    else:
                        self.tree.set(item, 'Spike Threshold', display_val)

                    logger.info(f"Edited {col_label} threshold from main table for {key}: {display_val}")
                    return

                # Double-click cột khác -> mở chart
                if broker and symbol:
                    self.open_chart(broker, symbol)
                    self.log(f"Opened chart for {symbol} ({broker})")

            except Exception as e:
                logger.error(f"Error handling double-click on main Gap/Spike table: {e}")

    
    def on_delay_double_click(self, event):
        """Xử lý double-click vào symbol từ bảng Delay để mở chart"""
        try:
            # Lấy item được click
            item = self.delay_tree.selection()[0]
            values = self.delay_tree.item(item, 'values')
            
            if not values or len(values) < 2:
                return
            
            # Values: (Broker, Symbol, Bid, Last Change, Delay Time, Status)
            broker = values[0]
            symbol = values[1]
            
            # Skip if it's a message row (không phải symbol data)
            if broker in ['No delays detected', 'No active delays'] or symbol == '-':
                return
            
            if broker and symbol:
                self.open_chart(broker, symbol)
                self.log(f"📈 Opened chart for {symbol} ({broker}) from Delay board")
                
        except IndexError:
            pass  # No selection
        except Exception as e:
            logger.error(f"Error opening chart from delay board: {e}")
    
    def on_alert_double_click(self, event):
        """Xử lý double-click vào symbol từ bảng Alert để mở chart"""
        try:
            # Lấy item được click
            item = self.alert_tree.selection()[0]
            values = self.alert_tree.item(item, 'values')
            
            if not values or len(values) < 2:
                return
            
            # Values: (Broker, Symbol, Price, Gap %, Spike %, Alert Type, Time, Grace)
            broker = values[0]
            symbol = values[1]
            
            # Skip if it's a message row
            if broker == 'Không có kèo' or symbol == '-':
                return
            
            if broker and symbol:
                self.open_chart(broker, symbol)
                self.log(f"🔔 Opened chart for {symbol} ({broker}) from Alert board")
                
        except IndexError:
            pass  # No selection
        except Exception as e:
            logger.error(f"Error opening chart from alert board: {e}")
    
    def show_delay_context_menu(self, event):
        """Show context menu for delay board"""
        try:
            # Select item under cursor
            item = self.delay_tree.identify_row(event.y)
            if not item:
                return
            
            self.delay_tree.selection_set(item)
            values = self.delay_tree.item(item, 'values')
            
            if not values or len(values) < 2:
                return
            
            broker = values[0]
            symbol = values[1]
            
            # Skip if it's a message row
            if broker in ['No delays detected', 'No active delays'] or symbol == '-':
                return
            
            # Create context menu
            context_menu = tk.Menu(self.root, tearoff=0)
            
            key = f"{broker}_{symbol}"
            
            if key in manual_hidden_delays:
                # If already hidden manually, show Unhide option
                context_menu.add_command(
                    label=f"🔓 Unhide {symbol}",
                    command=lambda: self.unhide_delay_symbol(broker, symbol)
                )
            else:
                # If not hidden, show Hide option
                context_menu.add_command(
                    label=f"🔒 Hide {symbol}",
                    command=lambda: self.hide_delay_symbol(broker, symbol)
                )
            
            context_menu.add_separator()
            context_menu.add_command(
                label=f"📈 Open Chart",
                command=lambda: self.open_chart(broker, symbol)
            )
            
            context_menu.tk_popup(event.x_root, event.y_root)
            
        except Exception as e:
            logger.error(f"Error showing delay context menu: {e}")
    
    def hide_delay_symbol(self, broker, symbol):
        """Hide symbol manually from delay board"""
        try:
            key = f"{broker}_{symbol}"
            manual_hidden_delays[key] = True
            save_manual_hidden_delays()
            
            self.log(f"🔒 Hidden {symbol} ({broker}) from Delay board")
            logger.info(f"Manually hidden: {key}")
            
            # Update display
            self.update_delay_board_display()
            
        except Exception as e:
            logger.error(f"Error hiding delay symbol: {e}")
    
    def unhide_delay_symbol(self, broker, symbol):
        """Unhide symbol from delay board"""
        try:
            key = f"{broker}_{symbol}"
            if key in manual_hidden_delays:
                del manual_hidden_delays[key]
                save_manual_hidden_delays()
            
            self.log(f"🔓 Unhidden {symbol} ({broker}) from Delay board")
            logger.info(f"Manually unhidden: {key}")
            
            # Update display
            self.update_delay_board_display()
            
        except Exception as e:
            logger.error(f"Error unhiding delay symbol: {e}")
    
    def open_chart(self, broker, symbol):
        """Mở chart window cho symbol"""
        RealTimeChartWindow(self.root, self, broker, symbol)

# ===================== REAL-TIME CHART WINDOW =====================
class RealTimeChartWindow:
    def __init__(self, parent, main_app, broker, symbol):
        self.main_app = main_app
        self.broker = broker
        self.symbol = symbol
        self.key = f"{broker}_{symbol}"
        
        self.window = tk.Toplevel(parent)
        self.window.title(f"📈 {symbol} - {broker} (M1)")
        self.window.geometry("1200x700")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Top Frame - Info
        info_frame = ttk.Frame(self.window, padding="10")
        info_frame.pack(fill=tk.X)
        
        ttk.Label(info_frame, text=f"📊 {symbol}", font=('Arial', 16, 'bold')).pack(side=tk.LEFT, padx=10)
        ttk.Label(info_frame, text=f"Broker: {broker}", font=('Arial', 10)).pack(side=tk.LEFT, padx=10)
        
        self.price_label = ttk.Label(info_frame, text="Bid: --- | Ask: ---", font=('Arial', 12, 'bold'))
        self.price_label.pack(side=tk.LEFT, padx=20)
        
        self.candle_count_label = ttk.Label(info_frame, text="Candles: 0/60", font=('Arial', 10))
        self.candle_count_label.pack(side=tk.LEFT, padx=10)
        
        self.time_label = ttk.Label(info_frame, text="", font=('Arial', 10))
        self.time_label.pack(side=tk.RIGHT, padx=10)
        
        # Chart Frame
        chart_frame = ttk.Frame(self.window)
        chart_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create matplotlib figure
        self.fig = Figure(figsize=(12, 6), dpi=100, facecolor='#1e1e1e')
        self.ax = self.fig.add_subplot(111, facecolor='#2d2d30')
        
        # Canvas
        self.canvas = FigureCanvasTkAgg(self.fig, master=chart_frame)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Configure plot style
        self.ax.tick_params(colors='white', labelsize=9)
        self.ax.spines['bottom'].set_color('#404040')
        self.ax.spines['top'].set_color('#404040') 
        self.ax.spines['right'].set_color('#404040')
        self.ax.spines['left'].set_color('#404040')
        self.ax.grid(True, alpha=0.2, color='#404040', linestyle='--')
        
        # Current bid/ask for horizontal lines
        self.bid_line = None
        self.ask_line = None
        
        # Initial draw
        self.update_chart()
        
        # Auto-refresh every 1 second
        self.is_running = True
        self.auto_refresh()
        
        # Cleanup on close
        self.window.protocol("WM_DELETE_WINDOW", self.on_close)
    
    def on_close(self):
        """Cleanup khi đóng window"""
        self.is_running = False
        self.window.destroy()
    
    def draw_candlesticks(self, candles):
        """Vẽ candlestick chart"""
        # Clear previous plot
        self.ax.clear()
        
        if not candles:
            # No candles yet - show message
            self.ax.text(0.5, 0.5, 'Đang tích lũy nến M1...\nVui lòng đợi ít phút để chart hiển thị',
                        ha='center', va='center', fontsize=12, color='white',
                        transform=self.ax.transAxes)
            return
        
        # Get last 60 candles (or less if not enough yet)
        candles_to_show = candles[-60:] if len(candles) >= 60 else candles
        
        # Draw candlesticks
        for i, (ts, o, h, l, c) in enumerate(candles_to_show):
            # Color: green if close > open, red if close < open
            color = '#26a69a' if c >= o else '#ef5350'
            wick_color = color
            
            # Draw high-low wick (thân nến)
            self.ax.plot([i, i], [l, h], color=wick_color, linewidth=1, solid_capstyle='round')
            
            # Draw open-close body (hình chữ nhật)
            body_height = abs(c - o)
            body_bottom = min(o, c)
            
            rect = Rectangle((i - 0.4, body_bottom), 0.8, body_height, 
                           facecolor=color, edgecolor=color, linewidth=1)
            self.ax.add_patch(rect)
        
        # Configure axes
        self.ax.set_xlim(-1, len(candles_to_show))
        
        # Y-axis (price)
        prices = [h for _, _, h, _, _ in candles_to_show] + [l for _, _, _, l, _ in candles_to_show]
        if prices:
            y_margin = (max(prices) - min(prices)) * 0.1
            self.ax.set_ylim(min(prices) - y_margin, max(prices) + y_margin)
        
        # X-axis labels (time)
        x_positions = list(range(0, len(candles_to_show), max(1, len(candles_to_show) // 10)))
        x_labels = []
        for pos in x_positions:
            if pos < len(candles_to_show):
                ts = candles_to_show[pos][0]
                x_labels.append(server_timestamp_to_datetime(ts).strftime('%H:%M'))
        
        self.ax.set_xticks(x_positions)
        self.ax.set_xticklabels(x_labels, rotation=45, ha='right')
        
        # Labels
        self.ax.set_xlabel('Time (M1)', color='white', fontsize=10)
        self.ax.set_ylabel('Price', color='white', fontsize=10)
        self.ax.set_title(f'{self.symbol} - M1 Chart', color='white', fontsize=12, pad=10)
        
        # Grid
        self.ax.grid(True, alpha=0.2, color='#404040', linestyle='--')
        
        # Style
        self.ax.tick_params(colors='white', labelsize=9)
        self.ax.spines['bottom'].set_color('#404040')
        self.ax.spines['top'].set_color('#404040')
        self.ax.spines['right'].set_color('#404040')
        self.ax.spines['left'].set_color('#404040')
    
    def update_chart(self):
        """Update chart với data mới"""
        try:
            with data_lock:
                # Get candle data
                candles = candle_data.get(self.key, [])
                
                # Update candle count label
                candle_count = len(candles)
                max_candles = 60
                self.candle_count_label.config(text=f"Candles: {candle_count}/{max_candles}")
                
                # Draw candlesticks
                self.draw_candlesticks(candles)
                
                # Get current bid/ask
                if self.broker in market_data and self.symbol in market_data[self.broker]:
                    symbol_data = market_data[self.broker][self.symbol]
                    bid = symbol_data.get('bid', 0)
                    ask = symbol_data.get('ask', 0)
                    digits = symbol_data.get('digits', 5)
                    
                    # Draw bid/ask lines
                    if bid > 0 and ask > 0:
                        # Bid line (red)
                        if self.bid_line:
                            self.bid_line.remove()
                        self.bid_line = self.ax.axhline(y=bid, color='#ef5350', linestyle='--', 
                                                        linewidth=1.5, alpha=0.8, label=f'Bid: {bid:.{digits}f}')
                        
                        # Ask line (green)
                        if self.ask_line:
                            self.ask_line.remove()
                        self.ask_line = self.ax.axhline(y=ask, color='#26a69a', linestyle='--', 
                                                        linewidth=1.5, alpha=0.8, label=f'Ask: {ask:.{digits}f}')
                        
                        # Legend
                        self.ax.legend(loc='upper left', fontsize=9, facecolor='#2d2d30', 
                                     edgecolor='#404040', labelcolor='white')
                        
                        # Update price label
                        self.price_label.config(text=f"Bid: {bid:.{digits}f} | Ask: {ask:.{digits}f}")
                
                # Update time label
                self.time_label.config(text=datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
                
                # Redraw canvas
                self.canvas.draw()
                
        except Exception as e:
            logger.error(f"Error updating chart: {e}")
    
    def auto_refresh(self):
        """Auto refresh chart every 1 second"""
        if self.is_running and self.window.winfo_exists():
            self.update_chart()
            self.window.after(1000, self.auto_refresh)

# ===================== SETTINGS WINDOW =====================
class SettingsWindow:
    
    def create_audio_settings_tab(self):
        """Create Audio Alerts Settings tab"""
        audio_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(audio_frame, text="🔊 Cảnh báo âm thanh")
        
        # Title
        ttk.Label(audio_frame, text="🔊 Cấu hình cảnh báo âm thanh",
                 font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=10)

        # Enable/Disable audio alerts
        enable_frame = ttk.LabelFrame(audio_frame, text="Bật cảnh báo âm thanh", padding="10")
        enable_frame.pack(fill=tk.X, pady=10)

        self.audio_enabled_var = tk.BooleanVar(value=audio_settings.get('enabled', True))
        ttk.Checkbutton(enable_frame, text="✅ Bật cảnh báo âm thanh cho phát hiện Gap/Spike/Delay",
                       variable=self.audio_enabled_var).pack(anchor=tk.W, pady=5)
        
        # Info text
        info_text = (
            "🔔 Khi bật, Python sẽ phát âm thanh cảnh báo khi phát hiện:\n"
            "  • Gap: Phát file Gap.mp3\n"
            "  • Spike: Phát file Spike.mp3\n"
            "  • Delay: Phát file Delay.mp3\n\n"
            "⏱️ Mỗi sản phẩm chỉ phát âm thanh 1 lần (cooldown 30 giây trước khi phát lại)\n"
            "🔄 Âm thanh được phát trong thread riêng (không chặn giao diện chính)"
        )
        ttk.Label(enable_frame, text=info_text, justify=tk.LEFT, foreground='blue',
                 font=('Arial', 9)).pack(anchor=tk.W, pady=10)
        
        # Audio file selection
        files_frame = ttk.LabelFrame(audio_frame, text="📁 Tệp âm thanh", padding="10")
        files_frame.pack(fill=tk.X, pady=10)

        # Gap sound
        gap_frame = ttk.Frame(files_frame)
        gap_frame.pack(fill=tk.X, pady=5)

        ttk.Label(gap_frame, text="Âm thanh cảnh báo Gap:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.gap_sound_var = tk.StringVar(value=audio_settings.get('gap_sound', 'sounds/Gap.mp3'))
        ttk.Entry(gap_frame, textvariable=self.gap_sound_var, width=40).pack(side=tk.LEFT, padx=5)
        ttk.Button(gap_frame, text="📂 Chọn",
                  command=lambda: self.browse_audio_file(self.gap_sound_var, 'Gap')).pack(side=tk.LEFT, padx=2)
        ttk.Button(gap_frame, text="🔊 Thử",
                  command=lambda: self.test_audio_file(self.gap_sound_var.get())).pack(side=tk.LEFT, padx=2)

        # Spike sound
        spike_frame = ttk.Frame(files_frame)
        spike_frame.pack(fill=tk.X, pady=5)

        ttk.Label(spike_frame, text="Âm thanh cảnh báo Spike:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.spike_sound_var = tk.StringVar(value=audio_settings.get('spike_sound', 'sounds/Spike.mp3'))
        ttk.Entry(spike_frame, textvariable=self.spike_sound_var, width=40).pack(side=tk.LEFT, padx=5)
        ttk.Button(spike_frame, text="📂 Chọn",
                  command=lambda: self.browse_audio_file(self.spike_sound_var, 'Spike')).pack(side=tk.LEFT, padx=2)
        ttk.Button(spike_frame, text="🔊 Thử",
                  command=lambda: self.test_audio_file(self.spike_sound_var.get())).pack(side=tk.LEFT, padx=2)

        # Delay sound
        delay_frame = ttk.Frame(files_frame)
        delay_frame.pack(fill=tk.X, pady=5)

        ttk.Label(delay_frame, text="Âm thanh cảnh báo Delay:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.delay_sound_var = tk.StringVar(value=audio_settings.get('delay_sound', 'sounds/Delay.mp3'))
        ttk.Entry(delay_frame, textvariable=self.delay_sound_var, width=40).pack(side=tk.LEFT, padx=5)
        ttk.Button(delay_frame, text="📂 Chọn",
                  command=lambda: self.browse_audio_file(self.delay_sound_var, 'Delay')).pack(side=tk.LEFT, padx=2)
        ttk.Button(delay_frame, text="🔊 Thử",
                  command=lambda: self.test_audio_file(self.delay_sound_var.get())).pack(side=tk.LEFT, padx=2)
        
        # Cooldown settings
        cooldown_frame = ttk.LabelFrame(audio_frame, text="⏱️ Thời gian chờ phát lại", padding="10")
        cooldown_frame.pack(fill=tk.X, pady=10)

        ttk.Label(cooldown_frame, text="Thời gian tối thiểu trước khi phát lại cùng cảnh báo (giây):",
                 font=('Arial', 9)).pack(side=tk.LEFT, padx=5)
        ttk.Label(cooldown_frame, text="30", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        ttk.Label(cooldown_frame, text="(Cố định - không thể thay đổi)", foreground='gray',
                 font=('Arial', 8)).pack(side=tk.LEFT, padx=5)

        # Separator
        ttk.Separator(audio_frame, orient='horizontal').pack(fill=tk.X, pady=10)

        # Quick actions
        action_frame = ttk.Frame(audio_frame)
        action_frame.pack(fill=tk.X, pady=10)

        ttk.Button(action_frame, text="💾 Lưu cài đặt âm thanh",
                  command=self.save_audio_settings_ui).pack(side=tk.LEFT, padx=5)
        ttk.Button(action_frame, text="🔄 Đặt lại mặc định",
                  command=self.reset_audio_defaults).pack(side=tk.LEFT, padx=5)
        ttk.Button(action_frame, text="🔊 Thử tất cả âm thanh",
                  command=self.test_all_sounds).pack(side=tk.LEFT, padx=5)
    
    def browse_audio_file(self, var, alert_type):
        """Browse and select audio file"""
        try:
            filename = filedialog.askopenfilename(
                title=f"Select {alert_type} Alert Sound",
                filetypes=[("MP3 Files", "*.mp3"), ("WAV Files", "*.wav"), ("All Files", "*.*")],
                initialdir="sounds"
            )
            if filename:
                var.set(filename)
                logger.info(f"Selected {alert_type} sound: {filename}")
        except Exception as e:
            logger.error(f"Error browsing audio file: {e}")
    
    def test_audio_file(self, filepath):
        """Test play an audio file"""
        try:
            if not filepath:
                messagebox.showwarning("Warning", "No file selected")
                return
            
            if not os.path.exists(filepath):
                messagebox.showerror("Error", f"File not found:\n{filepath}")
                return
            
            # Play in separate thread
            threading.Thread(target=_play_audio_thread, 
                           args=(filepath, "test", "test", "test"), 
                           daemon=True).start()
            messagebox.showinfo("Playing", f"Testing: {os.path.basename(filepath)}")
            
        except Exception as e:
            logger.error(f"Error testing audio: {e}")
            messagebox.showerror("Error", f"Failed to test audio:\n{str(e)}")
    
    def test_all_sounds(self):
        """Test all configured sounds in sequence"""
        try:
            gap_file = self.gap_sound_var.get()
            spike_file = self.spike_sound_var.get()
            delay_file = self.delay_sound_var.get()
            
            missing_files = []
            for audio_type, filepath in [('Gap', gap_file), ('Spike', spike_file), ('Delay', delay_file)]:
                if not os.path.exists(filepath):
                    missing_files.append(f"  ❌ {audio_type}: {filepath}")
            
            if missing_files:
                messagebox.showerror("Error", "Some audio files not found:\n" + "\n".join(missing_files))
                return
            
            messagebox.showinfo("Testing", "Playing all sounds in sequence...\nGap → Spike → Delay")
            
            # Play with delays between each
            def play_all():
                for audio_type, filepath in [('Gap', gap_file), ('Spike', spike_file), ('Delay', delay_file)]:
                    time.sleep(0.5)
                    _play_audio_thread(filepath, audio_type.lower(), "test", "test")
                    time.sleep(1.5)  # Wait for sound to finish
            
            threading.Thread(target=play_all, daemon=True).start()
            
        except Exception as e:
            logger.error(f"Error testing all sounds: {e}")
            messagebox.showerror("Error", f"Failed to test sounds:\n{str(e)}")
    
    def save_audio_settings_ui(self):
        """Save audio settings to file"""
        global audio_settings
        try:
            audio_settings['enabled'] = self.audio_enabled_var.get()
            audio_settings['gap_sound'] = self.gap_sound_var.get()
            audio_settings['spike_sound'] = self.spike_sound_var.get()
            audio_settings['delay_sound'] = self.delay_sound_var.get()
            
            save_audio_settings()
            
            status = "BẬT" if audio_settings['enabled'] else "TẮT"
            messagebox.showinfo("Success", 
                              f"✅ Đã lưu Audio Settings!\n\n"
                              f"Trạng thái: {status}\n"
                              f"Gap: {os.path.basename(audio_settings['gap_sound'])}\n"
                              f"Spike: {os.path.basename(audio_settings['spike_sound'])}\n"
                              f"Delay: {os.path.basename(audio_settings['delay_sound'])}")
            
            self.main_app.log(f"🔊 Saved audio settings: enabled={status}")
            logger.info(f"Audio settings saved")
            
        except Exception as e:
            logger.error(f"Error saving audio settings: {e}")
            messagebox.showerror("Error", f"Failed to save audio settings:\n{str(e)}")
    
    def reset_audio_defaults(self):
        """Reset audio settings to defaults"""
        try:
            confirm = messagebox.askyesno("Confirm", 
                                         "Reset audio settings to defaults?\n\n"
                                         "Gap: sounds/Gap.mp3\n"
                                         "Spike: sounds/Spike.mp3\n"
                                         "Delay: sounds/Delay.mp3")
            if confirm:
                self.gap_sound_var.set('sounds/Gap.mp3')
                self.spike_sound_var.set('sounds/Spike.mp3')
                self.delay_sound_var.set('sounds/Delay.mp3')
                self.audio_enabled_var.set(True)
                
                self.save_audio_settings_ui()
        except Exception as e:
            logger.error(f"Error resetting audio defaults: {e}")
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("⚙️ Cài đặt - Gap, Spike & Delay")
        self.window.geometry("800x600")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Notebook for tabs
        self.notebook = ttk.Notebook(self.window)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Tab 1: Delay Settings
        self.create_delay_settings_tab()
        
        # Tab 2: Gap/Spike Settings
        self.create_gap_spike_settings_tab()

        # Tab 3: Symbol Filter
        self.create_symbol_filter_tab()
        
        # Tab 4: Screenshot Settings
        self.create_screenshot_settings_tab()
        
        # Tab 5: Manual Hidden List
        self.create_hidden_list_tab()
        
        # Tab 6: Tools
        self.create_tools_tab()
        
        # Tab 7: Auto-Send Google Sheets
        self.create_auto_send_tab()
        
        # Tab 8: Audio Alerts (NEW)
        self.create_audio_settings_tab()
    
    def create_delay_settings_tab(self):
        """Create Delay Settings tab"""
        delay_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(delay_frame, text="⏱️ Cài đặt Delay")

        # Title
        ttk.Label(delay_frame, text="Cài đặt phát hiện Delay",
                 font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=5)

        # Delay Threshold
        threshold_frame = ttk.LabelFrame(delay_frame, text="Ngưỡng Delay", padding="10")
        threshold_frame.pack(fill=tk.X, pady=10)

        ttk.Label(threshold_frame, text="Ngưỡng delay (giây):").pack(side=tk.LEFT, padx=5)
        self.delay_threshold_var = tk.IntVar(value=delay_settings['threshold'])
        ttk.Spinbox(threshold_frame, from_=30, to=600, textvariable=self.delay_threshold_var,
                   width=10).pack(side=tk.LEFT, padx=5)
        ttk.Label(threshold_frame, text="(30-600s)", foreground='gray').pack(side=tk.LEFT, padx=5)

        # Info
        info_text = "Symbols không update giá trên ngưỡng sẽ hiển thị trong bảng Delay"
        ttk.Label(threshold_frame, text=info_text, foreground='blue').pack(side=tk.LEFT, padx=20)

        # Auto Hide Time
        auto_hide_frame = ttk.LabelFrame(delay_frame, text="Thời gian tự động ẩn", padding="10")
        auto_hide_frame.pack(fill=tk.X, pady=10)

        ttk.Label(auto_hide_frame, text="Tự động ẩn sau (giây):").pack(side=tk.LEFT, padx=5)
        self.auto_hide_time_var = tk.IntVar(value=delay_settings.get('auto_hide_time', 3600))
        ttk.Spinbox(auto_hide_frame, from_=600, to=7200, textvariable=self.auto_hide_time_var,
                   width=10, increment=300).pack(side=tk.LEFT, padx=5)
        ttk.Label(auto_hide_frame, text="(10-120 phút)", foreground='gray').pack(side=tk.LEFT, padx=5)

        # Info
        info_text2 = "Symbols delay quá lâu sẽ tự động ẩn khỏi bảng Delay"
        ttk.Label(auto_hide_frame, text=info_text2, foreground='blue').pack(side=tk.LEFT, padx=20)

        # Save button
        ttk.Button(delay_frame, text="💾 Lưu cài đặt Delay",
                  command=self.save_delay_settings).pack(pady=20)
    
    def create_gap_spike_settings_tab(self):
        """Create Gap/Spike Settings tab with visual editor"""
        gs_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(gs_frame, text="📊 Cài đặt Gap/Spike")

        # Top controls
        top_frame = ttk.Frame(gs_frame)
        top_frame.pack(fill=tk.X, pady=5)

        ttk.Label(top_frame, text="📊 Cấu hình ngưỡng Gap/Spike",
                 font=('Arial', 11, 'bold')).pack(side=tk.LEFT, padx=5)

        ttk.Button(top_frame, text="🔄 Làm mới Symbols",
                  command=self.refresh_gap_spike_list).pack(side=tk.RIGHT, padx=5)

        # Instructions
        inst_frame = ttk.LabelFrame(gs_frame, text="💡 Hướng dẫn", padding="5")
        inst_frame.pack(fill=tk.X, pady=5)
        
        instructions = """• Double-click cell để edit Gap/Spike threshold
• Broker_*: Apply cho TẤT CẢ symbols của broker (VD: XM_*:0.01)
• Symbol: Apply cho symbol từ TẤT CẢ brokers (VD: EURUSD:0.02)
• *: Default cho tất cả (VD: *:0.01)
• Để trống = sử dụng default"""
        
        ttk.Label(inst_frame, text=instructions, justify=tk.LEFT, foreground='blue',
                 font=('Arial', 9)).pack(anchor=tk.W)
        
        # Quick actions
        action_frame = ttk.LabelFrame(gs_frame, text="⚡ Thao tác nhanh - Cấu hình hàng loạt", padding="10")
        action_frame.pack(fill=tk.X, pady=5)

        # Threshold inputs
        threshold_row = ttk.Frame(action_frame)
        threshold_row.pack(fill=tk.X, pady=5)

        ttk.Label(threshold_row, text="Ngưỡng Gap:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.quick_gap_var = tk.StringVar(value="0.01")
        ttk.Entry(threshold_row, textvariable=self.quick_gap_var, width=10).pack(side=tk.LEFT, padx=2)
        ttk.Label(threshold_row, text="%", foreground='blue').pack(side=tk.LEFT, padx=2)

        ttk.Label(threshold_row, text="  Ngưỡng Spike:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=(20, 5))
        self.quick_spike_var = tk.StringVar(value="0.02")
        ttk.Entry(threshold_row, textvariable=self.quick_spike_var, width=10).pack(side=tk.LEFT, padx=2)
        ttk.Label(threshold_row, text="%", foreground='blue').pack(side=tk.LEFT, padx=2)
        
        # Separator
        ttk.Separator(action_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        
        # Option 1: Apply to ALL brokers
        option1_row = ttk.Frame(action_frame)
        option1_row.pack(fill=tk.X, pady=3)

        ttk.Label(option1_row, text="🌐 Tùy chọn 1:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        ttk.Button(option1_row, text="Áp dụng cho TẤT CẢ Symbols từ TẤT CẢ Brokers",
                  command=self.apply_to_all, width=40).pack(side=tk.LEFT, padx=5)
        ttk.Label(option1_row, text="(Tất cả sản phẩm tất cả sàn)",
                 foreground='gray', font=('Arial', 8)).pack(side=tk.LEFT, padx=5)

        # Option 2: Apply to ONE broker
        option2_row = ttk.Frame(action_frame)
        option2_row.pack(fill=tk.X, pady=3)

        ttk.Label(option2_row, text="🏢 Tùy chọn 2:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        ttk.Label(option2_row, text="Chọn Broker:").pack(side=tk.LEFT, padx=5)

        self.broker_selector_var = tk.StringVar()
        self.broker_selector = ttk.Combobox(option2_row, textvariable=self.broker_selector_var,
                                            width=15, state='readonly')
        self.broker_selector.pack(side=tk.LEFT, padx=5)

        ttk.Button(option2_row, text="Áp dụng cho TẤT CẢ Symbols từ Broker này",
                  command=self.apply_to_selected_broker_from_dropdown, width=40).pack(side=tk.LEFT, padx=5)
        ttk.Label(option2_row, text="(Tất cả sản phẩm của sàn này)",
                 foreground='gray', font=('Arial', 8)).pack(side=tk.LEFT, padx=5)
        
        # Filter by broker
        filter_frame = ttk.Frame(gs_frame)
        filter_frame.pack(fill=tk.X, pady=5)

        ttk.Label(filter_frame, text="🔍 Lọc theo Broker:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        self.broker_filter_var = tk.StringVar(value="All Brokers")
        self.broker_filter = ttk.Combobox(filter_frame, textvariable=self.broker_filter_var,
                                          width=20, state='readonly')
        self.broker_filter.pack(side=tk.LEFT, padx=5)
        self.broker_filter.bind('<<ComboboxSelected>>', lambda e: self.filter_symbols_by_broker())

        ttk.Label(filter_frame, text="(Lọc hiển thị symbols theo sàn)",
                 foreground='gray', font=('Arial', 8)).pack(side=tk.LEFT, padx=5)

        # Treeview for symbols
        tree_frame = ttk.LabelFrame(gs_frame, text="📋 Symbols từ Market Watch", padding="5")
        tree_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Create treeview
        columns = ('Broker', 'Symbol', 'Gap %', 'Spike %', 'Status')
        self.gs_tree = ttk.Treeview(tree_frame, columns=columns, show='headings', height=15)

        self.gs_tree.heading('Broker', text='Broker')
        self.gs_tree.heading('Symbol', text='Symbol')
        self.gs_tree.heading('Gap %', text='Ngưỡng Gap (%)')
        self.gs_tree.heading('Spike %', text='Ngưỡng Spike (%)')
        self.gs_tree.heading('Status', text='Nguồn')
        
        self.gs_tree.column('Broker', width=120)
        self.gs_tree.column('Symbol', width=100)
        self.gs_tree.column('Gap %', width=120)
        self.gs_tree.column('Spike %', width=120)
        self.gs_tree.column('Status', width=200)
        
        # Scrollbars
        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.gs_tree.yview)
        hsb = ttk.Scrollbar(tree_frame, orient="horizontal", command=self.gs_tree.xview)
        self.gs_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        self.gs_tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        hsb.grid(row=1, column=0, sticky='ew')
        
        tree_frame.grid_rowconfigure(0, weight=1)
        tree_frame.grid_columnconfigure(0, weight=1)
        
        # Bind double-click for edit
        self.gs_tree.bind('<Double-Button-1>', self.edit_threshold)
        
        # Bottom buttons
        bottom_frame = ttk.Frame(gs_frame)
        bottom_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(bottom_frame, text="💾 Save All Settings", 
                  command=self.save_gap_spike_from_tree).pack(side=tk.LEFT, padx=5)
        ttk.Button(bottom_frame, text="🗑️ Clear Selected", 
                  command=self.clear_selected_thresholds).pack(side=tk.LEFT, padx=5)
        ttk.Button(bottom_frame, text="📄 Export to Text", 
                  command=self.export_to_text_mode).pack(side=tk.LEFT, padx=5)
        
        # Initial load
        self.refresh_gap_spike_list()
    
    def create_symbol_filter_tab(self):
        """Create Symbol Filter tab to choose which symbols are processed"""
        symbol_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(symbol_frame, text="🎯 Lọc Symbol")

        ttk.Label(
            symbol_frame,
            text="Lọc Symbol để phát hiện Gap/Spike",
            font=('Arial', 12, 'bold')
        ).pack(anchor=tk.W, pady=(0, 5))

        info_text = (
            "⚙️ Tùy chọn này cho phép chọn sản phẩm nào sẽ được tính Gap/Spike.\n"
            "• Khi bật, chỉ các symbols được chọn mới xuất hiện trong bảng Gap/Spike.\n"
            "• Lọc theo sàn và nhóm sản phẩm để chọn nhanh từng cụm.\n"
            "• Double-click vào dòng để bật/tắt symbol.\n"
            "• Nhấn Save để áp dụng (Python sẽ tự động dùng lựa chọn mới cho tick tiếp theo)."
        )
        ttk.Label(symbol_frame, text=info_text, justify=tk.LEFT, foreground='blue', font=('Arial', 9)).pack(anchor=tk.W, pady=(0, 10))

        # Local copy of selection
        self.symbol_filter_selection = {
            broker: set(symbols or [])
            for broker, symbols in symbol_filter_settings.get('selection', {}).items()
        }

        # Enable checkbox
        self.symbol_filter_enabled_var = tk.BooleanVar(value=symbol_filter_settings.get('enabled', False))
        ttk.Checkbutton(
            symbol_frame,
            text="🔒 Chỉ xét Gap/Spike cho symbols được chọn",
            variable=self.symbol_filter_enabled_var
        ).pack(anchor=tk.W, pady=(0, 10))

        # Controls
        control_frame = ttk.Frame(symbol_frame)
        control_frame.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(control_frame, text="🔍 Broker:").pack(side=tk.LEFT, padx=(0, 5))
        self.symbol_filter_broker_var = tk.StringVar(value="All Brokers")
        self.symbol_filter_broker_combo = ttk.Combobox(
            control_frame,
            textvariable=self.symbol_filter_broker_var,
            width=20,
            state='readonly'
        )
        self.symbol_filter_broker_combo.pack(side=tk.LEFT, padx=(0, 10))
        self.symbol_filter_broker_combo.bind('<<ComboboxSelected>>', lambda e: self.refresh_symbol_filter_tree())

        ttk.Label(control_frame, text="| Nhóm:").pack(side=tk.LEFT, padx=(0, 5))
        self.symbol_filter_group_var = tk.StringVar(value="All Groups")
        self.symbol_filter_group_combo = ttk.Combobox(
            control_frame,
            textvariable=self.symbol_filter_group_var,
            width=18,
            state='readonly'
        )
        self.symbol_filter_group_combo.pack(side=tk.LEFT, padx=(0, 10))
        self.symbol_filter_group_combo.bind('<<ComboboxSelected>>', lambda e: self.refresh_symbol_filter_tree())

        ttk.Button(
            control_frame,
            text="Chọn tất cả (Hiển thị)",
            command=self.select_all_visible_symbols
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            control_frame,
            text="Xóa bỏ hiển thị",
            command=self.clear_visible_symbols
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            control_frame,
            text="💾 Lưu",
            command=self.save_symbol_filter_settings_ui
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            control_frame,
            text="Làm mới",
            command=self.refresh_symbol_filter_tree
        ).pack(side=tk.RIGHT, padx=5)

        # Treeview
        tree_frame = ttk.LabelFrame(symbol_frame, text="Danh sách Symbols", padding="5")
        tree_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        columns = ('Selected', 'Broker', 'Symbol', 'Group', 'Status')
        self.symbol_filter_tree = ttk.Treeview(
            tree_frame,
            columns=columns,
            show='headings',
            height=18,
            selectmode='browse'
        )

        self.symbol_filter_tree.heading('Selected', text='Chọn')
        self.symbol_filter_tree.heading('Broker', text='Broker')
        self.symbol_filter_tree.heading('Symbol', text='Symbol')
        self.symbol_filter_tree.heading('Group', text='Nhóm')
        self.symbol_filter_tree.heading('Status', text='Trạng thái')

        self.symbol_filter_tree.column('Selected', width=60, anchor=tk.CENTER)
        self.symbol_filter_tree.column('Broker', width=160)
        self.symbol_filter_tree.column('Symbol', width=120)
        self.symbol_filter_tree.column('Group', width=100)
        self.symbol_filter_tree.column('Status', width=120)

        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.symbol_filter_tree.yview)
        hsb = ttk.Scrollbar(tree_frame, orient="horizontal", command=self.symbol_filter_tree.xview)
        self.symbol_filter_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.symbol_filter_tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        hsb.grid(row=1, column=0, sticky='ew')

        tree_frame.grid_rowconfigure(0, weight=1)
        tree_frame.grid_columnconfigure(0, weight=1)

        self.symbol_filter_tree.bind('<Double-Button-1>', self.toggle_symbol_filter_selection)

        # Bottom actions
        bottom_frame = ttk.Frame(symbol_frame)
        bottom_frame.pack(fill=tk.X, pady=10)

        ttk.Button(
            bottom_frame,
            text="💾 Lưu lọc Symbol",
            command=self.save_symbol_filter_settings_ui
        ).pack(side=tk.LEFT, padx=5)

        ttk.Label(
            bottom_frame,
            text="Double-click để bật/tắt symbol",
            foreground='gray',
            font=('Arial', 8)
        ).pack(side=tk.RIGHT, padx=5)

        # Populate initial data
        self.refresh_symbol_filter_tree()

    def refresh_symbol_filter_tree(self):
        """Refresh symbol filter tree with current market data"""
        try:
            # Clear current rows
            for item in self.symbol_filter_tree.get_children():
                self.symbol_filter_tree.delete(item)

            with data_lock:
                market_snapshot = {
                    broker: {symbol: data for symbol, data in symbols_dict.items()}
                    for broker, symbols_dict in market_data.items()
                }

            selection = self.symbol_filter_selection

            broker_names = sorted(set(market_snapshot.keys()) | set(selection.keys()))
            combo_values = ["All Brokers"] + broker_names if broker_names else ["All Brokers"]
            self.symbol_filter_broker_combo['values'] = combo_values

            if self.symbol_filter_broker_var.get() not in combo_values:
                self.symbol_filter_broker_var.set("All Brokers")

            current_filter = self.symbol_filter_broker_var.get()
            current_group = self.symbol_filter_group_var.get()
            available_groups = set()
            total_rows = 0

            for broker in broker_names:
                if current_filter != "All Brokers" and broker != current_filter:
                    continue

                broker_data = market_snapshot.get(broker, {})
                live_symbols = set(broker_data.keys())
                selected_symbols = selection.get(broker, set())
                combined_symbols = sorted(live_symbols | selected_symbols)

                visible_count = 0
                for symbol in combined_symbols:
                    group_path = ''
                    symbol_info = broker_data.get(symbol)
                    if isinstance(symbol_info, dict):
                        group_path = symbol_info.get('group', '') or ''

                    group_name = classify_symbol_group(symbol, group_path)
                    available_groups.add(group_name)

                    if current_group != "All Groups" and group_name != current_group:
                        continue

                    status = "Live" if symbol in live_symbols else "No data"
                    selected_flag = "✅" if symbol in selected_symbols else "⬜"
                    self.symbol_filter_tree.insert(
                        '', 'end',
                        values=(selected_flag, broker, symbol, group_name, status)
                    )
                    total_rows += 1
                    visible_count += 1

                if not combined_symbols:
                    # Hiển thị dòng thông tin nếu broker không có symbol nào
                    self.symbol_filter_tree.insert(
                        '', 'end',
                        values=("ℹ️", broker, "-", "-", "Chưa có data"),
                        tags=('info',)
                    )
                    total_rows += 1
                elif visible_count == 0:
                    # Có symbol nhưng không thuộc nhóm được chọn
                    self.symbol_filter_tree.insert(
                        '', 'end',
                        values=("ℹ️", broker, "-", "-", f"Không có symbol thuộc nhóm {current_group}"),
                        tags=('info',)
                    )
                    total_rows += 1

            if total_rows == 0:
                self.symbol_filter_tree.insert(
                    '', 'end',
                    values=("ℹ️", "No symbols", "-", "-", "Chờ dữ liệu từ EA"),
                    tags=('info',)
                )

            group_values = ["All Groups"] + sorted(available_groups) if available_groups else ["All Groups"]
            self.symbol_filter_group_combo['values'] = group_values

            if self.symbol_filter_group_var.get() not in group_values:
                self.symbol_filter_group_var.set("All Groups")

        except Exception as e:
            logger.error(f"Error refreshing symbol filter tree: {e}")

    def toggle_symbol_filter_selection(self, event=None):
        """Toggle selection state when user double-clicks a row"""
        try:
            selected_items = self.symbol_filter_tree.selection()
            if not selected_items:
                return

            item = selected_items[0]
            values = self.symbol_filter_tree.item(item, 'values')
            if len(values) < 5:
                return

            broker = values[1]
            symbol = values[2]

            if symbol in ('-', '') or broker in ('No symbols', '') or values[0] == 'ℹ️':
                return

            current_set = self.symbol_filter_selection.setdefault(broker, set())

            if symbol in current_set:
                current_set.remove(symbol)
                self.symbol_filter_tree.set(item, 'Selected', '⬜')
            else:
                current_set.add(symbol)
                self.symbol_filter_tree.set(item, 'Selected', '✅')

        except Exception as e:
            logger.error(f"Error toggling symbol filter selection: {e}")

    def select_all_visible_symbols(self):
        """Select all symbols currently visible in the tree"""
        try:
            has_update = False
            for item in self.symbol_filter_tree.get_children():
                values = self.symbol_filter_tree.item(item, 'values')
                if len(values) < 5:
                    continue

                if values[0] == 'ℹ️':
                    continue

                broker = values[1]
                symbol = values[2]

                if symbol in ('-', '') or broker in ('No symbols', ''):
                    continue

                selection_set = self.symbol_filter_selection.setdefault(broker, set())
                if symbol not in selection_set:
                    selection_set.add(symbol)
                    has_update = True

            if has_update:
                self.refresh_symbol_filter_tree()
        except Exception as e:
            logger.error(f"Error selecting all visible symbols: {e}")

    def clear_visible_symbols(self):
        """Clear selection for currently visible brokers"""
        try:
            affected_brokers = set()

            for item in self.symbol_filter_tree.get_children():
                values = self.symbol_filter_tree.item(item, 'values')
                if len(values) < 5:
                    continue

                if values[0] == 'ℹ️':
                    continue

                broker = values[1]
                symbol = values[2]

                if symbol in ('-', '') or broker in ('No symbols', ''):
                    continue

                selection_set = self.symbol_filter_selection.setdefault(broker, set())
                if symbol in selection_set:
                    selection_set.discard(symbol)
                    affected_brokers.add(broker)

            if affected_brokers:
                self.refresh_symbol_filter_tree()
        except Exception as e:
            logger.error(f"Error clearing visible symbols: {e}")

    def save_symbol_filter_settings_ui(self):
        """Persist symbol filter selections to disk"""
        global symbol_filter_settings
        try:
            symbol_filter_settings['enabled'] = self.symbol_filter_enabled_var.get()

            payload = {}
            for broker, symbols in self.symbol_filter_selection.items():
                if symbols is None:
                    payload[broker] = []
                else:
                    payload[broker] = sorted(symbols)

            symbol_filter_settings['selection'] = payload
            save_symbol_filter_settings()

            cleanup_unselected_symbol_results()

            try:
                self.main_app.update_display()
                self.main_app.update_alert_board_display()
                self.main_app.update_delay_board_display()
            except Exception as refresh_err:
                logger.warning(f"Unable to refresh main UI after saving symbol filter: {refresh_err}")

            enabled_text = "BẬT" if symbol_filter_settings['enabled'] else "TẮT"
            messagebox.showinfo(
                "Symbol Filter",
                f"Đã lưu symbol filter!\n\n"
                f"Trạng thái: {enabled_text}\n"
                f"Số sàn cấu hình: {len(payload)}"
            )

            self.main_app.log(
                f"Symbol filter saved: enabled={symbol_filter_settings['enabled']}, brokers={len(payload)}"
            )

        except Exception as e:
            logger.error(f"Error saving symbol filter settings: {e}")
            messagebox.showerror("Error", f"Không thể lưu symbol filter: {e}")

    def create_screenshot_settings_tab(self):
        """Create Screenshot Settings tab"""
        screenshot_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(screenshot_frame, text="📸 Chụp màn hình")

        # Title
        ttk.Label(screenshot_frame, text="📸 Cài đặt tự động chụp màn hình",
                 font=('Arial', 12, 'bold')).pack(pady=10)

        # Enable/Disable
        enable_frame = ttk.LabelFrame(screenshot_frame, text="Bật tự động chụp màn hình", padding="10")
        enable_frame.pack(fill=tk.X, pady=5)

        self.screenshot_enabled_var = tk.BooleanVar(value=screenshot_settings['enabled'])
        ttk.Checkbutton(enable_frame, text="✅ Tự động chụp màn hình khi phát hiện Gap/Spike",
                       variable=self.screenshot_enabled_var).pack(anchor=tk.W, pady=5)

        # Type selection
        type_frame = ttk.LabelFrame(screenshot_frame, text="Loại chụp màn hình", padding="10")
        type_frame.pack(fill=tk.X, pady=5)

        self.screenshot_gap_var = tk.BooleanVar(value=screenshot_settings['save_gap'])
        ttk.Checkbutton(type_frame, text="📸 Chụp khi phát hiện Gap",
                       variable=self.screenshot_gap_var).pack(anchor=tk.W, pady=2)

        self.screenshot_spike_var = tk.BooleanVar(value=screenshot_settings['save_spike'])
        ttk.Checkbutton(type_frame, text="📸 Chụp khi phát hiện Spike",
                       variable=self.screenshot_spike_var).pack(anchor=tk.W, pady=2)

        # Folder settings
        folder_frame = ttk.LabelFrame(screenshot_frame, text="Lưu trữ", padding="10")
        folder_frame.pack(fill=tk.X, pady=5)

        ttk.Label(folder_frame, text="Thư mục:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.screenshot_folder_var = tk.StringVar(value=screenshot_settings['folder'])
        folder_entry = ttk.Entry(folder_frame, textvariable=self.screenshot_folder_var, width=30)
        folder_entry.grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)

        ttk.Button(folder_frame, text="📂 Mở thư mục",
                  command=self.open_screenshots_folder).grid(row=0, column=2, padx=5, pady=5)
        
        # Info
        info_frame = ttk.Frame(screenshot_frame)
        info_frame.pack(fill=tk.X, pady=10)
        
        info_text = (
            "ℹ️ Screenshots will be saved with filename format:\n"
            "   <broker>_<symbol>_<type>_<timestamp>.png\n\n"
            "Example: Exness_EURUSD_gap_20251015_143020.png\n\n"
            "• Type: gap, spike, or both\n"
            "• Timestamp: Thời gian server của sàn (marketwatch time)\n"
            "  KHÔNG bị convert sang GMT+7 local time của máy Python\n"
            "• Captured in separate thread (doesn't block detection)\n"
            "• View all screenshots in 📸 Pictures window"
        )
        
        ttk.Label(info_frame, text=info_text, foreground='blue', 
                 font=('Arial', 9)).pack(padx=10)
        
        # Save button
        ttk.Button(screenshot_frame, text="💾 Lưu cài đặt chụp màn hình",
                  command=self.save_screenshot_settings).pack(pady=20)
    
    def save_screenshot_settings(self):
        """Save screenshot settings"""
        global screenshot_settings
        try:
            screenshot_settings['enabled'] = self.screenshot_enabled_var.get()
            screenshot_settings['save_gap'] = self.screenshot_gap_var.get()
            screenshot_settings['save_spike'] = self.screenshot_spike_var.get()
            screenshot_settings['folder'] = self.screenshot_folder_var.get()
            
            save_screenshot_settings()
            ensure_pictures_folder()
            
            messagebox.showinfo("Success", 
                              f"Đã lưu screenshot settings:\n"
                              f"- Enabled: {screenshot_settings['enabled']}\n"
                              f"- Save Gap: {screenshot_settings['save_gap']}\n"
                              f"- Save Spike: {screenshot_settings['save_spike']}\n"
                              f"- Folder: {screenshot_settings['folder']}")
        except Exception as e:
            logger.error(f"Error saving screenshot settings: {e}")
            messagebox.showerror("Error", f"Failed to save: {str(e)}")
    
    def open_screenshots_folder(self):
        """Open screenshots folder"""
        try:
            folder = self.screenshot_folder_var.get()
            if not os.path.exists(folder):
                os.makedirs(folder)
            
            if os.name == 'nt':  # Windows
                os.startfile(folder)
            elif os.name == 'posix':
                import sys
                os.system(f'open "{folder}"' if sys.platform == 'darwin' else f'xdg-open "{folder}"')
        except Exception as e:
            logger.error(f"Error opening folder: {e}")
            messagebox.showerror("Error", f"Failed to open folder: {str(e)}")
    
    def create_hidden_list_tab(self):
        """Create Manual Hidden List tab"""
        hidden_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(hidden_frame, text="🔒 Danh sách ẩn")

        # Title
        ttk.Label(hidden_frame, text="Symbols đã ẩn thủ công",
                 font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=5)
        
        # Info
        info_text = "Danh sách symbols đã bị hide thủ công từ Delay board (Right-click → Hide)"
        ttk.Label(hidden_frame, text=info_text, foreground='blue').pack(anchor=tk.W, pady=5)
        
        # List frame
        list_frame = ttk.Frame(hidden_frame)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Treeview for hidden list
        columns = ('Broker', 'Symbol')
        self.hidden_tree = ttk.Treeview(list_frame, columns=columns, show='headings', height=15)
        
        self.hidden_tree.heading('Broker', text='Broker')
        self.hidden_tree.heading('Symbol', text='Symbol')
        
        self.hidden_tree.column('Broker', width=200)
        self.hidden_tree.column('Symbol', width=200)
        
        # Scrollbar
        vsb = ttk.Scrollbar(list_frame, orient="vertical", command=self.hidden_tree.yview)
        self.hidden_tree.configure(yscrollcommand=vsb.set)
        
        self.hidden_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Buttons
        btn_frame = ttk.Frame(hidden_frame)
        btn_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(btn_frame, text="🔓 Bỏ ẩn đã chọn",
                  command=self.unhide_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="🗑️ Xóa tất cả",
                  command=self.clear_all_hidden).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="🔄 Làm mới",
                  command=self.refresh_hidden_list).pack(side=tk.LEFT, padx=5)
        
        # Initial load
        self.refresh_hidden_list()
    
    def create_tools_tab(self):
        """Create Tools tab for Trading Hours & Raw Data"""
        tools_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tools_frame, text="🔧 Công cụ")

        # Title
        ttk.Label(tools_frame, text="Công cụ bổ sung",
                 font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=10)

        # Trading Hours section
        trading_hours_section = ttk.LabelFrame(tools_frame, text="📅 Giờ giao dịch", padding="20")
        trading_hours_section.pack(fill=tk.X, pady=10)

        ttk.Label(trading_hours_section,
                 text="Xem giờ trade của các symbols từ các sàn",
                 foreground='blue').pack(anchor=tk.W, pady=5)

        ttk.Button(trading_hours_section, text="📅 Mở giờ giao dịch",
                  command=self.main_app.open_trading_hours,
                  width=30).pack(anchor=tk.W, pady=5)

        # Raw Data section
        raw_data_section = ttk.LabelFrame(tools_frame, text="📊 Xem dữ liệu thô", padding="20")
        raw_data_section.pack(fill=tk.X, pady=10)

        ttk.Label(raw_data_section,
                 text="Xem raw data từ MT4/MT5 (giá bid/ask, OHLC, v.v.)",
                 foreground='blue').pack(anchor=tk.W, pady=5)

        ttk.Button(raw_data_section, text="📊 Mở xem dữ liệu thô",
                  command=self.main_app.open_raw_data_viewer,
                  width=30).pack(anchor=tk.W, pady=5)
        
        # Auto reset Python section
        python_reset_section = ttk.LabelFrame(tools_frame, text="🔁 Tự động khởi động lại Python", padding="20")
        python_reset_section.pack(fill=tk.X, pady=10)

        ttk.Label(
            python_reset_section,
            text="Tự động gọi khởi động lại Python định kỳ để làm mới kết nối.",
            foreground='blue'
        ).pack(anchor=tk.W, pady=5)

        self.python_reset_enabled_var = tk.BooleanVar(value=python_reset_settings.get('enabled', False))
        ttk.Checkbutton(
            python_reset_section,
            text="Bật tự động khởi động lại Python",
            variable=self.python_reset_enabled_var
        ).pack(anchor=tk.W, pady=2)

        interval_frame = ttk.Frame(python_reset_section)
        interval_frame.pack(fill=tk.X, pady=5)

        ttk.Label(interval_frame, text="Khoảng thời gian (phút):").pack(side=tk.LEFT, padx=5)
        self.python_reset_interval_var = tk.IntVar(value=python_reset_settings.get('interval_minutes', 30))
        ttk.Spinbox(
            interval_frame,
            from_=1,
            to=720,
            textvariable=self.python_reset_interval_var,
            width=6
        ).pack(side=tk.LEFT, padx=5)
        ttk.Label(
            interval_frame,
            text="(mặc định 30 phút)",
            foreground='gray',
            font=('Arial', 8)
        ).pack(side=tk.LEFT, padx=5)

        ttk.Button(
            python_reset_section,
            text="💾 Lưu cài đặt tự động khởi động lại",
            command=self.save_python_reset_settings_ui
        ).pack(anchor=tk.W, pady=10)
    
    def create_auto_send_tab(self):
        """Create Auto-Send Google Sheets Settings tab"""
        auto_send_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(auto_send_frame, text="📤 Tự động gửi Sheets")

        # Title
        ttk.Label(auto_send_frame, text="Cấu hình Google Sheets cho Thư viện ảnh",
                 font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=5)
        
        # Info
        info_text = "📸 Gửi dữ liệu lên Google Sheet khi click 'Hoàn thành' trong Picture Gallery"
        ttk.Label(auto_send_frame, text=info_text, foreground='blue').pack(anchor=tk.W, pady=5)
        
        info_text2 = "⚠️ Cấu hình Sheet URL, Sheet Name, và Columns trước khi sử dụng"
        ttk.Label(auto_send_frame, text=info_text2, foreground='orange').pack(anchor=tk.W, pady=2)
        
        # Google Sheet URL
        url_frame = ttk.LabelFrame(auto_send_frame, text="📊 Cấu hình Google Sheet", padding="10")
        url_frame.pack(fill=tk.X, pady=10)

        ttk.Label(url_frame, text="URL Sheet:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.sheet_url_var = tk.StringVar(value=auto_send_settings['sheet_url'])
        ttk.Entry(url_frame, textvariable=self.sheet_url_var, width=60).grid(row=0, column=1, padx=5, pady=5)

        ttk.Label(url_frame, text="Tên Sheet (tab):").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        self.sheet_name_var = tk.StringVar(value=auto_send_settings['sheet_name'])
        ttk.Entry(url_frame, textvariable=self.sheet_name_var, width=30).grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)

        ttk.Label(url_frame, text="Cột bắt đầu:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        self.start_column_var = tk.StringVar(value=auto_send_settings['start_column'])
        ttk.Entry(url_frame, textvariable=self.start_column_var, width=5).grid(row=2, column=1, sticky=tk.W, padx=5, pady=5)
        ttk.Label(url_frame, text="(VD: A, B, C, ...)", foreground='gray', font=('Arial', 8)).grid(row=2, column=1, padx=(50, 0), sticky=tk.W)

        # Column mapping
        columns_frame = ttk.LabelFrame(auto_send_frame, text="📋 Cột cần gửi", padding="10")
        columns_frame.pack(fill=tk.X, pady=10)

        ttk.Label(columns_frame, text="Chọn thông tin muốn gửi lên Sheet:", foreground='blue').pack(anchor=tk.W, pady=5)
        
        columns_config = auto_send_settings.get('columns', {})

        self.col_assignee_var = tk.BooleanVar(value=columns_config.get('assignee', True))
        ttk.Checkbutton(columns_frame, text="👤 Người lọc (Tên)", variable=self.col_assignee_var).pack(anchor=tk.W, padx=20)

        self.col_time_var = tk.BooleanVar(value=columns_config.get('time', True))
        ttk.Checkbutton(columns_frame, text="⏰ Time (Thời gian chụp)", variable=self.col_time_var).pack(anchor=tk.W, padx=20)
        
        self.col_broker_var = tk.BooleanVar(value=columns_config.get('broker', True))
        ttk.Checkbutton(columns_frame, text="🏦 Broker (Sàn)", variable=self.col_broker_var).pack(anchor=tk.W, padx=20)
        
        self.col_symbol_var = tk.BooleanVar(value=columns_config.get('symbol', True))
        ttk.Checkbutton(columns_frame, text="💱 Symbol (Sản phẩm)", variable=self.col_symbol_var).pack(anchor=tk.W, padx=20)
        
        self.col_type_var = tk.BooleanVar(value=columns_config.get('type', True))
        ttk.Checkbutton(columns_frame, text="📊 Type (Gap/Spike/Both)", variable=self.col_type_var).pack(anchor=tk.W, padx=20)
        
        self.col_percentage_var = tk.BooleanVar(value=columns_config.get('percentage', True))
        ttk.Checkbutton(columns_frame, text="📐 Percentage (Gap/Spike %)", variable=self.col_percentage_var).pack(anchor=tk.W, padx=20)
        
        # Actions
        action_frame = ttk.Frame(auto_send_frame)
        action_frame.pack(fill=tk.X, pady=10)

        ttk.Button(action_frame, text="🧪 Kiểm tra kết nối",
                  command=self.test_google_sheet_connection).pack(side=tk.LEFT, padx=5)

        ttk.Button(action_frame, text="💾 Lưu cài đặt tự động gửi",
                  command=self.save_auto_send_settings_ui).pack(side=tk.LEFT, padx=5)

    def save_auto_send_settings_ui(self):
        """Validate input fields and persist Google Sheets auto-send settings"""
        global auto_send_settings
        try:
            import re

            sheet_url = self.sheet_url_var.get().strip()
            sheet_name = self.sheet_name_var.get().strip()
            start_column = self.start_column_var.get().strip().upper() or 'A'

            if not sheet_url:
                messagebox.showwarning("Warning",
                                       "⚠️ Vui lòng nhập Sheet URL trước khi lưu!")
                return

            if not re.search(r'/spreadsheets/d/([a-zA-Z0-9-_]+)', sheet_url):
                messagebox.showwarning(
                    "Warning",
                    "⚠️ Sheet URL không hợp lệ!\n\nURL phải có dạng: https://docs.google.com/spreadsheets/d/YOUR_SHEET_ID/..."
                )
                return

            if not re.fullmatch(r'[A-Z]+', start_column):
                messagebox.showwarning(
                    "Warning",
                    "⚠️ Start Column chỉ được chứa chữ cái (ví dụ: A, B, AA)"
                )
                return

            auto_send_settings['enabled'] = True  # Enable once configured
            auto_send_settings['sheet_url'] = sheet_url
            auto_send_settings['sheet_name'] = sheet_name
            auto_send_settings['start_column'] = start_column

            columns_config = auto_send_settings.setdefault('columns', {})
            columns_config['assignee'] = self.col_assignee_var.get()
            columns_config['time'] = self.col_time_var.get()
            columns_config['broker'] = self.col_broker_var.get()
            columns_config['symbol'] = self.col_symbol_var.get()
            columns_config['type'] = self.col_type_var.get()
            columns_config['percentage'] = self.col_percentage_var.get()

            save_auto_send_settings()

            sheet_url_display = sheet_url
            if len(sheet_url_display) > 50:
                sheet_url_display = sheet_url_display[:50] + "..."

            messagebox.showinfo(
                "Success",
                f"✅ Đã lưu Google Sheets settings!\n\n"
                f"- Sheet URL: {sheet_url_display}\n"
                f"- Sheet Name: {sheet_name or '(default)'}\n\n"
                "Khi click 'Hoàn thành' trong Picture Gallery,\n"
                "dữ liệu sẽ được gửi lên sheet này."
            )

            try:
                self.main_app.log("💾 Đã lưu cấu hình Auto-Send Google Sheets")
            except Exception:
                pass

        except Exception as e:
            logger.error(f"Error saving auto-send settings: {e}")
            messagebox.showerror("Error", f"Lỗi khi lưu settings:\n{str(e)}")
    
    def save_python_reset_settings_ui(self):
        """Persist auto reset Python settings"""
        global python_reset_settings
        try:
            interval = int(self.python_reset_interval_var.get() or 30)
            if interval <= 0:
                interval = 30
            python_reset_settings['enabled'] = self.python_reset_enabled_var.get()
            python_reset_settings['interval_minutes'] = interval
            save_python_reset_settings()
            self.main_app.update_python_reset_schedule()
            
            status = "BẬT" if python_reset_settings['enabled'] else "TẮT"
            messagebox.showinfo(
                "Auto Reset Python",
                f"Đã lưu Auto Reset Python!\n\nTrạng thái: {status}\nChu kỳ: {interval} phút"
            )
        except Exception as e:
            logger.error(f"Error saving Python reset settings: {e}")
            messagebox.showerror("Lỗi", f"Không thể lưu Auto Reset Python: {e}")
    
    def test_google_sheet_connection(self):
        """Test connection to Google Sheet"""
        try:
            # Check if credentials exist
            if not os.path.exists(CREDENTIALS_FILE):
                messagebox.showerror("Error", 
                                   f"❌ Không tìm thấy file credentials.json!\n\n"
                                   f"Vui lòng đặt file {CREDENTIALS_FILE} vào thư mục chương trình.")
                return
            
            # Check if URL is filled
            sheet_url = self.sheet_url_var.get().strip()
            if not sheet_url:
                messagebox.showwarning("Warning", 
                                     "⚠️ Vui lòng điền Sheet URL trước khi test!")
                return
            
            # Try to authenticate
            messagebox.showinfo("Testing", "⏳ Đang test connection...\n\nVui lòng đợi...")
            
            # Run test in thread to avoid blocking UI
            threading.Thread(target=self._test_connection_thread, args=(sheet_url,), daemon=True).start()
            
        except Exception as e:
            logger.error(f"Error testing connection: {e}")
            messagebox.showerror("Error", f"Lỗi khi test connection:\n{str(e)}")
    
    def _test_connection_thread(self, sheet_url):
        """Test connection in background thread"""
        try:
            from google.oauth2 import service_account
            
            # Authenticate
            creds = service_account.Credentials.from_service_account_file(
                CREDENTIALS_FILE,
                scopes=['https://www.googleapis.com/auth/spreadsheets',
                       'https://www.googleapis.com/auth/drive']
            )
            client = gspread.authorize(creds)
            
            # Extract sheet ID from URL
            import re
            match = re.search(r'/spreadsheets/d/([a-zA-Z0-9-_]+)', sheet_url)
            if match:
                sheet_id = match.group(1)
                spreadsheet = client.open_by_key(sheet_id)
                
                self.window.after(0, lambda: messagebox.showinfo("Success", 
                                    f"✅ Kết nối thành công!\n\n"
                                    f"Sheet: {spreadsheet.title}\n"
                                    f"Worksheets: {len(spreadsheet.worksheets())}"))
            else:
                self.window.after(0, lambda: messagebox.showerror("Error", 
                                    "❌ URL không hợp lệ!\n\n"
                                    "URL phải có dạng:\n"
                                    "https://docs.google.com/spreadsheets/d/YOUR_SHEET_ID/..."))
                
        except Exception as e:
            logger.error(f"Connection test failed: {e}")
            self.window.after(0, lambda: messagebox.showerror("Error", 
                                f"❌ Kết nối thất bại!\n\n{str(e)}"))
    
    def save_delay_settings(self):
        """Save delay settings"""
        global delay_settings
        try:
            delay_settings['threshold'] = self.delay_threshold_var.get()
            delay_settings['auto_hide_time'] = self.auto_hide_time_var.get()
            
            save_delay_settings()
            
            # Update main app
            self.main_app.delay_threshold.set(delay_settings['threshold'])
            
            messagebox.showinfo("Success", 
                              f"Đã lưu delay settings:\n"
                              f"- Threshold: {delay_settings['threshold']}s\n"
                              f"- Auto hide: {delay_settings['auto_hide_time']}s")
            
            self.main_app.log(f"⚙️ Updated delay settings: threshold={delay_settings['threshold']}s")
            logger.info(f"Delay settings saved: {delay_settings}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Lỗi lưu delay settings: {str(e)}")
    
    def save_gap(self):
        """Save gap settings"""
        global gap_settings
        try:
            content = self.gap_text.get('1.0', tk.END).strip()
            new_settings = {}
            
            for line in content.split('\n'):
                line = line.strip()
                if not line or ':' not in line:
                    continue
                symbol, threshold = line.split(':', 1)
                new_settings[symbol.strip().upper()] = float(threshold.strip())
            
            gap_settings = new_settings
            save_gap_settings()
            
            messagebox.showinfo("Success", f"Đã lưu {len(gap_settings)} gap settings")
            self.main_app.log(f"Updated gap settings: {len(gap_settings)} symbols")
            
        except Exception as e:
            messagebox.showerror("Error", f"Lỗi lưu gap settings: {str(e)}")
    
    def save_spike(self):
        """Save spike settings (legacy text mode)"""
        global spike_settings
        try:
            content = self.spike_text.get('1.0', tk.END).strip()
            new_settings = {}
            
            for line in content.split('\n'):
                line = line.strip()
                if not line or ':' not in line:
                    continue
                symbol, threshold = line.split(':', 1)
                new_settings[symbol.strip().upper()] = float(threshold.strip())
            
            spike_settings = new_settings
            save_spike_settings()
            
            messagebox.showinfo("Success", f"Đã lưu {len(spike_settings)} spike settings")
            self.main_app.log(f"Updated spike settings: {len(spike_settings)} symbols")
            
        except Exception as e:
            messagebox.showerror("Error", f"Lỗi lưu spike settings: {str(e)}")
    
    def refresh_gap_spike_list(self):
        """Refresh Gap/Spike settings list from market data"""
        try:
            # Clear existing items
            for item in self.gs_tree.get_children():
                self.gs_tree.delete(item)
            
            # Get all unique broker_symbol from market_data
            symbols_set = set()
            brokers_set = set()
            
            with data_lock:
                for broker, symbols_dict in market_data.items():
                    brokers_set.add(broker)
                    for symbol in symbols_dict.keys():
                        symbols_set.add((broker, symbol))
            
            # Update broker selector dropdown
            broker_list = sorted(list(brokers_set))
            self.broker_selector['values'] = broker_list
            if broker_list and not self.broker_selector_var.get():
                self.broker_selector_var.set(broker_list[0])
            
            # Update broker filter dropdown
            filter_list = ["All Brokers"] + broker_list
            self.broker_filter['values'] = filter_list
            if not self.broker_filter_var.get() or self.broker_filter_var.get() not in filter_list:
                self.broker_filter_var.set("All Brokers")
            
            # Get current filter
            current_filter = self.broker_filter_var.get()
            
            # Sort by broker, then symbol
            sorted_symbols = sorted(symbols_set, key=lambda x: (x[0], x[1]))
            
            # Add each symbol to tree (with filter)
            for broker, symbol in sorted_symbols:
                # Apply filter
                if current_filter != "All Brokers" and broker != current_filter:
                    continue
                
                key = f"{broker}_{symbol}"
                
                # Get current thresholds
                gap_threshold = self.get_threshold_for_display(broker, symbol, 'gap')
                spike_threshold = self.get_threshold_for_display(broker, symbol, 'spike')
                
                # Determine source
                gap_source = self.get_threshold_source(broker, symbol, 'gap')
                spike_source = self.get_threshold_source(broker, symbol, 'spike')
                
                # Display
                gap_display = f"{gap_threshold:.3f}" if gap_threshold else ""
                spike_display = f"{spike_threshold:.3f}" if spike_threshold else ""
                source_display = f"Gap: {gap_source} | Spike: {spike_source}"
                
                self.gs_tree.insert('', 'end', values=(
                    broker,
                    symbol,
                    gap_display,
                    spike_display,
                    source_display
                ), tags=(key,))
            
            logger.info(f"Refreshed Gap/Spike list: {len(sorted_symbols)} symbols, {len(broker_list)} brokers, filter={current_filter}")
            
        except Exception as e:
            logger.error(f"Error refreshing Gap/Spike list: {e}")
            messagebox.showerror("Error", f"Lỗi refresh list: {str(e)}")
    
    def filter_symbols_by_broker(self):
        """Filter symbols display by selected broker"""
        try:
            self.refresh_gap_spike_list()
            filter_value = self.broker_filter_var.get()
            logger.info(f"Filtered symbols by broker: {filter_value}")
        except Exception as e:
            logger.error(f"Error filtering symbols: {e}")
    
    def get_threshold_for_display(self, broker, symbol, threshold_type):
        """Get threshold for display (check broker_symbol, symbol, *, default)"""
        settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
        key = f"{broker}_{symbol}"
        
        # Priority: Broker_Symbol > Broker_* > Symbol > * > None
        if key in settings_dict:
            return settings_dict[key]
        
        broker_wildcard = f"{broker}_*"
        if broker_wildcard in settings_dict:
            return settings_dict[broker_wildcard]
        
        if symbol in settings_dict:
            return settings_dict[symbol]
        
        if '*' in settings_dict:
            return settings_dict['*']
        
        return DEFAULT_GAP_THRESHOLD if threshold_type == 'gap' else DEFAULT_SPIKE_THRESHOLD
    
    def get_threshold_source(self, broker, symbol, threshold_type):
        """Get source of threshold (for display)"""
        settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
        key = f"{broker}_{symbol}"
        
        if key in settings_dict:
            return f"{key}"
        
        broker_wildcard = f"{broker}_*"
        if broker_wildcard in settings_dict:
            return broker_wildcard
        
        if symbol in settings_dict:
            return symbol
        
        if '*' in settings_dict:
            return "*"
        
        return "default"
    
    def edit_threshold(self, event):
        """Edit threshold on double-click"""
        try:
            # Get clicked item and column
            item = self.gs_tree.selection()[0]
            column = self.gs_tree.identify_column(event.x)
            
            # Only edit Gap % or Spike % columns
            if column not in ('#3', '#4'):  # Column 3 = Gap %, Column 4 = Spike %
                return
            
            values = list(self.gs_tree.item(item, 'values'))
            broker = values[0]
            symbol = values[1]
            
            col_name = "Gap" if column == '#3' else "Spike"
            current_value = values[2] if column == '#3' else values[3]
            
            # Show input dialog
            new_value = tk.simpledialog.askstring(
                f"Edit {col_name} Threshold",
                f"{broker} {symbol}\nCurrent {col_name}: {current_value}%\n\nEnter new {col_name} threshold (%):",
                initialvalue=current_value
            )
            
            if new_value is not None:
                try:
                    threshold = float(new_value) if new_value.strip() else None
                    
                    # Update tree display
                    if column == '#3':  # Gap
                        values[2] = f"{threshold:.3f}" if threshold else ""
                    else:  # Spike
                        values[3] = f"{threshold:.3f}" if threshold else ""
                    
                    self.gs_tree.item(item, values=values)
                    
                    logger.info(f"Edited {col_name} for {broker}_{symbol}: {threshold}")
                    
                except ValueError:
                    messagebox.showerror("Error", "Invalid number format")
            
        except IndexError:
            pass
        except Exception as e:
            logger.error(f"Error editing threshold: {e}")
            messagebox.showerror("Error", f"Lỗi edit: {str(e)}")
    
    def apply_to_all(self):
        """Apply threshold to all symbols from all brokers"""
        try:
            gap_val = float(self.quick_gap_var.get())
            spike_val = float(self.quick_spike_var.get())
            
            # Count total symbols
            total_count = len(self.gs_tree.get_children())
            
            # Count brokers
            brokers_in_tree = set()
            for item in self.gs_tree.get_children():
                values = self.gs_tree.item(item, 'values')
                brokers_in_tree.add(values[0])
            
            confirm = messagebox.askyesno(
                "Confirm - Apply to ALL",
                f"🌐 Apply thresholds cho TẤT CẢ symbols từ TẤT CẢ brokers\n\n"
                f"Gap Threshold: {gap_val}%\n"
                f"Spike Threshold: {spike_val}%\n\n"
                f"Số brokers: {len(brokers_in_tree)}\n"
                f"Tổng số symbols: {total_count}\n\n"
                f"Continue?"
            )
            
            if confirm:
                count = 0
                for item in self.gs_tree.get_children():
                    values = list(self.gs_tree.item(item, 'values'))
                    values[2] = f"{gap_val:.3f}"
                    values[3] = f"{spike_val:.3f}"
                    self.gs_tree.item(item, values=values)
                    count += 1
                
                # Tự động lưu luôn (không hiện messagebox)
                self.save_gap_spike_from_tree(show_message=False)
                
                messagebox.showinfo("Success", 
                                  f"✅ Đã apply và LƯU thresholds cho TẤT CẢ\n\n"
                                  f"Brokers: {len(brokers_in_tree)}\n"
                                  f"Symbols: {count}\n"
                                  f"Gap: {gap_val}%\n"
                                  f"Spike: {spike_val}%\n\n"
                                  f"💾 Settings đã được lưu tự động!")
                
                self.main_app.log(f"🌐 Applied & Saved Gap:{gap_val}%, Spike:{spike_val}% to ALL ({count} symbols)")
                logger.info(f"Applied & Saved Gap:{gap_val}%, Spike:{spike_val}% to all: {count} symbols")
            
        except ValueError:
            messagebox.showerror("Error", "Invalid number format - vui lòng nhập số hợp lệ")
        except Exception as e:
            logger.error(f"Error applying to all: {e}")
            messagebox.showerror("Error", f"Lỗi: {str(e)}")
    
    def apply_to_broker(self):
        """Apply threshold to all symbols of selected broker (legacy - from tree selection)"""
        try:
            selected = self.gs_tree.selection()
            if not selected:
                messagebox.showwarning("No Selection", "Vui lòng chọn symbol từ broker cần apply")
                return
            
            # Get broker from selected item
            values = self.gs_tree.item(selected[0], 'values')
            broker = values[0]
            
            gap_val = float(self.quick_gap_var.get())
            spike_val = float(self.quick_spike_var.get())
            
            confirm = messagebox.askyesno(
                "Confirm",
                f"Apply Gap: {gap_val}% và Spike: {spike_val}% cho TẤT CẢ symbols từ broker {broker}?"
            )
            
            if confirm:
                count = 0
                for item in self.gs_tree.get_children():
                    item_values = list(self.gs_tree.item(item, 'values'))
                    if item_values[0] == broker:
                        item_values[2] = f"{gap_val:.3f}"
                        item_values[3] = f"{spike_val:.3f}"
                        self.gs_tree.item(item, values=item_values)
                        count += 1
                
                messagebox.showinfo("Success", f"Đã apply cho {count} symbols từ {broker}")
                logger.info(f"Applied Gap:{gap_val}%, Spike:{spike_val}% to {broker}: {count} symbols")
            
        except ValueError:
            messagebox.showerror("Error", "Invalid number format")
        except Exception as e:
            logger.error(f"Error applying to broker: {e}")
            messagebox.showerror("Error", f"Lỗi: {str(e)}")
    
    def apply_to_selected_broker_from_dropdown(self):
        """Apply threshold to all symbols from broker selected in dropdown"""
        try:
            broker = self.broker_selector_var.get()
            if not broker:
                messagebox.showwarning("No Selection", "Vui lòng chọn broker từ dropdown")
                return
            
            gap_val = float(self.quick_gap_var.get())
            spike_val = float(self.quick_spike_var.get())
            
            # Count symbols for this broker
            count_preview = 0
            for item in self.gs_tree.get_children():
                item_values = self.gs_tree.item(item, 'values')
                if item_values[0] == broker:
                    count_preview += 1
            
            if count_preview == 0:
                messagebox.showwarning("No Symbols", f"Không có symbols nào từ broker {broker}")
                return
            
            confirm = messagebox.askyesno(
                "Confirm - Apply to Broker",
                f"📊 Apply thresholds cho broker: {broker}\n\n"
                f"Gap Threshold: {gap_val}%\n"
                f"Spike Threshold: {spike_val}%\n\n"
                f"Số symbols sẽ được update: {count_preview}\n\n"
                f"Continue?"
            )
            
            if confirm:
                count = 0
                for item in self.gs_tree.get_children():
                    item_values = list(self.gs_tree.item(item, 'values'))
                    if item_values[0] == broker:
                        item_values[2] = f"{gap_val:.3f}"
                        item_values[3] = f"{spike_val:.3f}"
                        self.gs_tree.item(item, values=item_values)
                        count += 1
                
                # Tự động lưu luôn (không hiện messagebox)
                self.save_gap_spike_from_tree(show_message=False)
                
                messagebox.showinfo("Success", 
                                  f"✅ Đã apply và LƯU thresholds cho broker {broker}\n\n"
                                  f"Updated: {count} symbols\n"
                                  f"Gap: {gap_val}%\n"
                                  f"Spike: {spike_val}%\n\n"
                                  f"💾 Settings đã được lưu tự động!")
                
                self.main_app.log(f"📊 Applied & Saved Gap:{gap_val}%, Spike:{spike_val}% to broker {broker} ({count} symbols)")
                logger.info(f"Applied & Saved thresholds to broker {broker}: {count} symbols")
            
        except ValueError:
            messagebox.showerror("Error", "Invalid number format - vui lòng nhập số hợp lệ")
        except Exception as e:
            logger.error(f"Error applying to broker from dropdown: {e}")
            messagebox.showerror("Error", f"Lỗi: {str(e)}")
    
    def save_gap_spike_from_tree(self, show_message=True):
        """Save Gap/Spike settings from treeview"""
        global gap_settings, spike_settings
        try:
            new_gap_settings = {}
            new_spike_settings = {}
            
            for item in self.gs_tree.get_children():
                values = self.gs_tree.item(item, 'values')
                broker = values[0]
                symbol = values[1]
                gap_str = values[2]
                spike_str = values[3]
                
                key = f"{broker}_{symbol}"
                
                # Save Gap if has value
                if gap_str and gap_str.strip():
                    try:
                        new_gap_settings[key] = float(gap_str)
                    except ValueError:
                        pass
                
                # Save Spike if has value
                if spike_str and spike_str.strip():
                    try:
                        new_spike_settings[key] = float(spike_str)
                    except ValueError:
                        pass
            
            # Update global settings
            gap_settings = new_gap_settings
            spike_settings = new_spike_settings
            
            # Save to files
            save_gap_settings()
            save_spike_settings()
            
            if show_message:
                messagebox.showinfo("Success", 
                                  f"Đã lưu:\n"
                                  f"- Gap: {len(gap_settings)} configs\n"
                                  f"- Spike: {len(spike_settings)} configs")
            
            self.main_app.log(f"⚙️ Saved Gap/Spike settings: "
                            f"Gap={len(gap_settings)}, Spike={len(spike_settings)}")
            logger.info(f"Gap/Spike settings saved from tree")
            
        except Exception as e:
            logger.error(f"Error saving from tree: {e}")
            if show_message:
                messagebox.showerror("Error", f"Lỗi lưu settings: {str(e)}")
    
    def clear_selected_thresholds(self):
        """Clear thresholds for selected symbols"""
        try:
            selected = self.gs_tree.selection()
            if not selected:
                messagebox.showwarning("No Selection", "Vui lòng chọn symbols cần clear")
                return
            
            confirm = messagebox.askyesno("Confirm", 
                                         f"Clear thresholds cho {len(selected)} symbol(s)?")
            if confirm:
                for item in selected:
                    values = list(self.gs_tree.item(item, 'values'))
                    values[2] = ""  # Clear Gap
                    values[3] = ""  # Clear Spike
                    self.gs_tree.item(item, values=values)
                
                messagebox.showinfo("Success", f"Đã clear {len(selected)} symbol(s)")
            
        except Exception as e:
            logger.error(f"Error clearing selected: {e}")
            messagebox.showerror("Error", f"Lỗi: {str(e)}")
    
    def export_to_text_mode(self):
        """Export current settings to text format (for advanced users)"""
        try:
            # Create text window
            text_win = tk.Toplevel(self.window)
            text_win.title("📄 Export Gap/Spike Settings (Text Mode)")
            text_win.geometry("600x400")
            
            # Make window modal - chặn thao tác cửa sổ parent
            text_win.transient(self.window)  # Window luôn nằm trên parent
            text_win.grab_set()  # Chặn input đến parent window
            
            text_win.lift()  # Đưa cửa sổ lên trên
            text_win.focus_force()  # Focus vào cửa sổ
            
            # Gap text
            gap_frame = ttk.LabelFrame(text_win, text="Gap Settings", padding="10")
            gap_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
            
            gap_text = scrolledtext.ScrolledText(gap_frame, height=8, wrap=tk.WORD)
            gap_text.pack(fill=tk.BOTH, expand=True)
            
            gap_content = "\n".join([f"{k}:{v}" for k, v in gap_settings.items()])
            gap_text.insert('1.0', gap_content)
            
            # Spike text
            spike_frame = ttk.LabelFrame(text_win, text="Spike Settings", padding="10")
            spike_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
            
            spike_text = scrolledtext.ScrolledText(spike_frame, height=8, wrap=tk.WORD)
            spike_text.pack(fill=tk.BOTH, expand=True)
            
            spike_content = "\n".join([f"{k}:{v}" for k, v in spike_settings.items()])
            spike_text.insert('1.0', spike_content)
            
            ttk.Label(text_win, text="Copy/Edit và paste vào file nếu cần", 
                     foreground='blue').pack(pady=5)
            
        except Exception as e:
            logger.error(f"Error exporting to text: {e}")
            messagebox.showerror("Error", f"Lỗi export: {str(e)}")
    
    def refresh_hidden_list(self):
        """Refresh the hidden list display"""
        try:
            # Clear existing items
            for item in self.hidden_tree.get_children():
                self.hidden_tree.delete(item)
            
            # Add all manually hidden symbols
            for key in sorted(manual_hidden_delays.keys()):
                broker, symbol = key.split('_', 1)
                self.hidden_tree.insert('', 'end', values=(broker, symbol), tags=(key,))
            
        except Exception as e:
            logger.error(f"Error refreshing hidden list: {e}")
    
    def unhide_selected(self):
        """Unhide selected symbols"""
        try:
            selected = self.hidden_tree.selection()
            if not selected:
                messagebox.showwarning("No Selection", "Vui lòng chọn symbol cần unhide")
                return
            
            count = 0
            for item in selected:
                key = self.hidden_tree.item(item, 'tags')[0]
                if key in manual_hidden_delays:
                    del manual_hidden_delays[key]
                    count += 1
            
            if count > 0:
                save_manual_hidden_delays()
                self.refresh_hidden_list()
                self.main_app.update_delay_board_display()
                self.main_app.log(f"🔓 Unhidden {count} symbol(s)")
                messagebox.showinfo("Success", f"Đã unhide {count} symbol(s)")
            
        except Exception as e:
            logger.error(f"Error unhiding selected: {e}")
            messagebox.showerror("Error", f"Lỗi unhide: {str(e)}")
    
    def clear_all_hidden(self):
        """Clear all manually hidden symbols"""
        try:
            if not manual_hidden_delays:
                messagebox.showinfo("Info", "Không có symbols bị hidden")
                return
            
            count = len(manual_hidden_delays)
            confirm = messagebox.askyesno("Confirm", 
                                         f"Bạn có chắc muốn unhide tất cả {count} symbols?")
            if confirm:
                manual_hidden_delays.clear()
                save_manual_hidden_delays()
                self.refresh_hidden_list()
                self.main_app.update_delay_board_display()
                self.main_app.log(f"🔓 Cleared all {count} hidden symbols")
                messagebox.showinfo("Success", f"Đã unhide tất cả {count} symbols")
            
        except Exception as e:
            logger.error(f"Error clearing all hidden: {e}")
            messagebox.showerror("Error", f"Lỗi clear all: {str(e)}")

# ===================== HIDDEN DELAYS WINDOW =====================
class HiddenDelaysWindow:
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("Hidden Delays (>60 minutes)")
        self.window.geometry("1000x600")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Top Frame
        top_frame = ttk.Frame(self.window, padding="10")
        top_frame.pack(fill=tk.X)
        
        ttk.Label(top_frame, text="🔒 Hidden Delays (>60 phút)", font=('Arial', 14, 'bold')).pack(side=tk.LEFT, padx=10)
        
        # Refresh button
        ttk.Button(top_frame, text="🔄 Refresh", command=self.update_display).pack(side=tk.LEFT, padx=5)
        
        # Info label
        self.info_label = ttk.Label(top_frame, text="", font=('Arial', 9))
        self.info_label.pack(side=tk.LEFT, padx=20)
        
        # Main Table Frame
        table_frame = ttk.LabelFrame(self.window, text="Symbols with Long Delays", padding="10")
        table_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create Treeview
        columns = ('Broker', 'Symbol', 'Bid', 'Last Change', 'Delay Time', 'Status', 'Trading Status')
        self.tree = ttk.Treeview(table_frame, columns=columns, show='headings', height=20)
        
        self.tree.heading('Broker', text='Broker')
        self.tree.heading('Symbol', text='Symbol')
        self.tree.heading('Bid', text='Bid Price')
        self.tree.heading('Last Change', text='Last Change')
        self.tree.heading('Delay Time', text='Delay Duration')
        self.tree.heading('Status', text='Status')
        self.tree.heading('Trading Status', text='Market Status')
        
        self.tree.column('Broker', width=150)
        self.tree.column('Symbol', width=100)
        self.tree.column('Bid', width=100)
        self.tree.column('Last Change', width=120)
        self.tree.column('Delay Time', width=120)
        self.tree.column('Status', width=200)
        self.tree.column('Trading Status', width=120)
        
        # Scrollbars
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        self.tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        hsb.grid(row=1, column=0, sticky='ew')
        
        table_frame.grid_rowconfigure(0, weight=1)
        table_frame.grid_columnconfigure(0, weight=1)
        
        # Tags for colors
        self.tree.tag_configure('hidden_extreme', background='#ffcccc')  # Red - Very long
        self.tree.tag_configure('hidden_long', background='#ffe4cc')     # Orange - Long
        
        # Bind double-click to open chart
        self.tree.bind('<Double-Button-1>', self.on_symbol_double_click)
        
        # Info Frame
        info_frame = ttk.Frame(self.window, padding="10")
        info_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(info_frame, text="ℹ️  Info:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        ttk.Label(info_frame, text="Symbols bị ẩn vì delay quá lâu (>60 phút). Có thể là broker disconnect hoặc market đóng cửa dài hạn.").pack(side=tk.LEFT)
        
        # Initial display
        self.update_display()
        
        # Auto-refresh every 5 seconds
        self.auto_refresh()
    
    def update_display(self):
        """Cập nhật hiển thị hidden delays"""
        try:
            with data_lock:
                # Clear existing items
                for item in self.tree.get_children():
                    self.tree.delete(item)
                
                current_time = time.time()
                delay_threshold = self.main_app.delay_threshold.get()
                
                # Find symbols with delay >= 60 minutes
                hidden_symbols = []
                
                for key, tracking_info in bid_tracking.items():
                    last_change_time = tracking_info['last_change_time']
                    delay_duration = current_time - last_change_time
                    
                    # Only show if delay >= threshold AND >= 60 minutes (3600s)
                    if delay_duration >= delay_threshold and delay_duration >= 3600:
                        broker, symbol = key.split('_', 1)
                        
                        # Get current data
                        if broker in market_data and symbol in market_data[broker]:
                            symbol_data = market_data[broker][symbol]
                            current_bid = symbol_data.get('bid', 0)
                            is_open = symbol_data.get('isOpen', False)
                            
                            # Chỉ hiển thị symbols đang trong giờ giao dịch
                            if not is_open:
                                continue  # Bỏ qua nếu đóng cửa
                            
                            hidden_symbols.append({
                                'broker': broker,
                                'symbol': symbol,
                                'bid': current_bid,
                                'is_open': is_open,
                                'last_change_time': last_change_time,
                                'delay_duration': delay_duration
                            })
                
                # Sort by delay duration (longest first)
                hidden_symbols.sort(key=lambda x: x['delay_duration'], reverse=True)
                
                # Add to tree
                for item in hidden_symbols:
                    broker = item['broker']
                    symbol = item['symbol']
                    bid = item['bid']
                    is_open = item['is_open']
                    last_change_time = item['last_change_time']
                    delay_duration = item['delay_duration']
                    
                    # Format display
                    last_change_str = server_timestamp_to_datetime(last_change_time).strftime('%Y-%m-%d %H:%M:%S')
                    
                    # Format delay time
                    delay_hours = int(delay_duration / 3600)
                    delay_minutes = int((delay_duration % 3600) / 60)
                    
                    if delay_hours > 0:
                        delay_str = f"{delay_hours}h {delay_minutes}m"
                    else:
                        delay_str = f"{delay_minutes}m"
                    
                    # Determine tag/status
                    if delay_duration >= 86400:  # >= 24 hours
                        tag = 'hidden_extreme'
                        status = f"🔴 EXTREME DELAY ({delay_str})"
                    elif delay_duration >= 21600:  # >= 6 hours
                        tag = 'hidden_extreme'
                        status = f"🔴 VERY LONG DELAY ({delay_str})"
                    else:
                        tag = 'hidden_long'
                        status = f"🟠 LONG DELAY ({delay_str})"
                    
                    # Market status
                    market_status = "🟢 Trading" if is_open else "🔴 Closed"
                    
                    # Insert row
                    gap_threshold = self.get_threshold_for_display(broker, symbol, 'gap')
                    spike_threshold = self.get_threshold_for_display(broker, symbol, 'spike')

                    # Insert row (columns: Time, Broker, Symbol, Price, Gap Threshold, Spike Threshold, Status)
                    self.tree.insert('', 'end', values=(
                        time_str,
                        broker,
                        symbol,
                        f"{price:.5f}",
                        f"{gap_threshold:.3f}",
                        f"{spike_threshold:.3f}",
                        status
                    ), tags=(tag,))

                
                # Update info label
                self.info_label.config(text=f"Total: {len(hidden_symbols)} hidden symbol(s)")
                
                # If no hidden delays, show message
                if not hidden_symbols:
                    self.tree.insert('', 'end', values=(
                        'No hidden delays',
                        '-',
                        '-',
                        '-',
                        '-',
                        '✅ Không có symbols bị ẩn',
                        '-'
                    ))
                    self.info_label.config(text="Total: 0 hidden symbols")
                    
        except Exception as e:
            logger.error(f"Error updating hidden delays display: {e}")
    
def on_symbol_double_click(self, event):
    """Handle double-click on main table: edit threshold or open chart."""
    try:
        # Lấy item được click
        item = self.tree.selection()[0]
        values = self.tree.item(item, 'values')
        if not values or len(values) < 3:
            return

        # Xác định cột được click
        column = self.tree.identify_column(event.x)

        # Values: (Time, Broker, Symbol, Price, Gap Threshold, Spike Threshold, Status)
        broker = values[1]
        symbol = values[2]

        # Double-click chỉnh threshold
        if column in ('#5', '#6') and broker and symbol:
            threshold_type = 'gap' if column == '#5' else 'spike'
            col_label = "Gap" if threshold_type == 'gap' else "Spike"

            current_threshold = self.get_threshold_for_display(broker, symbol, threshold_type)
            initial = f"{current_threshold:.3f}" if current_threshold is not None else ""

            new_value = simpledialog.askstring(
                f"Edit {col_label} Threshold",
                f"{broker} {symbol}\nCurrent {col_label}: {initial}%\n\n"
                f"Nhập {col_label} threshold mới (%):\n(Để trống = dùng default)",
                initialvalue=initial,
                parent=self.root
            )
            if new_value is None:
                return

            new_value = new_value.strip()
            global gap_settings, spike_settings
            settings_dict = gap_settings if threshold_type == 'gap' else spike_settings
            key = f"{broker}_{symbol}"

            if new_value == "":
                if key in settings_dict:
                    del settings_dict[key]
            else:
                try:
                    threshold = float(new_value)
                except ValueError:
                    messagebox.showerror("Error", "Invalid number format")
                    return
                settings_dict[key] = threshold

            if threshold_type == 'gap':
                save_gap_settings()
            else:
                save_spike_settings()

            updated_threshold = self.get_threshold_for_display(broker, symbol, threshold_type)
            display_val = f"{updated_threshold:.3f}" if updated_threshold is not None else ""
            if threshold_type == 'gap':
                self.tree.set(item, 'Gap Threshold', display_val)
            else:
                self.tree.set(item, 'Spike Threshold', display_val)

            return

        # Double-click cột khác -> mở chart
        if broker and symbol:
            self.open_chart(broker, symbol)
            self.log(f"Opened chart for {symbol} ({broker})")

    except Exception as e:
        logger.error(f"Error handling double-click on table: {e}")


    
    def auto_refresh(self):
        """Auto refresh every 5 seconds"""
        if self.window.winfo_exists():
            self.update_display()
            self.window.after(5000, self.auto_refresh)

# ===================== RAW DATA VIEWER WINDOW =====================
class RawDataViewerWindow:
    """Window to view raw market data from all brokers"""
    
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("📊 Raw Data Viewer - Market Data from MT4/MT5")
        self.window.geometry("1200x700")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Selected symbol for detail view
        self.selected_broker = None
        self.selected_symbol = None
        
        # Top Frame - Title and controls
        top_frame = ttk.Frame(self.window, padding="10")
        top_frame.pack(fill=tk.X)
        
        ttk.Label(top_frame, text="📊 Raw Market Data", 
                 font=('Arial', 14, 'bold')).pack(side=tk.LEFT, padx=10)
        
        # Refresh button
        ttk.Button(top_frame, text="🔄 Refresh", 
                  command=self.update_display).pack(side=tk.LEFT, padx=5)
        
        # Auto-refresh checkbox (default OFF to prevent freeze)
        self.auto_refresh_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top_frame, text="Auto Refresh (2s)", 
                       variable=self.auto_refresh_var).pack(side=tk.LEFT, padx=10)
        
        # Status label
        self.status_label = ttk.Label(top_frame, text="Loading...", foreground='blue')
        self.status_label.pack(side=tk.LEFT, padx=10)
        
        # Main container with two panels
        main_container = ttk.Frame(self.window)
        main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # LEFT PANEL - Symbol List
        left_panel = ttk.Frame(main_container)
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # Broker selector
        broker_frame = ttk.LabelFrame(left_panel, text="🔍 Filter by Broker", padding="5")
        broker_frame.pack(fill=tk.X, pady=(0, 5))
        
        self.broker_filter_var = tk.StringVar(value="All Brokers")
        self.broker_filter = ttk.Combobox(broker_frame, 
                                          textvariable=self.broker_filter_var,
                                          state='readonly',
                                          width=30)
        self.broker_filter.pack(fill=tk.X, padx=5, pady=5)
        self.broker_filter.bind('<<ComboboxSelected>>', lambda e: self.update_symbol_list())
        
        # Symbol list
        symbol_frame = ttk.LabelFrame(left_panel, text="📋 Symbols", padding="5")
        symbol_frame.pack(fill=tk.BOTH, expand=True)
        
        # Create Treeview for symbols
        columns = ('Broker', 'Symbol', 'Bid', 'Ask', 'Last Update')
        self.symbol_tree = ttk.Treeview(symbol_frame, columns=columns, 
                                        show='headings', height=20)
        
        self.symbol_tree.heading('Broker', text='Broker')
        self.symbol_tree.heading('Symbol', text='Symbol')
        self.symbol_tree.heading('Bid', text='Bid')
        self.symbol_tree.heading('Ask', text='Ask')
        self.symbol_tree.heading('Last Update', text='Last Update')
        
        self.symbol_tree.column('Broker', width=120)
        self.symbol_tree.column('Symbol', width=100)
        self.symbol_tree.column('Bid', width=80)
        self.symbol_tree.column('Ask', width=80)
        self.symbol_tree.column('Last Update', width=150)
        
        # Scrollbar
        vsb = ttk.Scrollbar(symbol_frame, orient="vertical", 
                           command=self.symbol_tree.yview)
        self.symbol_tree.configure(yscrollcommand=vsb.set)
        
        self.symbol_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Bind selection event
        self.symbol_tree.bind('<<TreeviewSelect>>', self.on_symbol_select)
        
        # RIGHT PANEL - Detail View
        right_panel = ttk.Frame(main_container)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        # Detail header
        detail_header = ttk.Frame(right_panel)
        detail_header.pack(fill=tk.X, pady=(0, 5))
        
        self.detail_title = ttk.Label(detail_header, 
                                      text="Select a symbol to view details",
                                      font=('Arial', 12, 'bold'))
        self.detail_title.pack(side=tk.LEFT)
        
        ttk.Button(detail_header, text="📋 Copy JSON", 
                  command=self.copy_detail_to_clipboard).pack(side=tk.RIGHT, padx=5)
        
        # Detail text (with scrollbar)
        detail_frame = ttk.LabelFrame(right_panel, text="📊 Raw Data Details", padding="5")
        detail_frame.pack(fill=tk.BOTH, expand=True)
        
        # Text widget with scrollbar
        text_scroll = ttk.Scrollbar(detail_frame)
        text_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.detail_text = tk.Text(detail_frame, wrap=tk.WORD, 
                                   font=('Consolas', 10),
                                   yscrollcommand=text_scroll.set,
                                   bg='#1e1e1e', fg='#d4d4d4',
                                   insertbackground='white',
                                   selectbackground='#264f78')
        self.detail_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text_scroll.config(command=self.detail_text.yview)
        
        # Schedule initial update (avoid blocking on init)
        self.window.after(100, self.initial_update)
    
    def initial_update(self):
        """Initial update and start auto-refresh"""
        try:
            logger.info("Raw Data Viewer: Starting initial update...")
            self.status_label.config(text="Loading data...", foreground='blue')
            
            # Show initial help message
            self.detail_text.delete(1.0, tk.END)
            self.detail_text.insert(tk.END, "📊 Loading market data...\n\nPlease wait...")
            
            # Simple check first
            broker_count = 0
            try:
                with data_lock:
                    broker_count = len(market_data)
                logger.info(f"Raw Data Viewer: Found {broker_count} brokers")
            except Exception as check_err:
                logger.error(f"Raw Data Viewer: Error checking data: {check_err}")
            
            if broker_count == 0:
                logger.warning("Raw Data Viewer: No data yet, waiting for EA...")
                self.status_label.config(text="No data yet - waiting for EA...", foreground='orange')
                self.detail_text.delete(1.0, tk.END)
                self.detail_text.insert(tk.END, 
                    "⏳ Waiting for market data from EA...\n\n"
                    "Please make sure:\n"
                    "1. ✅ EA is running on MT4/MT5\n"
                    "2. ✅ Symbols are in Market Watch\n"
                    "3. ✅ Python server is receiving data\n\n"
                    "This window will auto-update when data is available."
                )
                # Retry after 2 seconds
                self.window.after(2000, self.initial_update)
                return
            
            # Load display
            logger.info("Raw Data Viewer: Updating display...")
            self.update_display()
            logger.info("Raw Data Viewer: Display updated successfully")
            self.status_label.config(text="Ready", foreground='green')
            
            # Update help text
            self.detail_text.delete(1.0, tk.END)
            self.detail_text.insert(tk.END, 
                "📊 Raw Market Data Viewer\n\n"
                "👈 Select a symbol from the list to view details\n\n"
                "Tips:\n"
                "• Filter by broker using the dropdown\n"
                "• Enable auto-refresh to monitor in real-time\n"
                "• Click 'Copy JSON' to export data\n"
            )
            
            # Start auto-refresh after initial update
            self.window.after(2000, self.auto_refresh)
            logger.info("Raw Data Viewer: Ready")
        except Exception as e:
            logger.error(f"Error in initial update: {e}", exc_info=True)
            self.status_label.config(text=f"Error: {str(e)[:50]}", foreground='red')
            # Show error message
            self.detail_text.delete(1.0, tk.END)
            self.detail_text.insert(tk.END, 
                f"⚠️ Error loading data:\n\n{str(e)}\n\n"
                "Please check:\n"
                "1. EA is running\n"
                "2. Symbols in Market Watch\n"
                "3. Data is being sent to Python\n"
                "4. Check console for detailed error logs"
            )
    
    def update_display(self):
        """Update broker filter and symbol list"""
        try:
            # Quick data collection with timeout protection
            brokers = []
            try:
                with data_lock:
                    # Get all brokers (quick)
                    brokers = sorted(list(market_data.keys()))
            except Exception as lock_err:
                logger.error(f"Error getting brokers: {lock_err}")
                return
            
            # Update UI (outside lock)
            filter_list = ["All Brokers"] + brokers
            self.broker_filter['values'] = filter_list
            
            # If current selection not valid, reset to "All Brokers"
            current_selection = self.broker_filter_var.get()
            if not current_selection or current_selection not in filter_list:
                self.broker_filter_var.set("All Brokers")
            
            # Update symbol list
            self.update_symbol_list()
                
        except Exception as e:
            logger.error(f"Error updating raw data viewer: {e}", exc_info=True)
            self.status_label.config(text="Error updating display", foreground='red')
    
    def update_symbol_list(self):
        """Update the symbol list based on broker filter"""
        try:
            # Clear current list first (outside lock)
            try:
                for item in self.symbol_tree.get_children():
                    self.symbol_tree.delete(item)
            except Exception as clear_err:
                logger.error(f"Error clearing tree: {clear_err}")
            
            # Get current filter
            current_filter = self.broker_filter_var.get()
            if not current_filter:
                current_filter = "All Brokers"
            
            # Collect data quickly with lock (with timeout protection)
            symbols_to_display = []
            try:
                with data_lock:
                    current_time = time.time()
                    
                    # Collect symbols (limit to 100 for faster load)
                    count = 0
                    max_symbols = 100  # Reduced from 500 for speed
                    
                    for broker in sorted(market_data.keys()):
                        # Apply filter
                        if current_filter != "All Brokers" and broker != current_filter:
                            continue
                        
                        symbols = market_data.get(broker, {})
                        for symbol in sorted(symbols.keys()):
                            if count >= max_symbols:  # Safety limit
                                break
                            
                            data = symbols.get(symbol, {})
                            bid = data.get('bid', 0)
                            ask = data.get('ask', 0)
                            timestamp = data.get('timestamp', 0)
                            digits = data.get('digits', 5)
                            
                            # Format last update (simplified)
                            if timestamp > 0:
                                age = current_time - timestamp
                                if age < 60:
                                    last_update = f"{int(age)}s"
                                elif age < 3600:
                                    last_update = f"{int(age/60)}m"
                                else:
                                    last_update = f"{int(age/3600)}h"
                            else:
                                last_update = "N/A"
                            
                            symbols_to_display.append((
                                broker,
                                symbol,
                                f"{bid:.{digits}f}" if bid > 0 else "N/A",
                                f"{ask:.{digits}f}" if ask > 0 else "N/A",
                                last_update,
                                f"{broker}_{symbol}"
                            ))
                            count += 1
                        
                        if count >= max_symbols:
                            break
                            
            except Exception as lock_err:
                logger.error(f"Error collecting symbol data: {lock_err}", exc_info=True)
                self.status_label.config(text="Error reading data", foreground='red')
                return
            
            # Insert into tree (outside lock, batch operation)
            try:
                for values in symbols_to_display:
                    tag = values[-1]
                    self.symbol_tree.insert('', 'end', values=values[:-1], tags=(tag,))
            except Exception as insert_err:
                logger.error(f"Error inserting to tree: {insert_err}")
            
            # Update status
            symbol_count = len(symbols_to_display)
            if symbol_count >= 100:
                self.status_label.config(text=f"{symbol_count}+ symbols", foreground='green')
            elif symbol_count > 0:
                self.status_label.config(text=f"{symbol_count} symbols", foreground='green')
            else:
                self.status_label.config(text="No symbols found", foreground='orange')
                
        except Exception as e:
            logger.error(f"Error updating symbol list: {e}", exc_info=True)
            self.status_label.config(text=f"Error loading symbols", foreground='red')
    
    def on_symbol_select(self, event):
        """Handle symbol selection"""
        try:
            selection = self.symbol_tree.selection()
            if not selection:
                return
            
            item = self.symbol_tree.item(selection[0])
            values = item['values']
            
            if len(values) >= 2:
                self.selected_broker = values[0]
                self.selected_symbol = values[1]
                self.update_detail_view()
        
        except Exception as e:
            logger.error(f"Error handling symbol selection: {e}")
    
    def update_detail_view(self):
        """Update the detail view with selected symbol's raw data"""
        try:
            if not self.selected_broker or not self.selected_symbol:
                return
            
            with data_lock:
                # Check if data exists
                if self.selected_broker not in market_data:
                    self.detail_text.delete(1.0, tk.END)
                    self.detail_text.insert(tk.END, "⚠️ Broker not found in market_data")
                    return
                
                if self.selected_symbol not in market_data[self.selected_broker]:
                    self.detail_text.delete(1.0, tk.END)
                    self.detail_text.insert(tk.END, "⚠️ Symbol not found in market_data")
                    return
                
                # Get data
                data = market_data[self.selected_broker][self.selected_symbol]
                key = f"{self.selected_broker}_{self.selected_symbol}"
                
                # Update title
                self.detail_title.config(
                    text=f"📊 {self.selected_broker} - {self.selected_symbol}"
                )
                
                # Build detailed view
                detail_lines = []
                detail_lines.append("=" * 80)
                detail_lines.append(f"BROKER: {self.selected_broker}")
                detail_lines.append(f"SYMBOL: {self.selected_symbol}")
                detail_lines.append("=" * 80)
                detail_lines.append("")
                
                # Current Prices
                detail_lines.append("📈 CURRENT PRICES")
                detail_lines.append("-" * 80)
                bid = data.get('bid', 0)
                ask = data.get('ask', 0)
                digits = data.get('digits', 5)
                spread = data.get('spread', 0)
                
                detail_lines.append(f"  Bid:        {bid:.{digits}f}")
                detail_lines.append(f"  Ask:        {ask:.{digits}f}")
                detail_lines.append(f"  Spread:     {spread}")
                detail_lines.append(f"  Digits:     {digits}")
                detail_lines.append("")
                
                # Timestamp
                detail_lines.append("⏰ TIMESTAMP")
                detail_lines.append("-" * 80)
                timestamp = data.get('timestamp', 0)
                if timestamp > 0:
                    dt = server_timestamp_to_datetime(timestamp)
                    age = time.time() - timestamp
                    detail_lines.append(f"  Timestamp:  {timestamp}")
                    detail_lines.append(f"  DateTime:   {dt.strftime('%Y-%m-%d %H:%M:%S')}")
                    detail_lines.append(f"  Age:        {age:.2f} seconds ago")
                else:
                    detail_lines.append(f"  Timestamp:  N/A")
                detail_lines.append("")
                
                # Previous OHLC (Index 1 - Candle đã đóng)
                detail_lines.append("📊 PREVIOUS CANDLE (M1 Index 1 - Đã đóng)")
                detail_lines.append("-" * 80)
                prev_ohlc = data.get('prev_ohlc', {})
                if prev_ohlc:
                    detail_lines.append(f"  Open:       {prev_ohlc.get('open', 'N/A')}")
                    detail_lines.append(f"  High:       {prev_ohlc.get('high', 'N/A')}")
                    detail_lines.append(f"  Low:        {prev_ohlc.get('low', 'N/A')}")
                    detail_lines.append(f"  Close:      {prev_ohlc.get('close', 'N/A')}")
                else:
                    detail_lines.append(f"  N/A")
                detail_lines.append("")
                
                # Current OHLC (Index 0 - Candle đang hình thành)
                detail_lines.append("📊 CURRENT CANDLE (M1 Index 0 - Đang hình thành)")
                detail_lines.append("-" * 80)
                current_ohlc = data.get('current_ohlc', {})
                if current_ohlc:
                    detail_lines.append(f"  Open:       {current_ohlc.get('open', 'N/A')}")
                    detail_lines.append(f"  High:       {current_ohlc.get('high', 'N/A')}")
                    detail_lines.append(f"  Low:        {current_ohlc.get('low', 'N/A')}")
                    detail_lines.append(f"  Close:      {current_ohlc.get('close', 'N/A')}")
                else:
                    detail_lines.append(f"  N/A")
                detail_lines.append("")
                
                # Market Status
                detail_lines.append("🕐 MARKET STATUS")
                detail_lines.append("-" * 80)
                is_open = data.get('isOpen', 'N/A')
                detail_lines.append(f"  Market Open: {is_open}")
                detail_lines.append("")
                
                # Bid Tracking Info
                detail_lines.append("📍 BID TRACKING")
                detail_lines.append("-" * 80)
                if key in bid_tracking:
                    bt = bid_tracking[key]
                    last_bid = bt.get('last_bid', 'N/A')
                    last_change = bt.get('last_change_time', 0)
                    first_seen = bt.get('first_seen_time', 0)
                    
                    detail_lines.append(f"  Last Bid:        {last_bid}")
                    if last_change > 0:
                        dt_change = server_timestamp_to_datetime(last_change)
                        age_change = time.time() - last_change
                        detail_lines.append(f"  Last Change:     {dt_change.strftime('%Y-%m-%d %H:%M:%S')}")
                        detail_lines.append(f"  Change Age:      {age_change:.2f} seconds ago")
                    if first_seen > 0:
                        dt_first = server_timestamp_to_datetime(first_seen)
                        detail_lines.append(f"  First Seen:      {dt_first.strftime('%Y-%m-%d %H:%M:%S')}")
                else:
                    detail_lines.append(f"  N/A")
                detail_lines.append("")
                
                # Candle Data Count
                detail_lines.append("📊 CANDLE DATA (Chart)")
                detail_lines.append("-" * 80)
                if key in candle_data:
                    candle_count = len(candle_data[key])
                    detail_lines.append(f"  Candles Stored:  {candle_count}")
                    if candle_count > 0:
                        last_candle = candle_data[key][-1]
                        detail_lines.append(f"  Last Candle:")
                        detail_lines.append(f"    Time:   {server_timestamp_to_datetime(last_candle[0]).strftime('%Y-%m-%d %H:%M:%S')}")
                        detail_lines.append(f"    Open:   {last_candle[1]}")
                        detail_lines.append(f"    High:   {last_candle[2]}")
                        detail_lines.append(f"    Low:    {last_candle[3]}")
                        detail_lines.append(f"    Close:  {last_candle[4]}")
                else:
                    detail_lines.append(f"  N/A")
                detail_lines.append("")
                
                # Gap & Spike Results
                detail_lines.append("⚡ GAP & SPIKE RESULTS")
                detail_lines.append("-" * 80)
                if key in gap_spike_results:
                    results = gap_spike_results[key]
                    gap_info = results.get('gap', {})
                    spike_info = results.get('spike', {})
                    
                    detail_lines.append(f"  Gap Detected:    {gap_info.get('detected', False)}")
                    detail_lines.append(f"  Gap %:           {gap_info.get('percentage', 0):.4f}%")
                    detail_lines.append(f"  Gap Direction:   {gap_info.get('direction', 'N/A')}")
                    detail_lines.append(f"  Gap Threshold:   {gap_info.get('threshold', 'N/A')}%")
                    detail_lines.append("")
                    detail_lines.append(f"  Spike Detected:  {spike_info.get('detected', False)}")
                    detail_lines.append(f"  Spike %:         {spike_info.get('strength', 0):.4f}%")
                    detail_lines.append(f"  Spike Type:      {spike_info.get('spike_type', 'N/A')}")
                    detail_lines.append(f"  Spike UP %:      {spike_info.get('spike_up_abs', 0):.4f}%")
                    detail_lines.append(f"  Spike DOWN %:    {spike_info.get('spike_down_abs', 0):.4f}%")
                    detail_lines.append(f"  Spike Threshold: {spike_info.get('threshold', 'N/A')}%")
                else:
                    detail_lines.append(f"  N/A")
                detail_lines.append("")
                
                # Manual Hidden Status
                detail_lines.append("👁️ VISIBILITY STATUS")
                detail_lines.append("-" * 80)
                is_hidden = key in manual_hidden_delays
                detail_lines.append(f"  Manually Hidden: {is_hidden}")
                detail_lines.append("")
                
                # RAW JSON (simplified to avoid freeze)
                detail_lines.append("📄 RAW JSON DATA")
                detail_lines.append("-" * 80)
                try:
                    import json
                    # Limit JSON to prevent freeze with large data
                    json_str = json.dumps(data, indent=2, default=str)
                    # Limit to first 5000 characters to prevent UI freeze
                    if len(json_str) > 5000:
                        json_str = json_str[:5000] + "\n... (truncated - data too large)"
                    detail_lines.append(json_str)
                except Exception as json_err:
                    detail_lines.append(f"⚠️ Error serializing JSON: {str(json_err)}")
                    detail_lines.append(f"Data keys: {list(data.keys())}")
            
            # Update text widget (outside data_lock to avoid blocking)
            self.detail_text.delete(1.0, tk.END)
            self.detail_text.insert(tk.END, "\n".join(detail_lines))
                
        except Exception as e:
            logger.error(f"Error updating detail view: {e}")
            try:
                self.detail_text.delete(1.0, tk.END)
                self.detail_text.insert(tk.END, f"⚠️ Error: {str(e)}")
            except:
                pass  # Window may be destroyed
    
    def copy_detail_to_clipboard(self):
        """Copy detail text to clipboard"""
        try:
            detail_content = self.detail_text.get(1.0, tk.END)
            self.window.clipboard_clear()
            self.window.clipboard_append(detail_content)
            messagebox.showinfo("Success", "Raw data copied to clipboard!")
        except Exception as e:
            logger.error(f"Error copying to clipboard: {e}")
            messagebox.showerror("Error", f"Failed to copy: {str(e)}")
    
    def auto_refresh(self):
        """Auto refresh every 2 seconds if enabled"""
        try:
            # Check if window still exists
            if not self.window.winfo_exists():
                return
            
            # Only refresh if enabled
            if self.auto_refresh_var.get():
                try:
                    self.update_symbol_list()  # Only update list, not full display
                    # If a symbol is selected, update its detail view
                    if self.selected_broker and self.selected_symbol:
                        self.update_detail_view()
                except Exception as update_err:
                    logger.error(f"Error during refresh update: {update_err}")
            
            # Schedule next refresh
            self.window.after(2000, self.auto_refresh)
        except Exception as e:
            logger.error(f"Error in auto refresh: {e}")

# ===================== PICTURE GALLERY WINDOW =====================
class PictureGalleryWindow:
    """Window to view all captured screenshots"""
    
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("📸 Picture Gallery - Gap & Spike Screenshots")
        self.window.geometry("1200x800")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Current selected image
        self.current_image = None
        self.current_image_path = None
        
        # Accepted screenshots for Google Sheets
        self.accepted_screenshots = []
        
        # Top Frame - Controls
        top_frame = ttk.Frame(self.window, padding="10")
        top_frame.pack(fill=tk.X)
        
        ttk.Label(top_frame, text="📸 Picture Gallery", 
                 font=('Arial', 14, 'bold')).pack(side=tk.LEFT, padx=10)
        
        ttk.Button(top_frame, text="🔄 Refresh", 
                  command=self.load_pictures).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(top_frame, text="🗑️ Delete Selected", 
                  command=self.delete_selected).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(top_frame, text="📂 Open Folder", 
                  command=self.open_pictures_folder).pack(side=tk.LEFT, padx=5)
        
        # Filter frame
        filter_frame = ttk.LabelFrame(self.window, text="🔍 Filter", padding="5")
        filter_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(filter_frame, text="Type:").pack(side=tk.LEFT, padx=5)
        self.filter_type_var = tk.StringVar(value="All")
        filter_type = ttk.Combobox(filter_frame, textvariable=self.filter_type_var,
                                    values=["All", "gap", "spike", "both"],
                                    state='readonly', width=15)
        filter_type.pack(side=tk.LEFT, padx=5)
        filter_type.bind('<<ComboboxSelected>>', lambda e: self.load_pictures())
        
        ttk.Label(filter_frame, text="Broker:").pack(side=tk.LEFT, padx=5)
        self.filter_broker_var = tk.StringVar(value="All")
        self.filter_broker = ttk.Combobox(filter_frame, textvariable=self.filter_broker_var,
                                          state='readonly', width=20)
        self.filter_broker.pack(side=tk.LEFT, padx=5)
        self.filter_broker.bind('<<ComboboxSelected>>', lambda e: self.load_pictures())

        ttk.Label(filter_frame, text="Tên:").pack(side=tk.LEFT, padx=5)
        initial_name = screenshot_settings.get('assigned_name', '')
        name_choices = list(PICTURE_ASSIGNEE_CHOICES)
        if initial_name and initial_name not in name_choices:
            name_choices.append(initial_name)

        self.assigned_name_var = tk.StringVar(value=initial_name)
        self.assigned_name_combo = ttk.Combobox(
            filter_frame,
            textvariable=self.assigned_name_var,
            values=name_choices,
            state='readonly',
            width=15
        )
        self.assigned_name_combo.pack(side=tk.LEFT, padx=5)
        self.assigned_name_combo.bind('<<ComboboxSelected>>', self.on_assigned_name_change)
        
        # Main container
        main_container = ttk.Frame(self.window)
        main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # LEFT: Thumbnail list
        left_panel = ttk.Frame(main_container)
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=False, padx=(0, 5))
        
        ttk.Label(left_panel, text="📋 Screenshots", font=('Arial', 10, 'bold')).pack()
        
        # Listbox for thumbnails
        list_frame = ttk.Frame(left_panel)
        list_frame.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.image_listbox = tk.Listbox(list_frame, width=40, height=30,
                                        yscrollcommand=scrollbar.set)
        self.image_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.image_listbox.yview)
        
        self.image_listbox.bind('<<ListboxSelect>>', self.on_image_select)
        
        # RIGHT: Image preview
        right_panel = ttk.Frame(main_container)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        ttk.Label(right_panel, text="🖼️ Preview", font=('Arial', 10, 'bold')).pack()
        
        # Canvas for image display
        self.canvas = tk.Canvas(right_panel, bg='#2d2d30', highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Action buttons below preview
        action_frame = ttk.Frame(right_panel)
        action_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Delete button
        ttk.Button(action_frame, text="🗑️ Delete", 
                  command=self.delete_selected,
                  style='Accent.TButton').pack(side=tk.LEFT, padx=5, pady=5)
        
        # Accept button (for Google Sheets)
        ttk.Button(action_frame, text="✅ Accept (Enter)", 
                  command=self.accept_screenshot,
                  style='Accent.TButton').pack(side=tk.LEFT, padx=5, pady=5)
        
        # Accepted list panel (below main container)
        accepted_frame = ttk.LabelFrame(self.window, text="✅ Accepted Screenshots (Ready to send)", padding="5")
        accepted_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Accepted listbox
        accepted_list_frame = ttk.Frame(accepted_frame)
        accepted_list_frame.pack(fill=tk.BOTH, expand=True)
        
        accepted_scrollbar = ttk.Scrollbar(accepted_list_frame)
        accepted_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.accepted_listbox = tk.Listbox(accepted_list_frame, height=4,
                                           yscrollcommand=accepted_scrollbar.set)
        self.accepted_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        accepted_scrollbar.config(command=self.accepted_listbox.yview)
        
        # Complete button
        complete_frame = ttk.Frame(accepted_frame)
        complete_frame.pack(fill=tk.X, pady=5)
        
        self.accepted_count_label = ttk.Label(complete_frame, text="Accepted: 0", 
                                              font=('Arial', 10, 'bold'))
        self.accepted_count_label.pack(side=tk.LEFT, padx=10)
        
        ttk.Button(complete_frame, text="📊 Hoàn thành - Gửi lên Google Sheets", 
                  command=self.complete_and_send,
                  style='Accent.TButton').pack(side=tk.RIGHT, padx=5)
        
        ttk.Button(complete_frame, text="🗑️ Clear Accepted", 
                  command=self.clear_accepted).pack(side=tk.RIGHT, padx=5)
        
        # Info label
        self.info_label = ttk.Label(self.window, text="No screenshots yet", 
                                    font=('Arial', 9), foreground='gray')
        self.info_label.pack(pady=5)
        
        # Bind keys
        self.window.bind('<Delete>', lambda e: self.delete_selected())
        self.window.bind('<KeyPress-Delete>', lambda e: self.delete_selected())
        self.window.bind('<Return>', lambda e: self.accept_screenshot())  # Enter key to accept
        self.window.bind('<KeyPress-Return>', lambda e: self.accept_screenshot())
        
        # Load pictures
        self.load_pictures()
    
    def load_pictures(self):
        """Load all screenshots from pictures folder"""
        try:
            # Clear listbox
            self.image_listbox.delete(0, tk.END)
            
            # Get pictures folder
            folder = screenshot_settings['folder']
            if not os.path.exists(folder):
                self.info_label.config(text="Pictures folder not found")
                return
            
            # Get all PNG files
            pattern = os.path.join(folder, "*.png")
            image_files = glob.glob(pattern)
            
            # Sort by modification time (newest first)
            image_files.sort(key=lambda x: os.path.getmtime(x), reverse=True)
            
            # Get unique brokers
            brokers = set()
            for filepath in image_files:
                filename = os.path.basename(filepath)
                parts = filename.split('_')
                if len(parts) >= 2:
                    brokers.add(parts[0])
            
            # Update broker filter
            broker_list = ["All"] + sorted(list(brokers))
            self.filter_broker['values'] = broker_list
            if self.filter_broker_var.get() not in broker_list:
                self.filter_broker_var.set("All")
            
            # Filter images
            filter_type = self.filter_type_var.get()
            filter_broker = self.filter_broker_var.get()
            
            filtered_files = []
            for filepath in image_files:
                filename = os.path.basename(filepath)
                
                # Filter by type
                if filter_type != "All":
                    if f"_{filter_type}_" not in filename:
                        continue
                
                # Filter by broker
                if filter_broker != "All":
                    if not filename.startswith(filter_broker + "_"):
                        continue
                
                filtered_files.append(filepath)
            
            # Add to listbox
            for filepath in filtered_files:
                filename = os.path.basename(filepath)
                # Parse filename: broker_symbol_type_timestamp.png
                parts = filename.replace('.png', '').split('_')
                
                if len(parts) >= 4:
                    broker = parts[0]
                    symbol = parts[1]
                    detection_type = parts[2]
                    timestamp_str = '_'.join(parts[3:])
                    
                    # Format display (thời gian từ sàn/server time - không bị convert sang GMT+7)
                    try:
                        dt = datetime.strptime(timestamp_str, '%Y%m%d_%H%M%S')
                        time_str = dt.strftime('%Y-%m-%d %H:%M:%S')
                    except:
                        time_str = timestamp_str
                    
                    display = f"[Server] {time_str} | {broker} {symbol} | {detection_type.upper()}"
                    self.image_listbox.insert(tk.END, display)
                else:
                    # Fallback
                    self.image_listbox.insert(tk.END, filename)
            
            # Update info
            total = len(image_files)
            shown = len(filtered_files)
            self.info_label.config(text=f"Total: {total} screenshots | Shown: {shown}")
            
        except Exception as e:
            logger.error(f"Error loading pictures: {e}", exc_info=True)
            self.info_label.config(text=f"Error loading pictures: {str(e)}")
    
    def on_image_select(self, event):
        """Handle image selection"""
        try:
            selection = self.image_listbox.curselection()
            if not selection:
                return
            
            index = selection[0]
            
            # Get all files again (same filtering)
            folder = screenshot_settings['folder']
            pattern = os.path.join(folder, "*.png")
            image_files = glob.glob(pattern)
            image_files.sort(key=lambda x: os.path.getmtime(x), reverse=True)
            
            # Filter images (same logic as load_pictures)
            filter_type = self.filter_type_var.get()
            filter_broker = self.filter_broker_var.get()
            
            filtered_files = []
            for filepath in image_files:
                filename = os.path.basename(filepath)
                
                if filter_type != "All":
                    if f"_{filter_type}_" not in filename:
                        continue
                
                if filter_broker != "All":
                    if not filename.startswith(filter_broker + "_"):
                        continue
                
                filtered_files.append(filepath)
            
            if index < len(filtered_files):
                filepath = filtered_files[index]
                self.display_image(filepath)
        
        except Exception as e:
            logger.error(f"Error selecting image: {e}")
    
    def on_assigned_name_change(self, event=None):
        """Persist assigned name selection"""
        try:
            selected_name = self.assigned_name_var.get()
            screenshot_settings['assigned_name'] = selected_name
            save_screenshot_settings()
            logger.info(f"Updated Picture Gallery assignee: {selected_name}")
        except Exception as e:
            logger.error(f"Error saving assigned name: {e}")

    def display_image(self, filepath):
        """Display selected image"""
        try:
            self.current_image_path = filepath
            
            # Load image
            img = Image.open(filepath)
            
            # Resize to fit canvas
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            
            if canvas_width < 10:  # Canvas not yet rendered
                canvas_width = 800
                canvas_height = 600
            
            # Calculate resize ratio
            img_width, img_height = img.size
            ratio = min(canvas_width / img_width, canvas_height / img_height)
            
            new_width = int(img_width * ratio * 0.95)
            new_height = int(img_height * ratio * 0.95)
            
            img_resized = img.resize((new_width, new_height), Image.Resampling.LANCZOS)
            
            # Convert to PhotoImage
            self.current_image = ImageTk.PhotoImage(img_resized)
            
            # Display on canvas
            self.canvas.delete("all")
            self.canvas.create_image(canvas_width // 2, canvas_height // 2,
                                    image=self.current_image, anchor=tk.CENTER)
            
        except Exception as e:
            logger.error(f"Error displaying image: {e}")
            self.canvas.delete("all")
            self.canvas.create_text(400, 300, text=f"Error loading image:\n{str(e)}",
                                   fill='red', font=('Arial', 12))
    
    def delete_selected(self):
        """Delete selected screenshot - NO CONFIRM (direct delete)"""
        try:
            if not self.current_image_path:
                # No warning, just ignore if nothing selected
                return
            
            # Get current selection index
            current_selection = self.image_listbox.curselection()
            current_index = current_selection[0] if current_selection else 0
            
            # Delete file directly - NO CONFIRM
            os.remove(self.current_image_path)
            logger.info(f"Deleted screenshot: {self.current_image_path}")
            
            # Clear display
            self.canvas.delete("all")
            self.current_image = None
            self.current_image_path = None
            
            # Reload list
            self.load_pictures()
            
            # Auto-select next image (or previous if last was deleted)
            total_items = self.image_listbox.size()
            if total_items > 0:
                # If current index still exists, select it (next image took its place)
                # Otherwise select last item
                new_index = min(current_index, total_items - 1)
                self.image_listbox.selection_clear(0, tk.END)
                self.image_listbox.selection_set(new_index)
                self.image_listbox.activate(new_index)
                self.image_listbox.see(new_index)
                # Trigger selection event to display the image
                self.on_image_select(None)
            else:
                # No more images
                self.info_label.config(text="Không còn screenshot nào")
        
        except Exception as e:
            logger.error(f"Error deleting image: {e}")
            # Show error but keep focus on this window
            messagebox.showerror("Lỗi", f"Không thể xóa hình: {str(e)}")
            # Re-grab focus after messagebox
            self.window.grab_set()
            self.window.focus_force()
    
    def accept_screenshot(self):
        """Accept current screenshot and add to list for Google Sheets"""
        try:
            if not self.current_image_path:
                return  # No image selected
            
            # Parse filename to extract info
            filename = os.path.basename(self.current_image_path)
            # Filename format: BROKER_SYMBOL_gap_2024-01-01_12-30-45.png
            
            parts = filename.replace('.png', '').split('_')
            if len(parts) < 3:
                messagebox.showwarning("Cảnh báo", "Không thể phân tích tên file")
                self.window.grab_set()
                return
            
            broker = parts[0]
            symbol = parts[1]
            detection_type = parts[2]  # gap, spike, or both
            
            # Load metadata saved during screenshot capture (if available)
            metadata = {}
            metadata_path = os.path.splitext(self.current_image_path)[0] + '.json'
            if os.path.exists(metadata_path):
                try:
                    with open(metadata_path, 'r', encoding='utf-8') as meta_file:
                        metadata = json.load(meta_file) or {}
                except Exception as meta_err:
                    logger.error(f"Error loading screenshot metadata: {meta_err}")
                    metadata = {}

            # Determine detection type (metadata overrides filename if available)
            detection_type = metadata.get('detection_type', detection_type).lower()

            # Server time string
            server_time = metadata.get('server_time', 'N/A')
            server_timestamp = metadata.get('server_timestamp')

            if server_time == 'N/A':
                timestamp_candidate = '_'.join(parts[3:]) if len(parts) > 3 else ''
                parsed = False
                if timestamp_candidate:
                    for fmt in ['%Y%m%d_%H%M%S', '%Y%m%d%H%M%S', '%Y-%m-%d_%H-%M-%S', '%Y-%m-%d_%H%M%S']:
                        try:
                            dt_from_filename = datetime.strptime(timestamp_candidate, fmt)
                            server_time = dt_from_filename.strftime('%Y-%m-%d %H:%M:%S')
                            parsed = True
                            break
                        except ValueError:
                            continue
                if not parsed:
                    server_time = 'N/A'

            # Pull detection metrics from metadata or fallback to current alert data
            gap_meta = metadata.get('gap') or {}
            spike_meta = metadata.get('spike') or {}

            result_key = f"{broker}_{symbol}"
            needs_gap_fallback = not gap_meta or ('percentage' not in gap_meta and 'message' not in gap_meta)
            needs_spike_fallback = not spike_meta or ('strength' not in spike_meta and 'message' not in spike_meta)

            if needs_gap_fallback or needs_spike_fallback or (server_time == 'N/A' and server_timestamp is None):
                with data_lock:
                    fallback_result = gap_spike_results.get(result_key)
                if fallback_result:
                    if needs_gap_fallback:
                        gap_meta = (fallback_result.get('gap') or {}).copy()
                    if needs_spike_fallback:
                        spike_meta = (fallback_result.get('spike') or {}).copy()
                    if server_time == 'N/A' and fallback_result.get('timestamp'):
                        dt_from_result = server_timestamp_to_datetime(fallback_result['timestamp'])
                        server_time = dt_from_result.strftime('%Y-%m-%d %H:%M:%S')
                    if server_timestamp is None and fallback_result.get('timestamp') is not None:
                        server_timestamp = fallback_result['timestamp']

            def _format_percentage(prefix: str, value):
                try:
                    if value is None:
                        return ''
                    value_float = float(value)
                    return f"{prefix}: {value_float:.3f}%"
                except (TypeError, ValueError):
                    return f"{prefix}: {value}" if value not in (None, '') else ''

            percentage_parts = []

            gap_percentage_display = ''
            gap_percentage_value = gap_meta.get('percentage') if isinstance(gap_meta, dict) else None
            if gap_percentage_value is None and isinstance(gap_meta, dict):
                gap_percentage_value = gap_meta.get('strength')
            if detection_type in ('gap', 'both') and gap_percentage_value is not None:
                gap_percentage_display = _format_percentage('Gap', gap_percentage_value)
                if gap_percentage_display:
                    percentage_parts.append(gap_percentage_display)

            spike_percentage_display = ''
            spike_percentage_value = None
            if isinstance(spike_meta, dict):
                spike_percentage_value = spike_meta.get('strength')
                if spike_percentage_value is None:
                    spike_percentage_value = spike_meta.get('percentage')
            if detection_type in ('spike', 'both') and spike_percentage_value is not None:
                spike_percentage_display = _format_percentage('Spike', spike_percentage_value)
                if spike_percentage_display:
                    percentage_parts.append(spike_percentage_display)

            percentage_display = ' | '.join([part for part in percentage_parts if part])

            gap_info_text = ''
            if isinstance(gap_meta, dict):
                gap_info_text = gap_meta.get('message') or gap_percentage_display

            spike_info_text = ''
            if isinstance(spike_meta, dict):
                spike_info_text = spike_meta.get('message') or spike_percentage_display
            
            assigned_name = self.assigned_name_var.get().strip() if hasattr(self, 'assigned_name_var') else ''

            def _format_value(value):
                try:
                    return f"{float(value):.3f}%"
                except (TypeError, ValueError):
                    return str(value) if value not in (None, '') else ''

            sheet_percentage = ''
            if detection_type == 'gap':
                if gap_percentage_value is not None:
                    sheet_percentage = _format_value(gap_percentage_value)
            elif detection_type == 'spike':
                if spike_percentage_value is not None:
                    sheet_percentage = _format_value(spike_percentage_value)
            else:  # both
                sheet_parts = []
                if gap_percentage_value is not None:
                    sheet_parts.append(f"Gap: {_format_value(gap_percentage_value)}")
                if spike_percentage_value is not None:
                    sheet_parts.append(f"Spike: {_format_value(spike_percentage_value)}")
                sheet_percentage = ' | '.join(sheet_parts)

            # Check if already accepted
            for item in self.accepted_screenshots:
                if item['filename'] == filename:
                    messagebox.showinfo("Thông báo", "Ảnh này đã được Accept rồi!")
                    self.window.grab_set()
                    return
            
            screenshot_data = {
                'server_time': server_time,
                'server_timestamp': server_timestamp,
                'broker': broker,
                'symbol': symbol,
                'detection_type': detection_type,
                'filename': filename,
                'percentage': sheet_percentage,
                'percentage_display': percentage_display,
                'gap_info': gap_info_text or '',
                'spike_info': spike_info_text or '',
                'gap_percentage': gap_percentage_value,
                'spike_percentage': spike_percentage_value,
                'assigned_name': assigned_name
            }
            
            # Add to accepted list
            self.accepted_screenshots.append(screenshot_data)
            
            # Update display
            self.update_accepted_display()
            
            logger.info(f"Accepted screenshot: {filename}")
            
            # Auto-move to next image
            current_selection = self.image_listbox.curselection()
            if current_selection:
                current_index = current_selection[0]
                total_items = self.image_listbox.size()
                if current_index + 1 < total_items:
                    # Select next
                    self.image_listbox.selection_clear(0, tk.END)
                    self.image_listbox.selection_set(current_index + 1)
                    self.image_listbox.activate(current_index + 1)
                    self.image_listbox.see(current_index + 1)
                    self.on_image_select(None)
        
        except Exception as e:
            logger.error(f"Error accepting screenshot: {e}")
            messagebox.showerror("Lỗi", f"Không thể accept: {str(e)}")
            self.window.grab_set()
    
    def update_accepted_display(self):
        """Update accepted screenshots listbox"""
        try:
            # Clear listbox
            self.accepted_listbox.delete(0, tk.END)
            
            # Add all accepted items
            for item in self.accepted_screenshots:
                server_time = item.get('server_time', 'N/A')
                broker = item.get('broker', '')
                symbol = item.get('symbol', '')
                detection = item.get('detection_type', '').upper()
                percentage_text = item.get('percentage_display', item.get('percentage', ''))
                assigned_name = item.get('assigned_name', '')

                display_text = f"{server_time} | {broker} {symbol} | {detection}"
                if percentage_text:
                    display_text += f" | {percentage_text}"
                if assigned_name:
                    display_text += f" | Người: {assigned_name}"
                self.accepted_listbox.insert(tk.END, display_text)
            
            # Update count
            count = len(self.accepted_screenshots)
            self.accepted_count_label.config(text=f"Accepted: {count}")
            
        except Exception as e:
            logger.error(f"Error updating accepted display: {e}")
    
    def clear_accepted(self):
        """Clear all accepted screenshots"""
        if not self.accepted_screenshots:
            return
        
        self.accepted_screenshots.clear()
        self.update_accepted_display()
        logger.info("Cleared accepted screenshots")
    
    def complete_and_send(self):
        """Send all accepted screenshots to Google Sheets"""
        try:
            if not self.accepted_screenshots:
                messagebox.showinfo("Thông báo", "Chưa có ảnh nào được Accept!\n\nHãy click 'Accept' hoặc nhấn Enter trên các ảnh muốn gửi.")
                self.window.grab_set()
                return
            
            # Confirm
            count = len(self.accepted_screenshots)
            confirm = messagebox.askyesno("Xác nhận", 
                                         f"Gửi {count} ảnh lên Google Sheets:\n\n'{GOOGLE_SHEET_NAME}'?\n\n"
                                         f"Sau khi gửi thành công, list sẽ được xóa.")
            
            if not confirm:
                self.window.grab_set()
                return
            
            # Show progress
            self.info_label.config(text="⏳ Đang gửi lên Google Sheets...")
            self.window.update()
            
            # Push to Google Sheets
            success, message = push_to_google_sheets(self.accepted_screenshots)
            
            if success:
                messagebox.showinfo("Thành công", message)
                # Clear accepted list after successful send
                self.clear_accepted()
            else:
                messagebox.showerror("Lỗi", message)
            
            self.info_label.config(text="")
            self.window.grab_set()
            self.window.focus_force()
        
        except Exception as e:
            logger.error(f"Error sending to Google Sheets: {e}")
            messagebox.showerror("Lỗi", f"Không thể gửi: {str(e)}")
            self.info_label.config(text="")
            self.window.grab_set()
            self.window.focus_force()
    
    def open_pictures_folder(self):
        """Open pictures folder in file explorer"""
        try:
            folder = screenshot_settings['folder']
            if not os.path.exists(folder):
                os.makedirs(folder)
            
            # Open folder in explorer
            if os.name == 'nt':  # Windows
                os.startfile(folder)
            elif os.name == 'posix':  # macOS/Linux
                os.system(f'open "{folder}"' if sys.platform == 'darwin' else f'xdg-open "{folder}"')
        
        except Exception as e:
            logger.error(f"Error opening folder: {e}")
            messagebox.showerror("Error", f"Failed to open folder: {str(e)}")

# ===================== CONNECTED BROKERS WINDOW =====================
class ConnectedBrokersWindow:
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("Connected Brokers")
        self.window.geometry("800x400")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Top Frame
        top_frame = ttk.Frame(self.window, padding="10")
        top_frame.pack(fill=tk.X)
        
        ttk.Label(top_frame, text="🔌 Connected Brokers", font=('Arial', 14, 'bold')).pack(side=tk.LEFT, padx=10)
        
        # Refresh button
        ttk.Button(top_frame, text="🔄 Refresh", command=self.update_display).pack(side=tk.LEFT, padx=5)
        
        # Main Table Frame
        table_frame = ttk.LabelFrame(self.window, text="Broker Status", padding="10")
        table_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create Treeview
        columns = ('Broker', 'Symbols', 'Last Update', 'Status')
        self.tree = ttk.Treeview(table_frame, columns=columns, show='headings', height=15)
        
        self.tree.heading('Broker', text='Broker Name')
        self.tree.heading('Symbols', text='Symbols')
        self.tree.heading('Last Update', text='Last Update')
        self.tree.heading('Status', text='Status')
        
        self.tree.column('Broker', width=250)
        self.tree.column('Symbols', width=100)
        self.tree.column('Last Update', width=200)
        self.tree.column('Status', width=150)
        
        # Scrollbar
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Tags for status
        self.tree.tag_configure('connected', background='#ccffcc')
        self.tree.tag_configure('disconnected', background='#ffcccc')
        
        # Initial display
        self.update_display()
        
        # Auto-refresh every 5 seconds
        self.auto_refresh()
    
    def update_display(self):
        """Cập nhật hiển thị brokers với connection status"""
        try:
            with data_lock:
                # Clear existing items
                for item in self.tree.get_children():
                    self.tree.delete(item)
                
                # Get broker info from market_data
                current_time = time.time()
                connection_timeout = 20  # 20 seconds như yêu cầu
                broker_info = {}
                
                for broker, symbols in market_data.items():
                    symbol_count = len(symbols)
                    
                    # Check if ANY symbol is still updating (< 20s delay)
                    has_active_symbol = False
                    latest_timestamp = 0
                    
                    for symbol_name in symbols.keys():
                        key = f"{broker}_{symbol_name}"
                        
                        # Check bid tracking
                        if key in bid_tracking:
                            last_change_time = bid_tracking[key]['last_change_time']
                            delay_duration = current_time - last_change_time
                            
                            if delay_duration < connection_timeout:
                                has_active_symbol = True
                            
                            if last_change_time > latest_timestamp:
                                latest_timestamp = last_change_time
                        
                        # Also check regular timestamp
                        symbol_data = symbols[symbol_name]
                        ts = symbol_data.get('timestamp', 0)
                        if ts > latest_timestamp:
                            latest_timestamp = ts
                    
                    # Broker is connected if at least 1 symbol is active
                    is_connected = has_active_symbol
                    age = current_time - latest_timestamp if latest_timestamp > 0 else 999999
                    
                    broker_info[broker] = {
                        'symbols': symbol_count,
                        'timestamp': latest_timestamp,
                        'connected': is_connected,
                        'age': age
                    }
                
                # Add brokers to tree
                for broker, info in sorted(broker_info.items()):
                    symbols = info['symbols']
                    timestamp = info['timestamp']
                    connected = info['connected']
                    age = info['age']
                    
                    if timestamp > 0:
                        last_update = server_timestamp_to_datetime(timestamp).strftime('%H:%M:%S')
                        if age < 60:
                            age_str = f"{int(age)}s ago"
                        else:
                            age_str = f"{int(age/60)}m ago"
                        last_update_str = f"{last_update} ({age_str})"
                    else:
                        last_update_str = "Never"
                    
                    status = "🟢 Connected" if connected else "🔴 Disconnected"
                    tag = 'connected' if connected else 'disconnected'
                    
                    self.tree.insert('', 'end', values=(
                        broker,
                        symbols,
                        last_update_str,
                        status
                    ), tags=(tag,))
                
                # If no brokers, show message
                if not broker_info:
                    self.tree.insert('', 'end', values=(
                        'No brokers connected',
                        '-',
                        '-',
                        '⚠️ Waiting...'
                    ))
                    
        except Exception as e:
            logger.error(f"Error updating connected brokers display: {e}")
    
    def auto_refresh(self):
        """Auto refresh every 5 seconds"""
        if self.window.winfo_exists():
            self.update_display()
            self.window.after(5000, self.auto_refresh)

# ===================== TRADING HOURS WINDOW =====================
class TradingHoursWindow:
    def __init__(self, parent, main_app):
        self.main_app = main_app
        self.window = tk.Toplevel(parent)
        self.window.title("Trading Hours - All Symbols")
        self.window.geometry("1200x700")
        
        # Make window modal - chặn thao tác cửa sổ parent
        self.window.transient(parent)  # Window luôn nằm trên parent
        self.window.grab_set()  # Chặn input đến parent window
        
        self.window.lift()  # Đưa cửa sổ lên trên
        self.window.focus_force()  # Focus vào cửa sổ
        
        # Top Frame
        top_frame = ttk.Frame(self.window, padding="10")
        top_frame.pack(fill=tk.X)
        
        ttk.Label(top_frame, text="📅 Trading Hours Status", font=('Arial', 14, 'bold')).pack(side=tk.LEFT, padx=10)
        
        # Filter by broker
        ttk.Label(top_frame, text="Broker:").pack(side=tk.LEFT, padx=5)
        self.broker_filter = ttk.Combobox(top_frame, width=20, state='readonly')
        self.broker_filter.pack(side=tk.LEFT, padx=5)
        self.broker_filter.bind('<<ComboboxSelected>>', lambda e: self.update_display())
        
        # Refresh button
        ttk.Button(top_frame, text="🔄 Refresh", command=self.update_display).pack(side=tk.LEFT, padx=5)
        
        # Status label
        self.status_label = ttk.Label(top_frame, text="", font=('Arial', 9))
        self.status_label.pack(side=tk.LEFT, padx=20)
        
        # Main Table Frame
        table_frame = ttk.LabelFrame(self.window, text="Trading Sessions", padding="10")
        table_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create Treeview
        columns = ('Broker', 'Symbol', 'Status', 'Current Day', 'Current Time', 'Active Session', 'All Sessions')
        self.tree = ttk.Treeview(table_frame, columns=columns, show='headings', height=25)
        
        # Column headings
        self.tree.heading('Broker', text='Broker')
        self.tree.heading('Symbol', text='Symbol')
        self.tree.heading('Status', text='Trading Status')
        self.tree.heading('Current Day', text='Current Day')
        self.tree.heading('Current Time', text='Current Time')
        self.tree.heading('Active Session', text='Active Session')
        self.tree.heading('All Sessions', text='All Sessions Today')
        
        # Column widths
        self.tree.column('Broker', width=150)
        self.tree.column('Symbol', width=100)
        self.tree.column('Status', width=120)
        self.tree.column('Current Day', width=100)
        self.tree.column('Current Time', width=100)
        self.tree.column('Active Session', width=150)
        self.tree.column('All Sessions', width=400)
        
        # Scrollbars
        vsb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(table_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        self.tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        hsb.grid(row=1, column=0, sticky='ew')
        
        table_frame.grid_rowconfigure(0, weight=1)
        table_frame.grid_columnconfigure(0, weight=1)
        
        # Tags for colors
        self.tree.tag_configure('open', background='#ccffcc')  # Green - Trading
        self.tree.tag_configure('closed', background='#ffcccc')  # Red - Not trading
        self.tree.tag_configure('unknown', background='#f0f0f0')  # Gray - Unknown
        
        # Legend Frame
        legend_frame = ttk.Frame(self.window, padding="10")
        legend_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(legend_frame, text="Legend:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=5)
        
        green_label = ttk.Label(legend_frame, text="  🟢 Trading  ", background='#ccffcc', relief='solid', borderwidth=1)
        green_label.pack(side=tk.LEFT, padx=5)
        
        red_label = ttk.Label(legend_frame, text="  🔴 Closed  ", background='#ffcccc', relief='solid', borderwidth=1)
        red_label.pack(side=tk.LEFT, padx=5)
        
        gray_label = ttk.Label(legend_frame, text="  ⚪ Unknown  ", background='#f0f0f0', relief='solid', borderwidth=1)
        gray_label.pack(side=tk.LEFT, padx=5)
        
        # Initial display
        self.update_display()
        
        # Auto-refresh every 5 seconds
        self.auto_refresh()
    
    def check_if_trading_now(self, trade_sessions):
        """
        Kiểm tra xem hiện tại có trong giờ giao dịch không
        Returns: (is_trading, current_session, all_sessions_today)
        """
        if not trade_sessions or not isinstance(trade_sessions, dict):
            return False, None, []
        
        current_day_name = trade_sessions.get('current_day', '')
        days_data = trade_sessions.get('days', [])
        
        # Lấy thời gian hiện tại
        now = datetime.now()
        current_time_minutes = now.hour * 60 + now.minute
        
        # Tìm phiên giao dịch của ngày hiện tại
        today_sessions = []
        for day_info in days_data:
            if day_info.get('day') == current_day_name:
                today_sessions = day_info.get('sessions', [])
                break
        
        if not today_sessions:
            return False, None, []
        
        # Kiểm tra xem có trong session nào không
        for session in today_sessions:
            start_str = session.get('start', '')
            end_str = session.get('end', '')
            
            if not start_str or not end_str:
                continue
            
            # Parse start time
            start_parts = start_str.split(':')
            start_minutes = int(start_parts[0]) * 60 + int(start_parts[1])
            
            # Parse end time
            end_parts = end_str.split(':')
            end_minutes = int(end_parts[0]) * 60 + int(end_parts[1])
            
            # Kiểm tra xem current time có trong session không
            if start_minutes == end_minutes:
                # 24/7 trading
                return True, f"{start_str}-{end_str} (24/7)", today_sessions
            elif start_minutes < end_minutes:
                # Normal session (same day)
                if start_minutes <= current_time_minutes < end_minutes:
                    return True, f"{start_str}-{end_str}", today_sessions
            else:
                # Overnight session
                if start_minutes <= current_time_minutes or current_time_minutes < end_minutes:
                    return True, f"{start_str}-{end_str}", today_sessions
        
        return False, None, today_sessions
    
    def format_sessions_list(self, sessions):
        """Format danh sách sessions thành string"""
        if not sessions:
            return "No sessions"
        
        session_strs = []
        for session in sessions:
            start = session.get('start', '')
            end = session.get('end', '')
            if start and end:
                session_strs.append(f"{start}-{end}")
        
        return ", ".join(session_strs) if session_strs else "No sessions"
    
    def update_display(self):
        """Cập nhật hiển thị trading hours"""
        try:
            with data_lock:
                # Clear existing items
                for item in self.tree.get_children():
                    self.tree.delete(item)
                
                # Update broker filter
                broker_list = ['All'] + sorted(market_data.keys())
                self.broker_filter['values'] = broker_list
                if not self.broker_filter.get():
                    self.broker_filter.set('All')
                
                selected_broker = self.broker_filter.get()
                
                # Get current time
                now = datetime.now()
                current_time_str = now.strftime('%H:%M:%S')
                current_day_name = now.strftime('%A')
                
                # Statistics
                total_symbols = 0
                trading_count = 0
                closed_count = 0
                
                # Sort by broker, then symbol
                for broker in sorted(market_data.keys()):
                    if selected_broker != 'All' and broker != selected_broker:
                        continue
                    
                    symbols_dict = market_data[broker]
                    
                    for symbol in sorted(symbols_dict.keys()):
                        symbol_data = symbols_dict[symbol]
                        trade_sessions = symbol_data.get('trade_sessions', {})
                        
                        # Check if trading now
                        is_trading, active_session, all_sessions = self.check_if_trading_now(trade_sessions)
                        
                        total_symbols += 1
                        if is_trading:
                            trading_count += 1
                            status = "🟢 TRADING"
                            tag = 'open'
                        else:
                            closed_count += 1
                            status = "🔴 CLOSED"
                            tag = 'closed'
                        
                        # Format session info
                        if active_session:
                            active_session_str = active_session
                        else:
                            active_session_str = "None"
                        
                        all_sessions_str = self.format_sessions_list(all_sessions)
                        
                        # Insert row
                        self.tree.insert('', 'end', values=(
                            broker,
                            symbol,
                            status,
                            current_day_name,
                            current_time_str,
                            active_session_str,
                            all_sessions_str
                        ), tags=(tag,))
                
                # Update status
                self.status_label.config(
                    text=f"Total: {total_symbols} | 🟢 Trading: {trading_count} | 🔴 Closed: {closed_count}"
                )
                
        except Exception as e:
            logger.error(f"Error updating trading hours display: {e}")
    
    def auto_refresh(self):
        """Auto refresh every 5 seconds"""
        if self.window.winfo_exists():
            self.update_display()
            self.window.after(5000, self.auto_refresh)

# ===================== MAIN APPLICATION =====================
def run_flask_server():
    """Chạy Flask server trong thread riêng"""
    try:
        app.run(host=HTTP_HOST, port=HTTP_PORT, debug=False, threaded=True)
    except Exception as e:
        logger.error(f"Error starting Flask server: {e}")

def main():
    """Main application entry point"""
    # Load settings
    load_gap_settings()
    load_spike_settings()
    load_manual_hidden_delays()
    load_audio_settings()
    load_symbol_filter_settings()
    load_delay_settings()
    load_screenshot_settings()
    load_market_open_settings()
    load_auto_send_settings()
    load_python_reset_settings()
    
    # Ensure pictures folder exists
    ensure_pictures_folder()
    
    # Start Flask server in background thread
    flask_thread = threading.Thread(target=run_flask_server, daemon=True)
    flask_thread.start()
    
    logger.info(f"Flask server started on http://{HTTP_HOST}:{HTTP_PORT}")
    logger.info(f"EA should send data to: http://127.0.0.1:{HTTP_PORT}/api/receive_data")
    
    # Start GUI
    root = tk.Tk()
    app_gui = GapSpikeDetectorGUI(root)
    
    # Log initial message
    app_gui.log(f"Server started on port {HTTP_PORT}")
    app_gui.log(f"Loaded {len(gap_settings)} gap settings, {len(spike_settings)} spike settings")
    app_gui.log("Waiting for data from MT4/MT5 EA...")
    
    # Run GUI main loop
    root.mainloop()

if __name__ == '__main__':
    main()

