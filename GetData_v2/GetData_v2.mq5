//+------------------------------------------------------------------+
//|                                              Get_Data_V1.mq5     |
//|                     Converted from MQL4 to MQL5                  |
//+------------------------------------------------------------------+
#property copyright "9/10/2025"
#property version   "Get_Data V2 - gap spike"
#property strict

#include <Trade/Trade.mqh>
CTrade trade;

struct Section_Trade
{
   datetime str_start_time;
   datetime str_finish_time;
};
struct Section_Trade_Ngay_Trong_Tuan
{
   Section_Trade str_arr_Section_Trade_Moi_Ngay[10];
   int str_Tong_Section_Trade_Moi_Ngay;//Tong sectioen trade moi ngay
};
Section_Trade_Ngay_Trong_Tuan glb_Section_Trade_Array[10];//CO 7 ngay tu : 0-6

input int SendInterval = 1;                  // Send interval (seconds)
input string glbStringFilePath = "web_url";  // File .txt chứa URL
input bool SendOnlyOpenMarkets = false;      // Chỉ gửi sản phẩm đang mở (false = gửi tất cả)
string WebServerURL = "";                    // URL sẽ được đọc từ file
datetime lastSendTime = 0;

string EscapeJsonString(string value)
{
   string result = value;
   StringReplace(result, "\\", "\\\\");
   StringReplace(result, "\"", "\\\"");
   return result;
}

string GetSymbolGroupPath(string symbol)
{
   string group_path = "";
#ifdef SYMBOL_PATH
   string tmp = "";
   if(SymbolInfoString(symbol, SYMBOL_PATH, tmp) && StringLen(tmp) > 0)
      group_path = tmp;
#endif

#ifdef SYMBOL_SECTOR
   if(group_path == "")
   {
      string sector = "";
      if(SymbolInfoString(symbol, SYMBOL_SECTOR, sector) && StringLen(sector) > 0)
         group_path = sector;
   }
#endif

   return group_path;
}

struct TradeSignal {
   string action;
   string symbol;
   string side;
   string comment;
   double volume;
   double sl_points;
   double tp_points;
   int    max_slippage;
   ulong  ticket;
};

//============================================================
// Hàm đọc URL từ file
bool ReadWebServerURL()
{
   int file_handle = FileOpen(glbStringFilePath + ".txt", FILE_READ | FILE_TXT | FILE_SHARE_READ | FILE_ANSI);
   if (file_handle == INVALID_HANDLE)
   {
      Print("Loi: Khong mo duoc file ", glbStringFilePath, ".txt ERR: ", GetLastError());
      return false;
   }   
   WebServerURL = FileReadString(file_handle);
   StringTrimLeft(WebServerURL); 
   StringTrimRight(WebServerURL);  
      
   FileClose(file_handle);   
   if (WebServerURL == "")
   {   
      Print("Loi: Thieu cau hinh trong file txt ", glbStringFilePath, ".txt");
      return false;
   }
   
   if (StringSubstr(WebServerURL, StringLen(WebServerURL) - 1) != "/")
      WebServerURL += "/";
      
   return true;
}

//============================================================
// Hàm gửi dữ liệu tới server
bool SendDataToWeb(string method, string url, string jsonData = "")
{
   string headers = "Content-Type: application/json\r\n";
   uchar post[], result[];
   string result_headers;
   int timeout = 3000;

   if (method == "POST" && (jsonData == "" || StringLen(jsonData) <= 2))
   {
      Print("Loi: JSON khong hop le");
      return false;
   }
   
   if (method == "POST")
   {
      // Fix: StringLen() instead of WHOLE_ARRAY to avoid null terminator
      int jsonLen = StringLen(jsonData);
      StringToCharArray(jsonData, post, 0, jsonLen, CP_UTF8);
   }

   int res = WebRequest(method, url, headers, timeout, post, result, result_headers);   
   if (res == -1)
   {
      Print("ERR WebRequest toi ", url, " ERR: ", GetLastError(), " Headers: ", result_headers);
      return false;
   }
   else
   {
      return true;
   }
}

//============================================================
// Biến toàn cục để lưu phản hồi GET
string global_last_response = "";

//============================================================
// Hàm lấy dữ liệu Market Watch
string GetMarketWatchData()
{
   if (!ReadWebServerURL()) return "";

   string jsonData = "{";
   int totalSymbols = SymbolsTotal(true);
   bool first = true;

   string symbolsData = "[";
   string brokerServer = AccountInfoString(ACCOUNT_SERVER);

   for (int i = 0; i < totalSymbols; i++)
   {
      string symbol = SymbolName(i, true);
      double bid, ask;
      int digits = (int)SymbolInfoInteger(symbol, SYMBOL_DIGITS);

      if(!SymbolInfoDouble(symbol, SYMBOL_BID, bid)) continue;
      if(!SymbolInfoDouble(symbol, SYMBOL_ASK, ask)) continue;
      double point_value = SymbolInfoDouble(symbol, SYMBOL_POINT);    
      bool isOpen = FunCheckMartKetOpenMotCapTien(symbol);     

      // Lấy OHLC của nến M1 trước đó và nến hiện tại
      MqlRates rates[];
      ArraySetAsSeries(rates, true);
      
      double prev_open = 0, prev_high = 0, prev_low = 0, prev_close = 0;
      double current_open = 0, current_high = 0, current_low = 0, current_close = 0;
      
      // Copy 2 nến gần nhất (0 = hiện tại, 1 = trước đó)
      if(CopyRates(symbol, PERIOD_M1, 0, 2, rates) == 2)
      {
         // Nến trước đó (index 1)
         prev_open = rates[1].open;
         prev_high = rates[1].high;
         prev_low = rates[1].low;
         prev_close = rates[1].close;
         
         // Nến hiện tại (index 0)
         current_open = rates[0].open;
         current_high = rates[0].high;
         current_low = rates[0].low;
         current_close = rates[0].close;
      }
      
      // Lấy thông tin trade sessions
      string tradeSessions = GetTradeSessionsJSON(symbol);

      string groupPathRaw = GetSymbolGroupPath(symbol);
      string groupPathJson = EscapeJsonString(groupPathRaw);

      string symbolData = StringFormat(
         "{\"symbol\":\"%s\",\"group\":\"%s\",\"bid\":%.5f,\"ask\":%.5f,\"digits\":%d,\"points\":%.5f,\"isOpen\":%s," +
         "\"prev_ohlc\":{\"open\":%.5f,\"high\":%.5f,\"low\":%.5f,\"close\":%.5f}," +
         "\"current_ohlc\":{\"open\":%.5f,\"high\":%.5f,\"low\":%.5f,\"close\":%.5f}," +
         "\"trade_sessions\":%s}",
         symbol, groupPathJson,
         bid, ask, digits, point_value,
         isOpen ? "true" : "false",
         prev_open, prev_high, prev_low, prev_close,
         current_open, current_high, current_low, current_close,
         tradeSessions
      );      

      if (SendOnlyOpenMarkets && !isOpen) continue;

      if (!first) symbolsData += ",";
      symbolsData += symbolData;
      first = false;
   }

   symbolsData += "]";
   jsonData += StringFormat("\"timestamp\":%lld,", TimeCurrent());   
   jsonData += StringFormat("\"broker\":\"%s\",", brokerServer);
   jsonData += "\"data\":" + symbolsData;
   jsonData += "}";
   
   return jsonData;
}
//============================================================
// Hàm kiểm tra phiên giao dịch
bool FunCheckMartKetOpenMotCapTien(string symbol)
{
    MqlDateTime Curent_time;
    TimeCurrent(Curent_time);
    int day_of_week=Curent_time.day_of_week;
    int curent_time_second=Curent_time.hour*3600+Curent_time.min*60+Curent_time.sec;
    int start_time_second,finish_time_second;
    
    Section_Trade_Ngay_Trong_Tuan Section_Trade_Array_Mot_Cap_Tien[10];
    FunGetSectionTradeArrayMotCapTien(symbol,Section_Trade_Array_Mot_Cap_Tien);
    int tong_section_trade_hom_nay=Section_Trade_Array_Mot_Cap_Tien[day_of_week].str_Tong_Section_Trade_Moi_Ngay;
    for (int i = 0; i < tong_section_trade_hom_nay; i++)
    {
        MqlDateTime temp_time;
        long distant_Current_second=0;
        long distant_finish_second=0;
        // Print("Curtime: ", Curent_time.hour, ":",Curent_time.min, ":", Curent_time.sec);
        // Print("Open time: ",Section_Trade_Array_Mot_Cap_Tien[day_of_week].str_arr_Section_Trade_Moi_Ngay[i].str_start_time, " Close time: ",Section_Trade_Array_Mot_Cap_Tien[day_of_week].str_arr_Section_Trade_Moi_Ngay[i].str_finish_time);
        start_time_second=0;finish_time_second=0;
        
        TimeToStruct(Section_Trade_Array_Mot_Cap_Tien[day_of_week].str_arr_Section_Trade_Moi_Ngay[i].str_start_time,temp_time);
        start_time_second=temp_time.hour*3600+temp_time.min*60+temp_time.sec;
        TimeToStruct(Section_Trade_Array_Mot_Cap_Tien[day_of_week].str_arr_Section_Trade_Moi_Ngay[i].str_finish_time,temp_time);
        finish_time_second=temp_time.hour*3600+temp_time.min*60+temp_time.sec;
        
        if(start_time_second==finish_time_second)
        {
            return true;//Thi truogn chayj 24/24
        }
        else if(start_time_second<finish_time_second)
        {
            if(start_time_second<=curent_time_second && curent_time_second<finish_time_second)
            return true;
        }
        else
        {
            if(start_time_second<=curent_time_second || curent_time_second<finish_time_second)
            return true;
        }
    }
    return false;

}

//============================================================
// Hàm lấy phiên giao dịch
void FunGetSectionTradeArrayMotCapTien(string _symbol, Section_Trade_Ngay_Trong_Tuan &_Section_Trade_Array[])
{
    MqlDateTime current_time;
    TimeCurrent(current_time);
    //ENUM_DAY_OF_WEEK day_of_week=(ENUM_DAY_OF_WEEK)current_time.day_of_week;
   for (int day_of_week = 0; day_of_week < 7; day_of_week++)
   {
      _Section_Trade_Array[day_of_week].str_Tong_Section_Trade_Moi_Ngay=0;
      for (int i = 0; i < 5; i++)
      {
         Section_Trade Tam;
         Tam.str_finish_time=0;
         Tam.str_start_time=0;
         SymbolInfoSessionTrade(_symbol,(ENUM_DAY_OF_WEEK) day_of_week,i,Tam.str_start_time, Tam.str_finish_time);
         //Print("Day off week: ", day_of_week, " str_finish_time ",Tam.str_start_time, " str_finish_time: ",Tam.str_finish_time );
         if(Tam.str_finish_time!=Tam.str_start_time)
         {
            
            _Section_Trade_Array[day_of_week].str_arr_Section_Trade_Moi_Ngay[_Section_Trade_Array[day_of_week].str_Tong_Section_Trade_Moi_Ngay]=Tam;
            _Section_Trade_Array[day_of_week].str_Tong_Section_Trade_Moi_Ngay++;
         }
      }
   }
}

//============================================================
// Hàm tạo JSON cho trade sessions
string GetTradeSessionsJSON(string symbol)
{
   Section_Trade_Ngay_Trong_Tuan Section_Trade_Array[10];
   FunGetSectionTradeArrayMotCapTien(symbol, Section_Trade_Array);
   
   MqlDateTime current_time;
   TimeCurrent(current_time);
   int today = current_time.day_of_week;
   
   string days[] = {"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"};
   
   string json = "{";
   json += "\"current_day\":\"" + days[today] + "\",";
   json += "\"days\":[";
   
   bool first_day = true;
   for (int day = 0; day < 7; day++)
   {
      int total_sessions = Section_Trade_Array[day].str_Tong_Section_Trade_Moi_Ngay;
      
      if (total_sessions > 0)
      {
         if (!first_day) json += ",";
         first_day = false;
         
         json += "{\"day\":\"" + days[day] + "\",\"sessions\":[";
         
         for (int i = 0; i < total_sessions; i++)
         {
            MqlDateTime start_time, end_time;
            TimeToStruct(Section_Trade_Array[day].str_arr_Section_Trade_Moi_Ngay[i].str_start_time, start_time);
            TimeToStruct(Section_Trade_Array[day].str_arr_Section_Trade_Moi_Ngay[i].str_finish_time, end_time);
            
            if (i > 0) json += ",";
            
            json += StringFormat("{\"start\":\"%02d:%02d\",\"end\":\"%02d:%02d\"}", 
                               start_time.hour, start_time.min,
                               end_time.hour, end_time.min);
         }
         
         json += "]}";
      }
   }
   
   json += "]}";
   return json;
}

//============================================================
// Hàm lấy dữ liệu positions
string GetPositionsData()
{
   if (!ReadWebServerURL()) 
   {
      //Print("[GetPositionsData] ERROR: Cannot read WebServerURL");
      return "";
   }

   string brokerServer = AccountInfoString(ACCOUNT_SERVER);
   
   //Print("[GetPositionsData] Start - Broker: ", brokerServer, " | PositionsTotal: ", PositionsTotal(), " | OrdersTotal: ", OrdersTotal());

   // ========== POSITIONS (Open Orders) ==========
   string posArr = "[";
   bool firstPos = true;
   int posTotal = PositionsTotal();
   
   for(int i = 0; i < posTotal; i++)
   {
      ulong ticket = PositionGetTicket(i);
      if(!PositionSelectByTicket(ticket)) continue;
      
      string symbol = PositionGetString(POSITION_SYMBOL);
      string side = (PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_BUY) ? "BUY" : "SELL";
      double volume = PositionGetDouble(POSITION_VOLUME);
      double price_open = PositionGetDouble(POSITION_PRICE_OPEN);
      double sl = PositionGetDouble(POSITION_SL);
      double tp = PositionGetDouble(POSITION_TP);
      double profit = PositionGetDouble(POSITION_PROFIT);
      long time_open = (long)PositionGetInteger(POSITION_TIME);
      
      string row = StringFormat(
         "{\"ticket\":%I64u,\"symbol\":\"%s\",\"side\":\"%s\",\"volume\":%.2f," +
         "\"price_open\":%.5f,\"sl\":%.5f,\"tp\":%.5f,\"profit\":%.2f,\"time\":%I64d}",
         ticket, symbol, side, volume, price_open, sl, tp, profit, time_open
      );
      
      if(!firstPos) posArr += ",";
      posArr += row;
      firstPos = false;
   }
   posArr += "]";
   
   // ========== PENDING ORDERS ==========
   string pendArr = "[";
   bool firstPend = true;
   int ordTotal = OrdersTotal();
   
   for(int i = 0; i < ordTotal; i++)
   {
      ulong ticket = OrderGetTicket(i);
      if(!OrderSelect(ticket)) continue;
      
      ENUM_ORDER_TYPE type = (ENUM_ORDER_TYPE)OrderGetInteger(ORDER_TYPE);
      
      // Bỏ qua market orders (đã có trong positions)
      if(type == ORDER_TYPE_BUY || type == ORDER_TYPE_SELL) continue;
      
      string symbol = OrderGetString(ORDER_SYMBOL);
      double volume = OrderGetDouble(ORDER_VOLUME_CURRENT);
      double price = OrderGetDouble(ORDER_PRICE_OPEN);
      double sl = OrderGetDouble(ORDER_SL);
      double tp = OrderGetDouble(ORDER_TP);
      long time_setup = (long)OrderGetInteger(ORDER_TIME_SETUP);
      
      string side = (type == ORDER_TYPE_BUY_LIMIT || 
                    type == ORDER_TYPE_BUY_STOP || 
                    type == ORDER_TYPE_BUY_STOP_LIMIT) ? "BUY" : "SELL";
      
      string typeName;
      switch(type) {
         case ORDER_TYPE_BUY_LIMIT:       typeName = "BUYLIMIT"; break;
         case ORDER_TYPE_SELL_LIMIT:      typeName = "SELLLIMIT"; break;
         case ORDER_TYPE_BUY_STOP:        typeName = "BUYSTOP"; break;
         case ORDER_TYPE_SELL_STOP:       typeName = "SELLSTOP"; break;
         case ORDER_TYPE_BUY_STOP_LIMIT:  typeName = "BUYSTOPLIMIT"; break;
         case ORDER_TYPE_SELL_STOP_LIMIT: typeName = "SELLSTOPLIMIT"; break;
         default: typeName = "PENDING";
      }
      
      string row = StringFormat(
         "{\"ticket\":%I64u,\"symbol\":\"%s\",\"side\":\"%s\",\"type\":\"%s\"," +
         "\"volume\":%.2f,\"price\":%.5f,\"sl\":%.5f,\"tp\":%.5f,\"time\":%I64d}",
         ticket, symbol, side, typeName, volume, price, sl, tp, time_setup
      );
      
      if(!firstPend) pendArr += ",";
      pendArr += row;
      firstPend = false;
   }
   pendArr += "]";
   
   // ========== JSON OUTPUT ==========
   string json = StringFormat(
      "{\"timestamp\":%lld,\"broker\":\"%s\",\"positions\":%s,\"pending\":%s}",
      TimeCurrent(), brokerServer, posArr, pendArr
   );
   
   //Print("[GetPositionsData] JSON Length: ", StringLen(json), " | Positions in array: ", posTotal, " | Pending: ", OrdersTotal());
   //Print("[GetPositionsData] JSON Preview (first 200 chars): ", StringSubstr(json, 0, 200));
   
   return json;
}

//============================================================
// Hàm xử lý TRADE
bool HandleTrade(TradeSignal &sig)
{
   if(sig.action != "TRADE") return false;

   ENUM_ORDER_TYPE type = (sig.side == "BUY") ? ORDER_TYPE_BUY : ORDER_TYPE_SELL;
   double price = (sig.side == "BUY") ? SymbolInfoDouble(sig.symbol, SYMBOL_ASK) : SymbolInfoDouble(sig.symbol, SYMBOL_BID);
   double point = SymbolInfoDouble(sig.symbol, SYMBOL_POINT);

   double sl = sig.sl_points > 0 ? ((sig.side == "BUY") ? price - sig.sl_points*point : price + sig.sl_points*point) : 0;
   double tp = sig.tp_points > 0 ? ((sig.side == "BUY") ? price + sig.tp_points*point : price - sig.tp_points*point) : 0;

   trade.SetDeviationInPoints(sig.max_slippage);

   bool ok = trade.PositionOpen(sig.symbol, type, sig.volume, price, sl, tp, sig.comment);

   string response;
   if(ok){
      ulong ticket = trade.ResultDeal();
      response = StringFormat("{\"ok\":true,\"ticket\":%d,\"symbol\":\"%s\",\"price\":%.5f,\"broker\":\"%s\"}",
                              ticket, sig.symbol, price, AccountInfoString(ACCOUNT_SERVER));
   } else {
      response = StringFormat("{\"ok\":false,\"error\":\"%d\",\"broker\":\"%s\"}",
                              GetLastError(), AccountInfoString(ACCOUNT_SERVER));
   }

   return SendDataToWeb("POST", WebServerURL + "api/send_trade_response", response);
}

//============================================================
// Hàm xử lý CLOSE
bool HandleClose(TradeSignal &sig)
{
   if(sig.action != "CLOSE") return false;

   // ✅ Tìm position theo ticket (chính xác hơn)
   bool positionFound = false;
   ulong ticket = sig.ticket;
   
   // Tìm position theo ticket
   for(int i = 0; i < PositionsTotal(); i++)
   {
      ulong posTicket = PositionGetTicket(i);
      if(posTicket == ticket)
      {
         if(PositionSelectByTicket(ticket))
         {
            positionFound = true;
            break;
         }
      }
   }
   
   if(!positionFound)
   {
      // Fallback: tìm theo symbol (nếu không có ticket)
      if(sig.symbol != "" && PositionSelect(sig.symbol))
      {
         positionFound = true;
         ticket = PositionGetInteger(POSITION_TICKET);
      }
   }

   if(positionFound)
   {
      string symbol = PositionGetString(POSITION_SYMBOL);
      double price = (PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_BUY) ? 
                     SymbolInfoDouble(symbol, SYMBOL_BID) : 
                     SymbolInfoDouble(symbol, SYMBOL_ASK);

      double lots = sig.volume > 0 ? sig.volume : PositionGetDouble(POSITION_VOLUME);
      
      // ✅ Sử dụng PositionClose() thay vì PositionClosePartial()
      bool res = trade.PositionClose(ticket);

      string response;
      if(res){
         response = StringFormat(
            "{\"ok\":true,\"ticket\":%d,\"symbol\":\"%s\",\"closed_volume\":%.2f,\"price\":%.5f,\"broker\":\"%s\"}", 
            ticket, symbol, lots, price, AccountInfoString(ACCOUNT_SERVER)
         );
         Print("✅ Position closed successfully: Ticket #", ticket, " Symbol: ", symbol);
      } else {
         response = StringFormat(
            "{\"ok\":false,\"error\":\"Close failed - %s\",\"broker\":\"%s\"}", 
            trade.ResultRetcodeDescription(), AccountInfoString(ACCOUNT_SERVER)
         );
         Print("❌ Position close failed: Ticket #", ticket, " Error: ", trade.ResultRetcodeDescription());
      }
      return SendDataToWeb("POST", WebServerURL + "api/send_close_response", response);
   }
   else
   {
      string response = StringFormat(
         "{\"ok\":false,\"error\":\"Position not found - Ticket: %d\",\"broker\":\"%s\"}", 
         sig.ticket, AccountInfoString(ACCOUNT_SERVER)
      );
      Print("❌ Position not found: Ticket #", sig.ticket);
      return SendDataToWeb("POST", WebServerURL + "api/send_close_response", response);
   }
}

//============================================================
// Hàm xử lý Cancel Pending Order
bool HandleCancelPending(TradeSignal &sig)
{
   if(sig.action != "CANCEL_PENDING") return false;
   if(sig.ticket <= 0) return false;
   
   if(!OrderSelect(sig.ticket))
   {
      string rErr = StringFormat(
         "{\"ok\":false,\"error\":\"order_not_found\",\"ticket\":%I64u,\"broker\":\"%s\"}",
         sig.ticket, AccountInfoString(ACCOUNT_SERVER)
      );
      SendDataToWeb("POST", WebServerURL + "api/send_cancel_pending_response", rErr);
      Print("❌ Order not found: Ticket #", sig.ticket);
      return false;
   }
   
   ENUM_ORDER_TYPE typ = (ENUM_ORDER_TYPE)OrderGetInteger(ORDER_TYPE);
   
   // Market orders (BUY/SELL) không được delete
   if(typ == ORDER_TYPE_BUY || typ == ORDER_TYPE_SELL)
   {
      string rBad = StringFormat(
         "{\"ok\":false,\"error\":\"not_pending\",\"ticket\":%I64u,\"broker\":\"%s\"}",
         sig.ticket, AccountInfoString(ACCOUNT_SERVER)
      );
      SendDataToWeb("POST", WebServerURL + "api/send_cancel_pending_response", rBad);
      Print("❌ Cannot delete market order: Ticket #", sig.ticket);
      return false;
   }
   
   string sym = OrderGetString(ORDER_SYMBOL);
   bool ok = trade.OrderDelete(sig.ticket);
   
   string resp;
   if(ok) {
      resp = StringFormat(
         "{\"ok\":true,\"ticket\":%I64u,\"symbol\":\"%s\",\"broker\":\"%s\"}",
         sig.ticket, sym, AccountInfoString(ACCOUNT_SERVER)
      );
      Print("✅ Pending order cancelled: Ticket #", sig.ticket, " Symbol: ", sym);
   } else {
      resp = StringFormat(
         "{\"ok\":false,\"error\":\"%s\",\"ticket\":%I64u,\"broker\":\"%s\"}",
         trade.ResultRetcodeDescription(), sig.ticket, AccountInfoString(ACCOUNT_SERVER)
      );
      Print("❌ Cancel failed: Ticket #", sig.ticket, " Error: ", trade.ResultRetcodeDescription());
   }
   
   SendDataToWeb("POST", WebServerURL + "api/send_cancel_pending_response", resp);
   return ok;
}

//============================================================

// Hàm lấy value của 1 key trong JSON đơn giản
string GetJsonString(string json, string key)
{
   string pattern = "\"" + key + "\"";
   int pos = StringFind(json, pattern);
   if(pos < 0) return "";
   int colon = StringFind(json, ":", pos);
   if(colon < 0) return "";
   int start = colon+1;

   // Bỏ qua khoảng trắng
   while(start < StringLen(json) && (StringGetCharacter(json,start)==' ')) start++;

   // Nếu có dấu " thì bỏ
   if(start < StringLen(json) && StringGetCharacter(json,start)=='\"') start++;

   // Tìm dấu kết thúc
   int end = StringFind(json, "\"", start);
   if(end < 0) {
      end = StringFind(json, ",", start);
      if(end < 0) end = StringFind(json, "}", start);
   }
   if(end < 0) return "";

   return StringSubstr(json,start,end-start);
}

// Parse JSON thành TradeSignal
bool ParseTradeSignal(string json, TradeSignal &sig)
{
   sig.action       = GetJsonString(json, "action");
   sig.symbol       = GetJsonString(json, "symbol");
   sig.side         = GetJsonString(json, "side");
   sig.comment      = GetJsonString(json, "comment");
   sig.volume       = StringToDouble(GetJsonString(json, "volume"));
   sig.sl_points    = StringToDouble(GetJsonString(json, "sl_points"));
   sig.tp_points    = StringToDouble(GetJsonString(json, "tp_points"));
   sig.max_slippage = (int)StringToDouble(GetJsonString(json, "max_slippage"));
   sig.ticket       = (int)StringToDouble(GetJsonString(json, "ticket"));

   return (sig.action != "");
}



//============================================================
// Hàm CheckSignalFromServer
void CheckSignalFromServer()
{
   string result_headers;
   uchar post[], result[];
   int timeout = 5000;

   string url = WebServerURL + "api/get_signal?broker=" + AccountInfoString(ACCOUNT_SERVER);
   int res = WebRequest("GET", url, "", timeout, post, result, result_headers);   

   if(res == -1){
      Print("ERR: Khong lay duoc tin hieu. ", GetLastError());
      return;
   }

   string response = CharArrayToString(result,0,-1);   
   if(StringLen(response) < 2) return;

   global_last_response = response;

   TradeSignal sig;   
   if(ParseTradeSignal(response, sig)){
      if(sig.action == "TRADE") HandleTrade(sig);
      else if(sig.action == "CLOSE") HandleClose(sig);
      else if(sig.action == "CANCEL_PENDING") HandleCancelPending(sig);
   }
}

//============================================================
// OnTimer
void OnTimer()
{
   string jsonData = GetMarketWatchData();
   if (StringLen(jsonData) > 2)
      SendDataToWeb("POST", WebServerURL + "api/receive_data", jsonData);
 
   //Print("[OnTimer] Calling GetPositionsData()...");
   string positionsData = GetPositionsData();
   //Print("[OnTimer] GetPositionsData() returned ", StringLen(positionsData), " bytes");
   
   if (StringLen(positionsData) > 2)
   {
      //Print("[OnTimer] WebServerURL: ", WebServerURL);
      //Print("[OnTimer] Sending TO: ", WebServerURL + "api/receive_positions");
      //Print("[OnTimer] Sending positions data: ", StringLen(positionsData), " bytes, Positions: ", PositionsTotal());
      bool sent = SendDataToWeb("POST", WebServerURL + "api/receive_positions", positionsData);
      //Print("[OnTimer] SendDataToWeb result: ", sent ? "SUCCESS" : "FAILED");
      if (!sent) {
         //Print("[OnTimer] ERROR: Failed to send! Check WebRequest URL permissions!");
      }
   }
   else
   {
      //Print("[OnTimer] No positions data to send (StringLen <= 2). PositionsTotal: ", PositionsTotal());
   }
   
   CheckSignalFromServer();      
}

//============================================================
// Viết URL mặc định ra file
void FunWriteDataToFile()
{
    int file_handle=FileOpen(glbStringFilePath+".txt",FILE_WRITE|FILE_TXT);
    if(file_handle!=INVALID_HANDLE)
    {
       FileWrite(file_handle,"http://127.0.0.1:80");        
    }
    FileClose(file_handle);
}

//============================================================
int OnInit()
{       
   if(!ReadWebServerURL())
   {
     FunWriteDataToFile();
   }   
   EventSetTimer(SendInterval);      
   return(INIT_SUCCEEDED);
}

void OnDeinit(const int reason)
{
   EventKillTimer();      
}
