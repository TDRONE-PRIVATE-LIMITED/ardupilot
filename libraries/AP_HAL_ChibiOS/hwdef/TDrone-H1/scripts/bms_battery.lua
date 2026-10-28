--[[
 TDrone-H1 battery monitor fed by the power_board BMS.

 The BMS MCU (U575) is MAVLink component 180 on SERIAL4 and sends BATTERY_STATUS at 4 Hz.
 This script hands that data to the scripting battery backend (BATT_MONITOR = 29), so the
 normal ArduPilot battery failsafes (BATT_LOW_VOLT / BATT_CRT_VOLT) act on it, and reports
 BMS faults as GCS text.

 DSG cut authority: the FC decides while it responds. In flight the BMS only cuts discharge for a
 short circuit (AFE hardware); under-voltage and over-current are flagged here for the failsafes.
 Disarmed, this script tells the BMS to cut discharge on under-voltage or over-current, so a pack
 left connected is not run flat. A BMS fault while disarmed also blocks arming.

 Restricted mode: with the balance lead open or missing the BMS keeps running but sends only the
 pack voltage (in cell 0, others UINT16_MAX, per MAVLink) plus CELL_FAIL: no charging, and arming
 is blocked here until the lead is back.
 Packed into ROMFS from the hwdef scripts/ directory (no SD card needed).
--]]

local MAV_SEVERITY = {EMERGENCY=0, ALERT=1, CRITICAL=2, ERROR=3, WARNING=4, NOTICE=5, INFO=6}

local MSG_BATTERY_STATUS = 147
local CRC_EXTRA = 154
local MSG_COMMAND_LONG = 76
local MSG_COMMAND_ACK = 77
local ACK_CRC_EXTRA = 143
local MAV_CMD_USER_1 = 31010   -- BMS: param1 1 = cut discharge, 0 = release
local MAV_RESULT_ACCEPTED = 0
local CUT_RETRY_MS = 1000
local FAULT_CUT = 1 | 8        -- DEEP_DISCHARGE | OVER_CURRENT
local COMP_ID_BATTERY = 180
local BATT_INSTANCE = 0         -- first battery (BATT_MONITOR)
local CELLS = 4
local LOOP_MS = 50
local STALE_MS = 1500           -- BMS sends at 4 Hz

local CHG_FAILED = 5
local FAULT_CELL_FAIL = 4
local CHG_UNHEALTHY = 6

local FAULT_TEXT = {
  [1] = "under-voltage",
  [4] = "cell fault",
  [8] = "over-current",
  [16] = "over-temperature",
  [32] = "under-temperature",
}

if param:get('BATT_MONITOR') ~= 29 then
  gcs:send_text(MAV_SEVERITY.WARNING, "BMS: BATT_MONITOR is not 29 (Scripting), script idle")
  return
end

local sysid = param:get('MAV_SYSID')

mavlink:init(4, 2)
mavlink:register_rx_msgid(MSG_BATTERY_STATUS)
mavlink:register_rx_msgid(MSG_COMMAND_ACK)

local last_rx_ms = nil
local link_lost = false
local last_faults = 0
local last_chg = -1
local last_restricted = false
local bms_chan = nil
local bms_sysid = nil
local cut_done = false         -- BMS acknowledged our cut
local last_cut_ms = nil

-- MAVLink X.25 CRC
local function crc_x25(buf)
  local crc = 0xFFFF
  for i = 1, #buf do
    local t = (string.byte(buf, i) ~ (crc & 0xFF)) & 0xFF
    t = (t ~ (t << 4)) & 0xFF
    crc = ((crc >> 8) ~ (t << 8) ~ (t << 3) ~ (t >> 4)) & 0xFFFF
  end
  return crc
end

--[[
 msg is ArduPilot's mavlink_message_t: checksum(2) magic len incompat compat seq sysid compid
 msgid(3), payload from byte 13. ArduPilot also passes frames that failed its CRC check to
 scripts, so the CRC is checked again here.
--]]
local function check(msg, crc_extra)
  local checksum, magic, len = string.unpack("<HBB", msg, 1)
  local _, sys, comp = string.unpack("<BBB", msg, 7)
  if magic ~= 0xFD or comp ~= COMP_ID_BATTERY or (sysid and sys ~= sysid) then
    return nil
  end
  if crc_x25(string.sub(msg, 4, 12 + len) .. string.char(crc_extra)) ~= checksum then
    return nil
  end
  return sys
end

local function decode(msg)
  local sys = check(msg, CRC_EXTRA)
  if not sys then
    return nil
  end
  local b = { sysid = sys }
  local ofs
  b.temperature, ofs = string.unpack("<h", msg, 13 + 8)
  b.cells = {}
  for i = 1, 10 do
    b.cells[i], ofs = string.unpack("<H", msg, ofs)
  end
  b.current, b.id, b.func, b.type, b.remaining = string.unpack("<hBBBb", msg, ofs)
  -- extensions (zero when truncated)
  b.charge_state = string.unpack("<B", msg, 13 + 40)
  b.faults = string.unpack("<I4", msg, 13 + 50)
  return b
end

local function report_restricted(restricted)
  if restricted and not last_restricted then
    gcs:send_text(MAV_SEVERITY.CRITICAL, "BMS: balance lead open, restricted (no charging, no arming)")
  elseif last_restricted and not restricted then
    gcs:send_text(MAV_SEVERITY.NOTICE, "BMS: balance lead OK")
  end
  last_restricted = restricted
end

local function report_faults(b, restricted)
  report_restricted(restricted)
  local faults = b.faults
  if restricted then
    faults = faults & ~FAULT_CELL_FAIL   -- reported as "restricted" above
  end
  if faults == last_faults and b.charge_state == last_chg then
    return
  end
  if b.charge_state == CHG_FAILED then
    gcs:send_text(MAV_SEVERITY.EMERGENCY, "BMS: SHORT CIRCUIT, discharge cut")
  end
  for bit, text in pairs(FAULT_TEXT) do
    if (faults & bit) ~= 0 and (last_faults & bit) == 0 then
      gcs:send_text(MAV_SEVERITY.CRITICAL, "BMS: " .. text)
    elseif (faults & bit) == 0 and (last_faults & bit) ~= 0 then
      gcs:send_text(MAV_SEVERITY.NOTICE, "BMS: " .. text .. " cleared")
    end
  end
  last_faults = faults
  last_chg = b.charge_state
end

-- pack voltage (V): cell sum, or cell 0 alone when the BMS cannot see the cells
local function set_voltages(state, b, restricted)
  if restricted then
    state:voltage(b.cells[1] * 0.001)
    return
  end
  local total_mv = 0
  for i = 1, CELLS do
    state:cell_voltages(i - 1, b.cells[i])
    total_mv = total_mv + b.cells[i]
  end
  state:cell_count(CELLS)
  state:voltage(total_mv * 0.001)
end

local function handle(b)
  if b.cells[1] == 0xFFFF then
    -- BMS not active (AFE bring-up failed): no data; the backend times out to unhealthy
    if last_chg ~= CHG_UNHEALTHY or last_faults ~= 0 then
      gcs:send_text(MAV_SEVERITY.CRITICAL, "BMS: not active")
      last_chg = CHG_UNHEALTHY
      last_faults = 0
    end
    return
  end
  local restricted = b.cells[2] == 0xFFFF
  report_faults(b, restricted)

  local state = BattMonitorScript_State()
  set_voltages(state, b, restricted)
  state:current_amps(b.current * 0.01)
  if b.temperature ~= 0x7FFF then
    state:temperature(b.temperature * 0.01)
  end
  if b.remaining >= 0 then
    state:capacity_remaining_pct(b.remaining)
  end
  -- in flight always healthy so the voltage failsafes keep working; on the ground a fault blocks arming
  state:healthy(arming:is_armed() or (b.faults == 0 and b.charge_state ~= CHG_FAILED))
  battery:handle_scripting(BATT_INSTANCE, state)
end

-- disarmed + under-voltage/over-current: tell the BMS to cut discharge (retry until acknowledged)
local function cut_policy(b, now)
  if (b.faults & FAULT_CUT) == 0 then
    cut_done = false            -- fault gone (the BMS clears its latch once it sees charging)
    return
  end
  if cut_done or arming:is_armed() or not bms_chan then
    return
  end
  if last_cut_ms and (now - last_cut_ms) < CUT_RETRY_MS then
    return
  end
  last_cut_ms = now
  local cmd = string.pack("<fffffffHBBB", 1, 0, 0, 0, 0, 0, 0, MAV_CMD_USER_1, bms_sysid, COMP_ID_BATTERY, 0)
  mavlink:send_chan(bms_chan, MSG_COMMAND_LONG, cmd)
end

local function handle_ack(msg)
  if not check(msg, ACK_CRC_EXTRA) then
    return
  end
  local command, result = string.unpack("<HB", msg, 13)
  if command ~= MAV_CMD_USER_1 then
    return
  end
  if result == MAV_RESULT_ACCEPTED then
    if not cut_done then
      gcs:send_text(MAV_SEVERITY.CRITICAL, "BMS: discharge cut (disarmed, battery fault)")
    end
    cut_done = true
  else
    gcs:send_text(MAV_SEVERITY.WARNING, string.format("BMS: cut refused (%d)", result))
  end
end

local function update()
  local now = millis():toint()
  while true do
    local msg, chan = mavlink:receive_chan()
    if not msg then
      break
    end
    local msgid = string.unpack("<I3", msg, 10)
    if msgid == MSG_COMMAND_ACK then
      handle_ack(msg)
    end
    local b = (msgid == MSG_BATTERY_STATUS) and decode(msg) or nil
    if b then
      bms_chan = chan
      bms_sysid = b.sysid
      last_rx_ms = now
      if link_lost then
        gcs:send_text(MAV_SEVERITY.NOTICE, "BMS: link back")
        link_lost = false
      end
      handle(b)
      cut_policy(b, now)
    end
  end
  if last_rx_ms and not link_lost and (now - last_rx_ms) > STALE_MS then
    gcs:send_text(MAV_SEVERITY.CRITICAL, "BMS: link lost")
    link_lost = true
  end
  return update, LOOP_MS
end

gcs:send_text(MAV_SEVERITY.INFO, "BMS: battery script running")
return update, LOOP_MS
