#!/usr/bin/env python3
"""
bridge_services.py - Hardware and communications bridge: ESP32 UART, serial locks, SSE queue, temp cache.

Used by bridge.py (routes) and print_formats.py (open_serial_locked, probe_and_choose_port).
No Flask routes here; init(app, config) stores logger and config, starts background threads.
"""

import errno
import json
import os
import queue
import threading
import time
from contextlib import contextmanager

import serial

# Module-level state (set in init)
_logger = None
_config = {}
_esp_port = None  # mutable; may be updated by probe

# ESP32 serial and line handling
ser_lock = threading.Lock()
esp_ser = None
line_q: "queue.Queue[str]" = queue.Queue(maxsize=2000)
sse_clients = []
esp_read_buffer = ""

# Heater state (Pi side)
HEATER_STATE = {"t1": 0.0, "t2": 0.0}

# Temperature cache
latest_temps_cache = {
    "IR1": 0.0,
    "IR2": 0.0,
    "EXT1": 0.0,
    "EXT2": 0.0,
    "timestamp": 0,
    "error": None,
    "age_seconds": 0
}
temp_cache_lock = threading.Lock()

# Printer UART locks
_printer_locks = {}
_printer_locks_lock = threading.Lock()

# Calibration in progress - temp polling skips cycles when set to reduce serial contention
_calibration_in_progress = False
_calibration_lock = threading.Lock()

# Preheat cooldown - skip temp polling briefly after PHW
_last_preheat_time = 0.0
_preheat_cooldown = 1.0


def record_preheat_time():
    """Call after sending PHW so temp poller skips for a short window."""
    global _last_preheat_time
    _last_preheat_time = time.time()


def should_skip_temp_poll_for_preheat() -> bool:
    """True if we should skip this temp poll cycle (recent preheat)."""
    return (time.time() - _last_preheat_time) < _preheat_cooldown


def set_calibration_in_progress(value: bool):
    """Set flag so temp polling skips cycles during calibration."""
    global _calibration_in_progress
    with _calibration_lock:
        _calibration_in_progress = value


def is_calibration_in_progress() -> bool:
    """Check if calibration is in progress."""
    with _calibration_lock:
        return _calibration_in_progress


def init(app, config):
    """Store logger and config; open ESP serial; start reader and temp polling threads."""
    global _logger, _config, _esp_port, line_q, sse_clients
    _logger = app.logger
    _config = dict(config)
    _esp_port = _config.get("ESP_PORT", "/dev/serial0")
    line_q = queue.Queue(maxsize=2000)
    sse_clients = []
    try:
        _open_esp_serial()
        _logger.info("ESP32 UART initialized at startup")
    except Exception as e:
        _logger.error("Failed to open ESP UART at startup: %s", e)
    threading.Thread(target=esp_reader_loop, daemon=True).start()
    _logger.info("ESP reader thread started")
    threading.Thread(target=temperature_polling_thread, daemon=True).start()
    _logger.info("[TEMP POLLER] Background temperature polling thread started")


def probe_and_choose_port(configured_port, candidates=None):
    """
    Return first existing device. If configured_port exists return it.
    Raises FileNotFoundError if none found.
    """
    if configured_port and os.path.exists(configured_port):
        return configured_port
    if candidates is None:
        candidates = [
            "/dev/ttyAMA4",
            "/dev/ttyAMA3",
            "/dev/ttyUSB0",
            "/dev/ttyUSB1",
            "/dev/ttyAMA0",
            "/dev/serial0"
        ]
    for p in candidates:
        if p and os.path.exists(p):
            _logger.info("[PORT PROBE] using discovered serial device: %s (requested: %s)", p, configured_port or "auto")
            return p
    raise FileNotFoundError(errno.ENOENT, "Serial device not found", configured_port or "no-config")


def _open_esp_serial():
    """Open UART to ESP32 if needed. Uses probe_and_choose_port if configured path doesn't exist."""
    global esp_ser, _esp_port
    port = _config.get("ESP_PORT", "/dev/serial0")
    baud = _config.get("ESP_BAUD", 9600)
    with ser_lock:
        if esp_ser and getattr(esp_ser, "is_open", False):
            _logger.debug("ESP serial already open")
            return esp_ser
        try:
            if not port or not os.path.exists(port):
                try:
                    chosen = probe_and_choose_port(port)
                    _esp_port = chosen
                    port = chosen
                    _logger.info("[PORT PROBE] ESP port probed: using %s", port)
                except FileNotFoundError:
                    _logger.error("[PORT PROBE] No ESP serial device found - tried %s", port)
                    raise
            if esp_ser:
                try:
                    esp_ser.close()
                except Exception:
                    pass
            esp_ser = serial.Serial(
                port=port,
                baudrate=baud,
                timeout=2.0,
                write_timeout=2.0,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE,
                xonxoff=False,
                rtscts=False,
                dsrdtr=False
            )
            esp_ser.reset_input_buffer()
            esp_ser.reset_output_buffer()
            _esp_port = port
            _logger.info("ESP serial opened on %s @ %d", port, baud)
            return esp_ser
        except Exception as e:
            _logger.error("Failed to open ESP serial: %s", e)
            raise


def esp_write_line(cmd: str, timeout=1.0, max_retries=3) -> bool:
    """Write a line to the ESP serial port safely with retry logic. Returns True on success."""
    global esp_ser
    if not cmd:
        return False
    backoff = 0.1
    max_backoff = 1.0
    for attempt in range(max_retries):
        if not esp_ser or not getattr(esp_ser, "is_open", False):
            try:
                _open_esp_serial()
            except Exception as e:
                _logger.error("[ESP WRITE] Could not reopen ESP serial (attempt %d/%d): %s", attempt + 1, max_retries, e)
                if attempt < max_retries - 1:
                    time.sleep(backoff)
                    backoff = min(backoff * 2, max_backoff)
                    continue
                return False
        try:
            with ser_lock:
                if not esp_ser or not getattr(esp_ser, "is_open", False):
                    if attempt < max_retries - 1:
                        time.sleep(backoff)
                        backoff = min(backoff * 2, max_backoff)
                        continue
                    return False
                line = (cmd.strip() + "\n").encode('ascii', errors='replace')
                esp_ser.write(line)
                esp_ser.flush()
                _logger.debug("[ESP WRITE] Sent: %r", cmd.strip())
                return True
        except Exception as e:
            _logger.warning("[ESP WRITE] Failed (attempt %d/%d): %s", attempt + 1, max_retries, e)
            if attempt < max_retries - 1:
                try:
                    with ser_lock:
                        if esp_ser:
                            try:
                                esp_ser.close()
                            except Exception:
                                pass
                            esp_ser = None
                        _open_esp_serial()
                except Exception:
                    pass
                time.sleep(backoff)
                backoff = min(backoff * 2, max_backoff)
            else:
                _logger.exception("[ESP WRITE] All %d attempts failed for: %s", max_retries, cmd)
                return False
    return False


def esp_reader_loop():
    """Background thread: read lines from ESP32, push into line_q and sse_clients."""
    global esp_read_buffer, esp_ser
    reopen_backoff = 1.0
    max_backoff = 30.0
    empty_reads = 0
    queue_max = 2000
    while True:
        try:
            if not esp_ser or not getattr(esp_ser, "is_open", False):
                try:
                    _open_esp_serial()
                    reopen_backoff = 1.0
                except Exception as e:
                    _logger.error("Cannot open ESP serial in reader thread: %s", e)
                    time.sleep(reopen_backoff)
                    reopen_backoff = min(reopen_backoff * 2, max_backoff)
                    continue
            s = esp_ser
            with ser_lock:
                bytes_waiting = getattr(s, 'in_waiting', 0) or 0
                if bytes_waiting > 0:
                    chunk = s.read(min(bytes_waiting, 1024))
                else:
                    chunk = s.readline()
            if not chunk:
                empty_reads += 1
                time.sleep(0.05)
                continue
            empty_reads = 0
            try:
                decoded_chunk = chunk.decode("ascii", errors="ignore")
                esp_read_buffer += decoded_chunk
            except Exception as e:
                _logger.warning("Failed to decode ESP32 chunk: %s", e)
                continue
            while "\n" in esp_read_buffer:
                line, esp_read_buffer = esp_read_buffer.split("\n", 1)
                line = line.strip()
                if not line:
                    continue
                _logger.debug("<<< RECEIVED FROM ESP32: %r", line)
                has_printable = any(c.isprintable() for c in line)
                if not has_printable and len(line) > 0:
                    continue
                # TS response (TR1,TR2 / 0,TR2 / TR1,0): queue for poller only, do not broadcast
                if _is_ts_response_line(line):
                    try:
                        line_q.put_nowait(line)
                    except queue.Full:
                        try:
                            line_q.put(line, timeout=0.2)
                        except queue.Full:
                            pass
                    continue

                # Fast path: parse temperature lines and push JSON temps immediately (real-time UI).
                # Supports both: "T1,25.3,24.8" and "T1,IR1,25.3,EXT1,24.8" (same for T2).
                try:
                    if line.startswith("T1") or line.startswith("T2"):
                        tag = "T1" if line.startswith("T1") else "T2"
                        parsed = _parse_t1_t2_response(line, tag)
                        if parsed is not None:
                            ir_val, ext_val = parsed
                            current_time_ms = int(time.time() * 1000)
                            with temp_cache_lock:
                                if tag == "T1":
                                    latest_temps_cache["IR1"] = float(ir_val)
                                    latest_temps_cache["EXT1"] = float(ext_val)
                                else:
                                    latest_temps_cache["IR2"] = float(ir_val)
                                    latest_temps_cache["EXT2"] = float(ext_val)
                                latest_temps_cache["timestamp"] = current_time_ms
                                latest_temps_cache["age_seconds"] = 0
                                latest_temps_cache["error"] = None
                                cache = latest_temps_cache.copy()
                            temps_push = {
                                "type": "temps",
                                "IR1": float(cache.get("IR1", 0.0)),
                                "IR2": float(cache.get("IR2", 0.0)),
                                "EXT1": float(cache.get("EXT1", 0.0)),
                                "EXT2": float(cache.get("EXT2", 0.0)),
                                "timestamp": current_time_ms,
                            }
                            temps_json = json.dumps(temps_push)
                            dead = [q for q in list(sse_clients) if not _put_sse(q, temps_json)]
                            for q in dead:
                                if q in sse_clients:
                                    sse_clients.remove(q)
                            # Still queue the raw line for internal consumers (poller/debug),
                            # but do NOT broadcast the raw "T1/T2" line over SSE (it floods clients).
                            try:
                                line_q.put_nowait(line)
                            except queue.Full:
                                try:
                                    line_q.put(line, timeout=0.2)
                                except queue.Full:
                                    _logger.error("line_q FULL - dropping temp line")
                            continue
                except Exception:
                    # Never let parsing break the reader loop.
                    pass
                qsize = line_q.qsize()
                if qsize > queue_max * 0.8:
                    _logger.warning("line_q > 80%% full (%d/%d)", qsize, queue_max)
                try:
                    line_q.put_nowait(line)
                except queue.Full:
                    try:
                        line_q.put(line, timeout=0.5)
                    except queue.Full:
                        _logger.error("line_q FULL - dropping line")
                dead = [q for q in list(sse_clients) if not _put_sse(q, line)]
                for q in dead:
                    if q in sse_clients:
                        sse_clients.remove(q)
            if len(esp_read_buffer) > 4096:
                last_nl = esp_read_buffer.rfind("\n")
                if last_nl >= 0:
                    esp_read_buffer = esp_read_buffer[last_nl + 1:]
                else:
                    esp_read_buffer = ""
            time.sleep(0.02)
            reopen_backoff = 1.0
        except OSError as e:
            err = str(e).lower()
            if "device reports readiness" in err or "returned no data" in err:
                time.sleep(0.05)
                continue
            _logger.error("ESP reader OSError: %s", e)
            _close_esp_ser()
            time.sleep(reopen_backoff)
            reopen_backoff = min(reopen_backoff * 2, max_backoff)
        except Exception as e:
            _logger.error("ESP reader error: %s", e, exc_info=True)
            _close_esp_ser()
            time.sleep(reopen_backoff)
            reopen_backoff = min(reopen_backoff * 2, max_backoff)


def _put_sse(q, msg):
    try:
        q.put_nowait(msg)
        return True
    except (queue.Full, Exception):
        return False


def _close_esp_ser():
    global esp_ser
    try:
        if esp_ser:
            try:
                esp_ser.close()
            except Exception:
                pass
        esp_ser = None
    except Exception:
        pass


def _is_ts_response_line(line: str) -> bool:
    """True if line matches TS response format: TR1,TR2 / 0,TR2 / TR1,0 / TS,TR1,TR2"""
    parts = [p.strip().upper() for p in line.split(',') if p.strip()]
    if len(parts) < 2:
        return False
    # Accept "TS,TR1,TR2" - take last two parts
    left = parts[-2] if len(parts) >= 2 else parts[0]
    right = parts[-1]
    ok_left = left in ('TR1', '0')
    ok_right = right in ('TR2', '0')
    return ok_left and ok_right


def _handle_ts_response(line: str):
    """Parse TS response (TR1,TR2 / 0,TR2 / TR1,0 / TS,TR1,TR2) and emit TR1/TR2 SSE events."""
    if not line:
        return
    parts = [p.strip().upper() for p in line.split(',') if p.strip()]
    if len(parts) < 2:
        _logger.debug("[TS] Unexpected TS response format: %r", line)
        return
    left = parts[-2]
    right = parts[-1]
    if left == 'TR1':
        event_json = json.dumps({"type": "TR1"})
        dead = [q for q in list(sse_clients) if not _put_sse(q, event_json)]
        for q in dead:
            if q in sse_clients:
                sse_clients.remove(q)
        _logger.info("[TS] Emitted TR1 - basket 1 ready")
    if right == 'TR2':
        event_json = json.dumps({"type": "TR2"})
        dead = [q for q in list(sse_clients) if not _put_sse(q, event_json)]
        for q in dead:
            if q in sse_clients:
                sse_clients.remove(q)
        _logger.info("[TS] Emitted TR2 - basket 2 ready")


def _parse_t1_t2_response(line: str, expected_tag: str):
    """
    Parse either:
      - New compact format: T1,25.3,24.8  (IR, EXT) or T2,25.3,24.8
      - Legacy tagged format: T1,IR1,25.3,EXT1,24.8 or T2,IR2,25.3,EXT2,24.8
    Returns (ir_val, ext_val) or None.
    """
    parts = [p.strip() for p in line.split(',')]
    if not parts:
        return None
    if parts[0].upper() != expected_tag.upper():
        return None
    # New compact: T1,IR,EXT
    if len(parts) == 3:
        try:
            return (float(parts[1]), float(parts[2]))
        except ValueError:
            return None
    # Legacy tagged: T1,IR1,x,EXT1,y
    if len(parts) == 5:
        if expected_tag == 'T1':
            if parts[1].upper() != 'IR1' or parts[3].upper() != 'EXT1':
                return None
        else:
            if parts[1].upper() != 'IR2' or parts[3].upper() != 'EXT2':
                return None
        try:
            return (float(parts[2]), float(parts[4]))
        except ValueError:
            return None
    return None


def _read_t1_t2_from_queue(expected_tag: str, timeout: float = 10.0):
    """Read from line_q until a line matches T1 or T2 temp format. Returns (ir, ext) or None.
    TS response lines (TR1,TR2 etc) are handled and skipped."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            remaining = max(0.1, deadline - time.time())
            line = line_q.get(timeout=remaining)
            if _is_ts_response_line(line):
                _handle_ts_response(line)
                continue
            result = _parse_t1_t2_response(line, expected_tag)
            if result is not None:
                return result
        except queue.Empty:
            break
    return None


def temperature_polling_thread():
    """Background thread: poll ESP32 for temperatures and update latest_temps_cache.
    When temp is within ±3°C of set temp, sends TS every 3s and emits TR1/TR2 from response."""
    global latest_temps_cache
    poll_interval = float(_config.get("TEMP_POLL_INTERVAL", 0.5))
    t1_t2_gap = max(1.0, float(_config.get("TEMP_T1_T2_GAP", 1.0)))
    read_timeout = float(_config.get("TEMP_READ_TIMEOUT", 2.0))
    ts_interval = float(_config.get("TS_POLL_INTERVAL", 3.0))
    ts_tolerance = float(_config.get("TS_TEMP_TOLERANCE", 3.0))
    last_ts_time = 0.0
    temp_read_lock = threading.Lock()
    consecutive_errors = 0
    max_consecutive_errors = 5
    _logger.info("[TEMP POLLER] Starting (interval: %.1fs, TS every %.1fs when temp within ±%.1f°C)", poll_interval, ts_interval, ts_tolerance)
    time.sleep(0.2)
    while True:
        try:
            if is_calibration_in_progress():
                _logger.debug("[TEMP POLLER] Skipping cycle - calibration in progress")
                time.sleep(1.0)
                continue
            if should_skip_temp_poll_for_preheat():
                time.sleep(0.2)
                continue
            with temp_read_lock:
                # NOTE: Do NOT flush line_q or reset_input_buffer() here.
                # Flushing discards TR1/TR2 "temperature ready" events from ESP32
                # that esp_reader_loop has queued but not yet forwarded to SSE clients.
                # The reader loop handles TR1/TR2 in real-time; flushing kills them.

                # IMPORTANT: Always attempt BOTH T1 and T2 each cycle.
                # Previously, a T1 failure/timeout would `continue` early and T2 would never be polled,
                # which makes T1 look "continuous" while T2 becomes stale.
                t1_result = None
                t2_result = None
                t1_err = None
                t2_err = None

                # --- Poll T1 ---
                if not esp_write_line("T1"):
                    t1_err = "Failed to send T1 command"
                else:
                    t1_result = _read_t1_t2_from_queue("T1", timeout=read_timeout)
                    if t1_result is None:
                        t1_err = "T1 timeout"

                # 1 second gap between T1 and T2 so Pi can read TR1/TR2 and other commands
                _logger.debug("[TEMP POLLER] Sleeping %.1fs between T1 and T2", t1_t2_gap)
                time.sleep(t1_t2_gap)

                # --- Poll T2 ---
                if not esp_write_line("T2"):
                    t2_err = "Failed to send T2 command"
                else:
                    t2_result = _read_t1_t2_from_queue("T2", timeout=read_timeout)
                    if t2_result is None:
                        t2_err = "T2 timeout"

                # Update cache with whichever results we got this cycle.
                any_success = (t1_result is not None) or (t2_result is not None)
                current_time_ms = int(time.time() * 1000)
                with temp_cache_lock:
                    if t1_result is not None:
                        ir1, ext1 = t1_result
                        latest_temps_cache["IR1"] = float(ir1)
                        latest_temps_cache["EXT1"] = float(ext1)
                    if t2_result is not None:
                        ir2, ext2 = t2_result
                        latest_temps_cache["IR2"] = float(ir2)
                        latest_temps_cache["EXT2"] = float(ext2)

                    # Only bump timestamp when we actually got new data (T1 or T2).
                    if any_success:
                        latest_temps_cache["timestamp"] = current_time_ms
                        latest_temps_cache["age_seconds"] = 0
                        latest_temps_cache["error"] = None
                    else:
                        # Surface the most relevant error (prefer T2 error if present).
                        latest_temps_cache["error"] = t2_err or t1_err or "No temp data"

                    cache = latest_temps_cache.copy()

                # Push a temps update if any new data arrived this cycle.
                if any_success:
                    temps_push = {
                        "type": "temps",
                        "IR1": float(cache.get("IR1", 0.0)),
                        "IR2": float(cache.get("IR2", 0.0)),
                        "EXT1": float(cache.get("EXT1", 0.0)),
                        "EXT2": float(cache.get("EXT2", 0.0)),
                        "timestamp": int(cache.get("timestamp", current_time_ms)),
                    }
                    temps_json = json.dumps(temps_push)
                    _logger.debug("[TEMP POLLER] Pushing temps (partial ok): IR1=%.1f, IR2=%.1f, EXT1=%.1f, EXT2=%.1f",
                                  float(temps_push["IR1"]), float(temps_push["IR2"]),
                                  float(temps_push["EXT1"]), float(temps_push["EXT2"]))
                    for q in list(sse_clients):
                        _put_sse(q, temps_json)

                # TS polling: when temp within ±tolerance of set temp, send TS every ts_interval and emit TR1/TR2
                heater = get_heater_state()
                ir1 = cache.get("IR1")
                ir2 = cache.get("IR2")
                t1_set = float(heater.get("t1") or 0.0)
                t2_set = float(heater.get("t2") or 0.0)
                near1 = (t1_set > 0) and (ir1 is not None) and (abs(float(ir1) - t1_set) <= ts_tolerance)
                near2 = (t2_set > 0) and (ir2 is not None) and (abs(float(ir2) - t2_set) <= ts_tolerance)
                if (near1 or near2) and (time.time() - last_ts_time >= ts_interval):
                    last_ts_time = time.time()
                    if esp_write_line("TS"):
                        try:
                            line = line_q.get(timeout=2.0)
                            if _is_ts_response_line(line):
                                _handle_ts_response(line)
                            else:
                                _logger.debug("[TS] Unexpected response: %r", line)
                        except queue.Empty:
                            _logger.warning("[TS] No response to TS command within timeout")

                # Error tracking: only count as error if BOTH reads failed.
                if any_success:
                    consecutive_errors = 0
                else:
                    consecutive_errors += 1
        except Exception as e:
            _logger.error("[TEMP POLLER] Error: %s", e, exc_info=True)
            with temp_cache_lock:
                latest_temps_cache["error"] = str(e)
            consecutive_errors += 1
        if consecutive_errors >= max_consecutive_errors:
            try:
                with ser_lock:
                    _close_esp_ser()
                consecutive_errors = 0
                time.sleep(3.0)
            except Exception:
                pass
        time.sleep(poll_interval)


def send_phw_from_state():
    """Send PHW command using HEATER_STATE (threadsafe)."""
    t1 = float(HEATER_STATE.get("t1", 0.0))
    t2 = float(HEATER_STATE.get("t2", 0.0))
    cmd = f"PHW,{t1:.1f},{t2:.1f}"
    _logger.info("[HEATER] Sending PHW from state: %s", cmd)
    esp_write_line(cmd)
    return cmd


def get_heater_state():
    """Return current heater state dict (copy)."""
    return dict(HEATER_STATE)


def set_heater_state(t1=None, t2=None):
    """Update HEATER_STATE; None leaves value unchanged."""
    if t1 is not None:
        HEATER_STATE["t1"] = float(t1)
    if t2 is not None:
        HEATER_STATE["t2"] = float(t2)


def get_latest_temps():
    """Return copy of latest temps cache (same shape as api_temp response)."""
    with temp_cache_lock:
        return latest_temps_cache.copy()


def get_esp_serial():
    """Return current esp_ser reference (for connection status)."""
    return esp_ser


def get_esp_port():
    """Return current ESP port path (may have been updated by probe)."""
    return _esp_port or _config.get("ESP_PORT", "/dev/serial0")


def get_connection_status(get_last_temps_flag=False):
    """Return dict: serial_open, queue_size, queue_max, queue_usage_percent, sse_clients, port[, last_temps]."""
    qsize = line_q.qsize()
    queue_max = 2000
    status = {
        "serial_open": bool(esp_ser and getattr(esp_ser, "is_open", False)),
        "queue_size": qsize,
        "queue_max": queue_max,
        "queue_usage_percent": int((qsize / queue_max) * 100) if qsize > 0 else 0,
        "sse_clients": len(sse_clients),
        "port": get_esp_port()
    }
    if get_last_temps_flag:
        status["last_temps"] = get_last_temps_flag
    return status


def drain_queue(max_lines=10):
    """Remove up to max_lines from line_q and return (list of lines, current qsize)."""
    lines = []
    for _ in range(max_lines):
        try:
            lines.append(line_q.get_nowait())
        except queue.Empty:
            break
    return lines, line_q.qsize()


def create_sse_stream_generator():
    """Return generator for /api/stream: register queue with sse_clients, yield 'data: ...\\n\\n'."""
    q = queue.Queue()
    sse_clients.append(q)
    _logger.info("SSE client connected, count=%d", len(sse_clients))
    # Push cached temps immediately so new clients see live temps without waiting for next poll
    with temp_cache_lock:
        cache = latest_temps_cache.copy()
    if cache.get("timestamp", 0) > 0:
        temps_push = {
            "type": "temps",
            "IR1": cache.get("IR1", 0.0),
            "IR2": cache.get("IR2", 0.0),
            "EXT1": cache.get("EXT1", 0.0),
            "EXT2": cache.get("EXT2", 0.0),
            "timestamp": cache.get("timestamp", 0),
        }
        _put_sse(q, json.dumps(temps_push))
    try:
        while True:
            line = q.get()
            yield f"data: {line}\n\n"
    except GeneratorExit:
        pass
    finally:
        if q in sse_clients:
            sse_clients.remove(q)
        _logger.info("SSE client disconnected, count=%d", len(sse_clients))


def _get_lock_for_port(port):
    with _printer_locks_lock:
        if port not in _printer_locks:
            _printer_locks[port] = threading.Lock()
        return _printer_locks[port]


@contextmanager
def open_serial_locked(port, baud, timeout=1, bytesize=serial.EIGHTBITS,
                       parity=serial.PARITY_NONE, stopbits=serial.STOPBITS_ONE,
                       rtscts=False, xonxoff=False):
    """Open a serial port under a per-port lock. Uses probe_and_choose_port if port missing."""
    actual_port = port
    if not port or not os.path.exists(port):
        try:
            actual_port = probe_and_choose_port(port)
            _logger.info("[PORT PROBE] Port probed: %s (requested %s)", actual_port, port)
        except FileNotFoundError:
            _logger.error("[PORT PROBE] No serial device found: %s", port)
            raise FileNotFoundError(errno.ENOENT, "Serial device not found", port)
    lock = _get_lock_for_port(port)
    lock.acquire()
    ser = None
    try:
        ser = serial.Serial(
            port=actual_port,
            baudrate=baud,
            timeout=timeout,
            bytesize=bytesize,
            parity=parity,
            stopbits=stopbits,
            rtscts=rtscts,
            xonxoff=xonxoff,
        )
        _logger.info("[SERIAL] Opened %s @ %d", actual_port, baud)
        yield ser
    finally:
        try:
            if ser and ser.is_open:
                ser.flush()
                ser.close()
        except Exception as e:
            _logger.exception("[SERIAL] Error closing %s: %s", port, e)
        lock.release()


def open_serial(port: str, baud: int):
    """Deprecated: open serial without lock. Use open_serial_locked instead."""
    try:
        ser = serial.Serial(port=port, baudrate=baud, timeout=1)
        _logger.info("[PRINT] Opened serial port: %s @ %d baud", port, baud)
        return ser
    except Exception as e:
        _logger.error("[PRINT] Serial open error on %s: %s", port, e)
        return None
