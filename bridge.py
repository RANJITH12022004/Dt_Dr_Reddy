#!/usr/bin/env python3
"""
bridge.py - Raspberry Pi hardware bridge and static server for your kiosk UI.

What it does, in plain terms:
- Serves index.html, app.js, style.css, assets, and local vendor JS/CSS.
- Talks to ESP32 over UART (commands + stroke data) via bridge_services.
- Streams ESP32 lines to the browser over SSE (/api/stream).
- Implements the StorageAdapter API on /api/storage/<key> pointing to the internal USB.
- Saves PDF reports on internal USB with FIFO delete when free space < MIN_FREE_GB.
- Prints via two RS232 UARTs (thermal + A4) via print_formats.
- Exports reports to an external USB when requested.

Refactored: ESP/serial/SSE in bridge_services; report/print logic in print_formats.
"""

import base64
import hashlib
import html
import json
import os
import pathlib
import sys
import re
import shutil
import subprocess
import time
from datetime import datetime, timedelta, timezone
try:
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None

import serial
from flask import Flask, Response, jsonify, request, send_from_directory, send_file
import io
import zipfile

import bridge_services
import print_formats
import report_context

# ======================= CONFIG SECTION ==========================

ESP_PORT = os.environ.get("ESP_PORT", "/dev/serial0")
ESP_BAUD = int(os.environ.get("ESP_BAUD", "9600"))
A4_PORT = os.environ.get("A4_PORT", "/dev/ttyAMA4")
A4_BAUD = int(os.environ.get("A4_BAUD", "9600"))
THERMAL_PORT = os.environ.get("THERMAL_PORT", "/dev/ttyAMA3")
THERMAL_BAUD = int(os.environ.get("THERMAL_BAUD", "9600"))

INTERNAL_ROOT = pathlib.Path("/media/usb_internal")
STORAGE_DIR = INTERNAL_ROOT / "storage"
REPORTS_DIR = INTERNAL_ROOT / "reports"
EXPORT_ROOT = pathlib.Path("/media/usb_export")
MIN_FREE_GB = 2.0
APP_ROOT = pathlib.Path("/opt/kiosk")
STATIC_ROOT = APP_ROOT
ALLOWED_DATETIME_ROLES = ('factory', 'admin')
_FACTORY_SUPPORT_USER = "raise@service"
_FACTORY_SUPPORT_PASSWORD = "raise@dev"
IST_TIMEZONE_NAME = "Asia/Kolkata"
IST_TZ = ZoneInfo(IST_TIMEZONE_NAME) if ZoneInfo else timezone(timedelta(hours=5, minutes=30))

# =================================================================

app = Flask(__name__)

try:
    STORAGE_DIR.mkdir(parents=True, exist_ok=True)
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
except Exception as e:
    pass  # log after app exists

config = {
    "ESP_PORT": ESP_PORT,
    "ESP_BAUD": ESP_BAUD,
    "TEMP_T1_T2_GAP": 1.0,  # 1 second gap between T1 and T2
    "TS_POLL_INTERVAL": 3.0,  # Send TS every 3 seconds when temp within tolerance
    "TS_TEMP_TOLERANCE": 3.0,  # ±3°C of set temp to start TS polling
    "A4_PORT": A4_PORT,
    "A4_BAUD": A4_BAUD,
    "THERMAL_PORT": THERMAL_PORT,
    "THERMAL_BAUD": THERMAL_BAUD,
    "REPORTS_DIR": REPORTS_DIR,
    "STORAGE_DIR": STORAGE_DIR,
    "MIN_FREE_GB": MIN_FREE_GB,
}
bridge_services.init(app, config)
print_formats.init(app, config)

app.logger.info("[CONFIG] A4_PORT=%s, A4_BAUD=%d", A4_PORT, A4_BAUD)
app.logger.info("[CONFIG] THERMAL_PORT=%s, THERMAL_BAUD=%d", THERMAL_PORT, THERMAL_BAUD)
if not STORAGE_DIR.exists():
    app.logger.error("Storage directory missing: %s", STORAGE_DIR)


def _now_ist() -> datetime:
    """Return the kiosk source-of-truth time in IST."""
    return datetime.now(IST_TZ)


def _parse_ist_wall_time(dt_str: str) -> datetime:
    """Parse user-entered date/time as an IST wall-clock value, never as UTC."""
    raw = str(dt_str or "").strip()
    if not raw:
        raise ValueError("Missing datetime parameter")
    raw = raw.replace("Z", "")
    if "+" in raw[10:]:
        raw = raw.split("+", 1)[0]
    if raw.count("-") > 2 and "T" in raw:
        raw = raw.rsplit("-", 1)[0]
    raw = raw.replace("T", " ")
    parsed = datetime.fromisoformat(raw)
    return parsed.replace(tzinfo=IST_TZ, microsecond=0)


def _format_datetime_payload(now: datetime) -> dict:
    h = now.hour
    h12 = 12 if (h % 12) == 0 else (h % 12)
    suffix = "PM" if h >= 12 else "AM"
    return {
        "datetime": now.strftime("%Y-%m-%dT%H:%M:%S"),
        "iso": now.strftime("%Y-%m-%dT%H:%M:%S"),
        "date": now.strftime("%d-%m-%Y"),
        "time": now.strftime("%H:%M"),
        "time_12h": f"{h12:02d}:{now.minute:02d} {suffix}",
        "timezone": IST_TIMEZONE_NAME,
        "utc_offset": "+05:30",
    }


def _run_time_command(cmd, timeout=5, check=True):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, check=check)


def _write_rtc_with_ioctl(user_dt: datetime):
    """Fallback RTC writer for images that do not ship the hwclock command."""
    rtc_writer = r'''
import fcntl
import os
import struct
import sys

RTC_SET_TIME = 0x4024700a
fields = [int(x) for x in sys.argv[1:7]]
year, month, day, hour, minute, second = fields
rtc_time = struct.pack("9i", second, minute, hour, day, month - 1, year - 1900, 0, 0, -1)
for rtc_path in ("/dev/rtc", "/dev/rtc0"):
    try:
        fd = os.open(rtc_path, os.O_RDONLY)
    except OSError:
        continue
    try:
        fcntl.ioctl(fd, RTC_SET_TIME, rtc_time)
        sys.exit(0)
    finally:
        os.close(fd)
raise SystemExit("No RTC device found")
'''
    args = [
        str(user_dt.year),
        str(user_dt.month),
        str(user_dt.day),
        str(user_dt.hour),
        str(user_dt.minute),
        str(user_dt.second),
    ]
    cmd = [sys.executable, "-c", rtc_writer, *args]
    if os.geteuid() != 0:
        cmd = ["sudo", *cmd]
    _run_time_command(cmd, timeout=10, check=True)


def _set_system_and_rtc_ist(user_dt: datetime) -> dict:
    """
    Set the Linux system clock and hardware RTC to the exact IST wall-clock time
    selected by the user. Linux reads the RTC as UTC on boot, so the hardware RTC
    must store UTC while the kiosk API/UI remains IST.
    """
    wall_time = user_dt.strftime("%Y-%m-%d %H:%M:%S")
    rtc_utc = user_dt.astimezone(timezone.utc)

    if sys.platform == 'win32':
        return {"ok": True, **_format_datetime_payload(user_dt)}

    commands = [
        (['sudo', '/usr/bin/timedatectl', 'set-ntp', 'false'], 5, True),
        (['sudo', '/usr/bin/timedatectl', 'set-timezone', IST_TIMEZONE_NAME], 5, True),
        (['sudo', '/usr/bin/timedatectl', 'set-local-rtc', '0'], 5, True),
        (['sudo', '/usr/bin/timedatectl', 'set-time', wall_time], 10, True),
    ]
    for cmd, timeout, check in commands:
        _run_time_command(cmd, timeout=timeout, check=check)

    hwclock = shutil.which("hwclock")
    if not hwclock:
        for candidate in ("/usr/sbin/hwclock", "/sbin/hwclock", "/usr/bin/hwclock", "/bin/hwclock"):
            if os.path.exists(candidate):
                hwclock = candidate
                break
    if hwclock:
        _run_time_command(['sudo', hwclock, '--systohc', '--utc'], timeout=10, check=True)
    else:
        _write_rtc_with_ioctl(rtc_utc)

    return {"ok": True, **_format_datetime_payload(user_dt)}

# =================== STATIC FILES (UI) ==========================

@app.route("/api/health")
def health():
    return {"status": "ok"}, 200


@app.route("/")
def serve_index():
    return send_from_directory(STATIC_ROOT, "index.html")


@app.route("/<path:path>")
def serve_static(path):
    return send_from_directory(STATIC_ROOT, path)


# =================== STORAGE HELPERS ==========================

def _truthy(v) -> bool:
    """Return True for common truthy payload values."""
    if isinstance(v, bool):
        return v
    if v is None:
        return False
    return str(v).strip().lower() in ("1", "true", "yes", "y", "on")


def _apply_factory_context(report_data, override: bool = False):
    """
    Merge factory settings from report_context into report_data["factorySettings"].

    - If override=False: only fills missing keys.
    - If override=True: always overwrites keys with current context values.
    """
    if not report_data:
        return report_data
    try:
        ctx = report_context.get_report_context(STORAGE_DIR)
    except Exception:
        return report_data

    fs = dict(report_data.get("factorySettings") or {})
    updates = {
        "companyName": (ctx.get("companyName") or "N/A"),
        "modelNo": (ctx.get("modelNo") or "N/A"),
        "serialNo": (ctx.get("serialNo") or "N/A"),
        "companyLocation": (ctx.get("location") or "N/A"),
        "instrumentId": (ctx.get("instrumentId") or "N/A"),
        "lastValidationDate": (ctx.get("lastValidationDate") or "N/A"),
        "nextValidationDate": (ctx.get("nextValidationDate") or "N/A"),
    }

    if override:
        fs.update(updates)
    else:
        for k, val in updates.items():
            fs.setdefault(k, val)

    out = dict(report_data)
    out["factorySettings"] = fs
    return out


def _apply_rtc_time(report_data):
    """
    Fill report createdAt from bridge RTC ONLY if missing.

    IMPORTANT:
    - Printing/exporting/regenerating a report must NOT overwrite the original conducted/saved time.
    - Some print paths regenerate text using report_data; those should preserve existing createdAt.
    """
    if not report_data:
        return report_data
    try:
        # Preserve an existing timestamp (conducted/saved time).
        existing = (report_data.get("createdAt") if isinstance(report_data, dict) else None)
        if existing:
            return report_data
        # Use current IST system/RTC time for createdAt when missing.
        dt_str = _now_ist().strftime("%Y-%m-%dT%H:%M:%S")
        report_data = dict(report_data)
        report_data["createdAt"] = dt_str
    except Exception:
        pass
    return report_data


def _enrich_report_data(report_data):
    """Merge factory settings and validation dates from storage if missing."""
    if not report_data:
        return report_data
    report_data = _apply_rtc_time(report_data)
    fs = report_data.get("factorySettings") or {}
    need = not fs.get("lastValidationDate") or not fs.get("nextValidationDate")
    if not need:
        return report_data
    return _apply_factory_context(report_data, override=False)


def storage_path_for(key: str) -> pathlib.Path:
    safe = "".join(c for c in key if c.isalnum() or c in "-_")
    return STORAGE_DIR / f"{safe}.json"


def decode_base64_to_file(b64_data: str, path: pathlib.Path):
    data = base64.b64decode(b64_data)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)


def safe_unique_report_path(prefix='report'):
    ts = _now_ist().strftime('%Y%m%dT%H%M%SIST')
    fname = f"{prefix}_{ts}.pdf"
    return REPORTS_DIR / fname


# =================== API: TEMP / MOTORS / STROKES ==================

@app.route("/api/temp/latest", methods=["GET"])
@app.route("/api/temp", methods=["GET"])
def api_temp():
    try:
        cache_copy = bridge_services.get_latest_temps()
        if cache_copy.get("timestamp", 0) > 0:
            age_seconds = (time.time() * 1000 - cache_copy["timestamp"]) / 1000
            cache_copy["age_seconds"] = round(age_seconds, 2)
            if age_seconds > 10:
                cache_copy["warning"] = f"Data is {age_seconds:.1f}s old"
        else:
            cache_copy["age_seconds"] = -1
            if not cache_copy.get("error"):
                cache_copy["warning"] = "Waiting for first temperature reading..."
        return jsonify(cache_copy)
    except Exception as e:
        app.logger.exception("[API] Error in api_temp")
        return jsonify({
            "IR1": 0.0, "IR2": 0.0, "EXT1": 0.0, "EXT2": 0.0,
            "timestamp": 0, "age_seconds": -1, "error": str(e)
        }), 500


@app.route("/api/heater", methods=["POST"])
def api_heater():
    data = request.get_json(force=True, silent=True) or {}
    try:
        updated = False
        if "id" in data and "pwm" in data:
            heater_id = str(data.get("id", "")).lower()
            pwm_value = float(data.get("pwm", 0.0)) if data.get("on", True) else 0.0
            if heater_id in ("h1", "1", "t1"):
                bridge_services.set_heater_state(t1=pwm_value)
                updated = True
            elif heater_id in ("h2", "2", "t2"):
                bridge_services.set_heater_state(t2=pwm_value)
                updated = True
            else:
                try:
                    n = int(''.join(ch for ch in heater_id if ch.isdigit()))
                    if n == 1:
                        bridge_services.set_heater_state(t1=pwm_value)
                        updated = True
                    elif n == 2:
                        bridge_services.set_heater_state(t2=pwm_value)
                        updated = True
                except Exception:
                    pass
        else:
            if "t1" in data or "h1" in data:
                bridge_services.set_heater_state(t1=float(data.get("t1", data.get("h1", 0.0))))
                updated = True
            if "t2" in data or "h2" in data:
                bridge_services.set_heater_state(t2=float(data.get("t2", data.get("h2", 0.0))))
                updated = True
        if not updated:
            return jsonify({"error": "E2001", "message": "No heater parameters provided"}), 400
        cmd = bridge_services.send_phw_from_state()
        return jsonify({"ok": True, "cmd": cmd, "state": bridge_services.get_heater_state()})
    except Exception as e:
        app.logger.exception("Failed to send PHW")
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/motor", methods=["POST"])
def api_motor():
    data = request.get_json(force=True, silent=True) or {}
    bid_raw = data.get("id")
    cmd = (data.get("cmd") or "").lower()
    if isinstance(bid_raw, str):
        try:
            bid = int(bid_raw.replace("m", "").replace("M", ""))
        except Exception:
            return jsonify({"error": "invalid motor id format"}), 400
    else:
        bid = bid_raw
    if bid not in (1, 2, 3):
        return jsonify({"error": "invalid motor id"}), 400
    if cmd == "start":
        return jsonify({"error": "start must use start-b1/b2/b3 endpoints"}), 400
    if cmd == "stop":
        out = f"STOP{bid}" if bid in (1, 2) else "STOP"
    elif cmd == "park":
        out = "STOP"
    else:
        return jsonify({"error": "invalid cmd"}), 400
    try:
        bridge_services.esp_write_line(out)
        return jsonify({"ok": True, "cmd": out})
    except Exception as e:
        app.logger.exception("Motor command failed")
        return jsonify({"success": False, "error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/stop", methods=["POST"])
def api_stop():
    try:
        bridge_services.esp_write_line("STOP")
        return jsonify({"ok": True, "cmd": "STOP"})
    except Exception as e:
        app.logger.exception("STOP command failed")
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/get_datetime", methods=["GET"])
def api_get_datetime():
    """Return current kiosk source-of-truth datetime in IST."""
    return jsonify(_format_datetime_payload(_now_ist()))


@app.route("/api/set_datetime", methods=["POST"])
def api_set_datetime():
    role = request.headers.get('X-User-Role', '').lower()
    if role not in ALLOWED_DATETIME_ROLES:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    data = request.get_json(force=True, silent=True) or {}
    dt_str = data.get('datetime', '')
    if not dt_str:
        return jsonify({"ok": False, "error": "Missing datetime parameter"}), 400
    try:
        user_dt = _parse_ist_wall_time(dt_str)
        return jsonify(_set_system_and_rtc_ist(user_dt))
    except subprocess.CalledProcessError as e:
        err_msg = (e.stderr or e.stdout or str(e)).strip() or "Failed to set system/RTC time"
        app.logger.warning("set_datetime failed: %s", err_msg)
        return jsonify({"ok": False, "error": "Failed to set system/RTC time", "detail": err_msg}), 500
    except subprocess.TimeoutExpired as e:
        app.logger.warning("set_datetime timed out: %s", e)
        return jsonify({"ok": False, "error": "Timed out setting system/RTC time"}), 500
    except ValueError:
        return jsonify({"ok": False, "error": "Invalid datetime format"}), 400
    except Exception as e:
        app.logger.exception("set_datetime failed")
        return jsonify({"error": str(e)}), 500


@app.route("/api/stop1", methods=["POST"])
def api_stop1():
    try:
        bridge_services.esp_write_line("STOP1")
        return jsonify({"ok": True, "cmd": "STOP1"})
    except Exception as e:
        app.logger.exception("STOP1 failed")
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/stop2", methods=["POST"])
def api_stop2():
    try:
        bridge_services.esp_write_line("STOP2")
        return jsonify({"ok": True, "cmd": "STOP2"})
    except Exception as e:
        app.logger.exception("STOP2 failed")
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/preheat", methods=["POST"])
def api_preheat():
    data = request.get_json(force=True, silent=True) or {}
    try:
        state = bridge_services.get_heater_state()
        h1 = float(data.get("h1", state.get("t1", 0.0)))
        h2 = float(data.get("h2", state.get("t2", 0.0)))
        bridge_services.set_heater_state(t1=h1, t2=h2)
        bridge_services.record_preheat_time()
        cmd = bridge_services.send_phw_from_state()
        return jsonify({"ok": True, "cmd": cmd, "state": bridge_services.get_heater_state()})
    except Exception as e:
        app.logger.exception("Preheat failed")
        return jsonify({"success": False, "error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/start-b1", methods=["POST"])
def api_start_b1():
    data = request.get_json(force=True, silent=True) or {}
    try:
        temp = float(data.get("temp", 37.0))
        bridge_services.set_heater_state(t1=temp)
        cmd = f"START,B1,{temp:.1f}W"
        bridge_services.esp_write_line(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        app.logger.exception("start-b1 failed")
        return jsonify({"success": False, "error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/start-b2", methods=["POST"])
def api_start_b2():
    data = request.get_json(force=True, silent=True) or {}
    try:
        temp = float(data.get("temp", 37.0))
        bridge_services.set_heater_state(t2=temp)
        cmd = f"START,B2,{temp:.1f}W"
        bridge_services.esp_write_line(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        app.logger.exception("start-b2 failed")
        return jsonify({"success": False, "error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/start-b3", methods=["POST"])
def api_start_b3():
    data = request.get_json(force=True, silent=True) or {}
    try:
        t1 = float(data.get("t1", 37.0))
        t2 = float(data.get("t2", 37.0))
        bridge_services.set_heater_state(t1=t1, t2=t2)
        cmd = f"START,B3,{t1:.1f}W,{t2:.1f}W"
        bridge_services.esp_write_line(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        app.logger.exception("start-b3 failed")
        return jsonify({"success": False, "error": "E1001", "message": "Device communication failed"}), 500


def _calibration_write(cmd):
    """Send calibration command with temp polling paused to reduce serial contention."""
    bridge_services.set_calibration_in_progress(True)
    try:
        bridge_services.esp_write_line(cmd)
    finally:
        bridge_services.set_calibration_in_progress(False)


@app.route("/api/cal-ir1", methods=["POST"])
def api_cal_ir1():
    data = request.get_json(force=True, silent=True) or {}
    temp = float(data.get("temp", 25.0))
    cmd = f"CAL,IR1,{temp:.1f}"
    try:
        _calibration_write(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/cal-ir2", methods=["POST"])
def api_cal_ir2():
    data = request.get_json(force=True, silent=True) or {}
    temp = float(data.get("temp", 25.0))
    cmd = f"CAL,IR2,{temp:.1f}"
    try:
        _calibration_write(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/cal-ext1", methods=["POST"])
def api_cal_ext1():
    data = request.get_json(force=True, silent=True) or {}
    temp = float(data.get("temp", 25.0))
    cmd = f"CAL,EXT1,{temp:.1f}"
    try:
        _calibration_write(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/cal-ext2", methods=["POST"])
def api_cal_ext2():
    data = request.get_json(force=True, silent=True) or {}
    temp = float(data.get("temp", 25.0))
    cmd = f"CAL,EXT2,{temp:.1f}"
    try:
        _calibration_write(cmd)
        return jsonify({"ok": True, "cmd": cmd})
    except Exception as e:
        return jsonify({"error": "E1001", "message": "Device communication failed"}), 500


@app.route("/api/debug/serial", methods=["POST"])
def api_debug_serial():
    data = request.get_json(force=True, silent=True) or {}
    cmd = data.get("cmd", "TEMP")
    try:
        bridge_services.esp_write_line(cmd)
        time.sleep(0.5)
        lines, qsize = bridge_services.drain_queue(max_lines=10)
        return jsonify({"ok": True, "cmd_sent": cmd, "lines_received": lines, "queue_size": qsize})
    except Exception as e:
        app.logger.exception("Debug serial failed")
        return jsonify({"error": "E9999", "message": "Unexpected system error"}), 500


@app.route("/api/stream", methods=["GET"])
def api_stream():
    return Response(
        bridge_services.create_sse_stream_generator(),
        mimetype="text/event-stream"
    )


# =================== STORAGE API ==================

@app.route("/api/storage/ping", methods=["GET"])
def api_storage_ping():
    return jsonify({"ok": True, "mode": "bridge"}), 200


@app.route("/api/internal_storage_status", methods=["GET"])
def api_internal_storage_status():
    try:
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        print_formats.enforce_fifo_reports()
        free_gb = print_formats.get_free_gb(REPORTS_DIR)
        return jsonify({
            "ok": True,
            "free_gb": round(float(free_gb), 3),
            "threshold_gb": float(MIN_FREE_GB),
            "low": float(free_gb) < float(MIN_FREE_GB),
            "message": "Internal storage full. Please export all the reports and contact sales.",
        }), 200
    except Exception as e:
        app.logger.exception("internal_storage_status failed: %s", e)
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/storage/<key>", methods=["GET", "POST", "DELETE"])
def api_storage(key):
    path = storage_path_for(key)
    if request.method == "GET":
        if not path.exists():
            return jsonify(None), 200
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return jsonify(data), 200
        except Exception as e:
            app.logger.exception("storage get failed")
            return jsonify({"error": str(e)}), 500
    if request.method == "POST":
        try:
            data = request.get_json(force=True)
            path.parent.mkdir(parents=True, exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            return jsonify({"ok": True}), 200
        except Exception as e:
            app.logger.exception("storage post failed")
            return jsonify({"error": str(e)}), 500
    if request.method == "DELETE":
        try:
            if path.exists():
                path.unlink()
            return jsonify({"ok": True}), 200
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    return jsonify({"error": "method not allowed"}), 405


@app.route("/api/report_context", methods=["GET"])
def api_report_context():
    try:
        ctx = report_context.get_report_context(STORAGE_DIR)
        return jsonify(ctx), 200
    except Exception as e:
        app.logger.exception("report_context failed: %s", e)
        return jsonify({"error": str(e)}), 500


@app.route("/api/reports_meta", methods=["GET"])
def api_reports_meta():
    filter_type = request.args.get("filter", "all")
    try:
        reports = report_context.get_filtered_reports_meta(STORAGE_DIR, filter_type)
        return jsonify({"ok": True, "reports": reports}), 200
    except Exception as e:
        app.logger.exception("reports_meta failed: %s", e)
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route("/api/storage/save_report", methods=["POST"])
def api_save_report():
    payload = request.get_json(force=True, silent=True) or {}
    filename = payload.get("filename")
    b64 = payload.get("data")
    if not filename or not b64:
        return jsonify({"error": "missing filename or data"}), 400
    filename = "".join(c for c in filename if c.isalnum() or c in "-_.")
    if not filename.lower().endswith(".pdf"):
        filename += ".pdf"
    path = REPORTS_DIR / filename
    try:
        decode_base64_to_file(b64, path)
        print_formats.enforce_fifo_reports()
    except Exception as e:
        app.logger.exception("Error saving PDF report")
        return jsonify({"error": "E9999", "message": "Unexpected system error"}), 500
    return jsonify({"ok": True, "file": filename})


# =================== PRINT API ==================

@app.route("/api/print", methods=["POST"])
def api_print():
    data = request.get_json(force=True, silent=True) or {}
    typ = (data.get("type") or "").lower()
    if typ == "a4":
        fname = data.get("file")
        if not fname:
            return jsonify({"error": "missing file"}), 400
        fname = "".join(c for c in fname if c.isalnum() or c in "-_.")
        pdf_path = REPORTS_DIR / fname
        if not pdf_path.exists():
            return jsonify({"error": f"file not found: {fname}"}), 404
        try:
            print_formats.print_a4_via_uart(pdf_path)
        except Exception as e:
            app.logger.exception("A4 print error")
            return jsonify({"error": "E1001", "message": "Device communication failed"}), 500
        return jsonify({"ok": True})
    if typ == "thermal":
        text = data.get("text") or "Test report\n"
        try:
            print_formats.print_thermal_text(text)
        except Exception as e:
            app.logger.exception("Thermal print error")
            return jsonify({"error": "E1001", "message": "Device communication failed"}), 500
        return jsonify({"ok": True})
    return jsonify({"error": "invalid type (expected 'a4' or 'thermal')"}), 400


@app.route("/api/report_to_image", methods=["POST"])
def api_report_to_image():
    try:
        data = request.get_json(force=True)
        if not data:
            return jsonify({"ok": False, "error": "Invalid JSON payload"}), 400
        html = data.get("html")
        pdf_b64 = data.get("pdf_base64")
        dpi = int(data.get("dpi", 150))
        printer = data.get("printer")
        images = print_formats.render_html_to_pdf_or_image(html=html, pdf_b64=pdf_b64, dpi=dpi)
        result = {"ok": True, "images": images}
        if printer == "a4":
            try:
                if images:
                    try:
                        from PIL import Image as PILImage
                        img = PILImage.open(images[0])
                        target_width_px = int(8.27 * dpi)
                        if img.width != target_width_px:
                            new_h = int(img.height * (target_width_px / img.width))
                            img = img.resize((target_width_px, new_h), PILImage.LANCZOS)
                        port_to_use = bridge_services.probe_and_choose_port(A4_PORT)
                        print_formats.send_escpos_raster(port_to_use, A4_BAUD, img, width_pixels=target_width_px)
                        result["printed"] = True
                        result["device"] = port_to_use
                    except Exception as e:
                        app.logger.exception("A4 raster send failed: %s", e)
                        if not data.get("use_raster"):
                            try:
                                from bs4 import BeautifulSoup
                                text_content = BeautifulSoup(html or "", "html.parser").get_text(separator="\n", strip=True)
                                port_to_use = bridge_services.probe_and_choose_port(A4_PORT)
                                print_formats.print_a4_fallback_text_send(text_content, port=port_to_use, baud=A4_BAUD)
                                result["printed"] = True
                                result["device"] = port_to_use
                            except Exception as e2:
                                result["printed"] = False
                                result["print_error"] = str(e2)
                        else:
                            result["printed"] = False
                            result["print_error"] = str(e)
                else:
                    result["printed"] = False
                    result["print_error"] = "No images generated"
            except Exception as e:
                result["printed"] = False
                result["print_error"] = str(e)
        elif printer == "thermal" and images:
            try:
                thermal_port = bridge_services.probe_and_choose_port(THERMAL_PORT)
                from PIL import Image as PILImage
                img = PILImage.open(images[0])
                print_formats.send_raster_to_thermal(img, thermal_port, THERMAL_BAUD)
                result["printed"] = True
                result["device"] = thermal_port
            except Exception as e:
                result["printed"] = False
                result["print_error"] = str(e)
        return jsonify(result)
    except ValueError as e:
        return jsonify({"ok": False, "error": str(e)}), 400
    except Exception as e:
        app.logger.exception("report_to_image failed")
        return jsonify({"ok": False, "error": str(e)}), 500


def _find_thermal_txt_path(report_name):
    """Find thermal .txt file by exact name or glob (handles timestamped filenames)."""
    safe_name = report_name.replace('.pdf', '').replace('.txt', '').replace('_thermal', '')
    if '/' in safe_name or '\\' in safe_name:
        safe_name = os.path.basename(safe_name)
    safe_name = "".join(c for c in safe_name if c.isalnum() or c in "-_.")[:50]
    if not safe_name:
        return None
    exact = REPORTS_DIR / f"{safe_name}_thermal.txt"
    if exact.exists():
        return exact
    # Glob fallback for timestamped names (e.g. report_20250205T123456Z_thermal.txt)
    candidates = sorted(REPORTS_DIR.glob(f"*{safe_name}*_thermal.txt"), key=lambda p: p.stat().st_mtime, reverse=True)
    return candidates[0] if candidates else None


def _find_a4_txt_path(report_name):
    """Find A4 .txt file by exact name or glob (handles timestamped filenames)."""
    safe_name = report_name
    if '/' in safe_name or '\\' in safe_name:
        safe_name = os.path.basename(safe_name)
    safe_name = safe_name.replace('.pdf', '').replace('.txt', '')
    safe_name = "".join(c for c in safe_name if c.isalnum() or c in "-_.")[:50]
    if not safe_name:
        return None
    exact = REPORTS_DIR / f"{safe_name}.txt"
    if exact.exists():
        return exact
    # Glob fallback for timestamped names (e.g. report_20250205T123456Z.txt)
    candidates = sorted(REPORTS_DIR.glob(f"*{safe_name}*.txt"), key=lambda p: p.stat().st_mtime, reverse=True)
    for p in candidates:
        if "_thermal" not in p.stem:
            return p
    return None


def _api_print_a4_impl():
    payload = request.get_json(force=True)
    if not payload:
        return jsonify({'ok': False, 'error': 'Invalid JSON payload'}), 400
    # Recipe print path — same UART text send as test reports
    if payload.get('type') == 'recipe' and (payload.get('recipe_data') or payload.get('text')):
        recipe_data = dict(payload.get('recipe_data') or {})
        recipe_data = _apply_factory_context(recipe_data, override=True)
        try:
            text = payload.get('text')
            if not text:
                text = print_formats.format_recipe_text(recipe_data, layout='a4')
            # Persist like test reports, then print via the same A4 text UART path
            safe_name = "".join(c for c in str(recipe_data.get('name') or 'recipe') if c.isalnum() or c in "-_")[:50] or "recipe"
            txt_path = REPORTS_DIR / f"RECIPE_{safe_name}.txt"
            try:
                REPORTS_DIR.mkdir(parents=True, exist_ok=True)
                with open(txt_path, 'w', encoding='utf-8') as f:
                    f.write(text if isinstance(text, str) else str(text))
            except Exception:
                app.logger.exception("[A4 PRINT] Could not save recipe text file")
            print_formats.print_a4_fallback_text_send(text)
            return jsonify({'ok': True, 'mode': 'recipe-text', 'message': 'Recipe printed successfully', 'file': str(txt_path)})
        except Exception as e:
            app.logger.exception("[A4 PRINT] Recipe printing failed: %s", e)
            # Fall through to plain text path if provided
            if payload.get('text'):
                try:
                    print_formats.print_a4_fallback_text_send(payload.get('text'))
                    return jsonify({'ok': True, 'mode': 'text', 'message': 'Recipe printed successfully'})
                except Exception:
                    pass
            return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
    report_name = payload.get('report_name')
    if report_name:
        force_regenerate = _truthy(payload.get("force_regenerate"))
        if not force_regenerate:
            txt_path = _find_a4_txt_path(report_name)
            if txt_path:
                try:
                    with open(txt_path, 'r', encoding='utf-8') as f:
                        text = f.read()
                    print_formats.print_a4_fallback_text_send(text)
                    return jsonify({'ok': True, 'mode': 'text-file', 'message': 'Text report printed successfully', 'file': str(txt_path)})
                except Exception as e:
                    app.logger.exception("[A4 PRINT] Text printing failed: %s", e)
                    return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
        report_data = payload.get('report_data')
        if report_data:
            # Option A: Always regenerate using current context when requested.
            report_data = _apply_factory_context(report_data, override=force_regenerate)
            report_data = _apply_rtc_time(report_data)
            if not force_regenerate:
                report_data = _enrich_report_data(report_data)
            safe_name = "".join(c for c in report_name if c.isalnum() or c in "-_.")[:50] or "report"
            txt_path = REPORTS_DIR / f"{safe_name}.txt"
            try:
                print_formats.generate_text_report(report_data, txt_path, layout='a4')
                with open(txt_path, 'r', encoding='utf-8') as f:
                    text = f.read()
                print_formats.print_a4_fallback_text_send(text)
                return jsonify({'ok': True, 'mode': 'text-file-generated', 'message': 'Text report generated and printed successfully', 'file': str(txt_path), 'force_regenerate': force_regenerate})
            except Exception as gen_err:
                app.logger.exception("[A4 PRINT] Error generating text report: %s", gen_err)
                return jsonify({'ok': False, 'error': f'Could not generate text report: {str(gen_err)}'}), 500
        return jsonify({'ok': False, 'error': 'Report layout not found. Please save the report again.'}), 404
    text = payload.get('text')
    if text:
        try:
            print_formats.print_a4_fallback_text_send(text)
            return jsonify({'ok': True, 'mode': 'text', 'message': 'Text printed successfully'})
        except Exception as e:
            app.logger.exception("[A4 PRINT] Text printing failed: %s", e)
            return jsonify({'ok': False, 'error': 'Text print failed', 'detail': str(e)}), 500
    pdf_path = payload.get('pdf_path')
    if not pdf_path:
        return jsonify({'ok': False, 'error': 'Missing required field: pdf_path or text'}), 400
    if not isinstance(pdf_path, str):
        return jsonify({'ok': False, 'error': 'pdf_path must be a string'}), 400
    pdf_abs = pathlib.Path(pdf_path).resolve() if os.path.isabs(pdf_path) else (REPORTS_DIR / pdf_path).resolve()
    if not pdf_abs.exists():
        return jsonify({'ok': False, 'error': 'PDF file not found', 'path': str(pdf_abs)}), 404
    if not os.access(str(pdf_abs), os.R_OK):
        return jsonify({'ok': False, 'error': 'PDF file not readable', 'path': str(pdf_abs)}), 500
    try:
        print_formats.print_a4_pdf_raster(pdf_abs)
        return jsonify({'ok': True, 'mode': 'raster', 'file': str(pdf_abs)})
    except Exception as raster_error:
        try:
            print_formats.print_a4_pdf_text_fallback(pdf_abs, width_chars=int(payload.get('width_chars', 80)))
            return jsonify({'ok': True, 'mode': 'text-fallback', 'file': str(pdf_abs), 'warning': 'Layout may differ from PDF'})
        except Exception as text_error:
            app.logger.exception("[A4 PRINT] Both raster and text fallback failed")
            return jsonify({'ok': False, 'error': 'Print failed', 'raster_error': str(raster_error), 'text_error': str(text_error)}), 500


@app.route('/api/print_a4', methods=['POST'])
def api_print_a4():
    try:
        return _api_print_a4_impl()
    except Exception as e:
        app.logger.exception("[API PRINT A4] Error: %s", e)
        err_str = str(e).lower()
        if any(x in err_str for x in ['filenotfound', 'no such file', 'serial', 'permission', 'connection', 'device', 'timeout', 'errno', 'e9999']):
            return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
        return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500


@app.route('/api/print_thermal', methods=['POST'])
def api_print_thermal():
    try:
        data = request.get_json(force=True)
        if not data:
            return jsonify({'ok': False, 'error': 'Invalid JSON payload'}), 400
        # Recipe print path — same UART text send as test reports
        if data.get('type') == 'recipe' and (data.get('recipe_data') or data.get('text')):
            recipe_data = dict(data.get('recipe_data') or {})
            recipe_data = _apply_factory_context(recipe_data, override=True)
            try:
                text = data.get('text')
                if not text:
                    text = print_formats.format_recipe_text(recipe_data, layout='thermal')
                if not isinstance(text, str):
                    text = str(text)
                safe_name = "".join(c for c in str(recipe_data.get('name') or 'recipe') if c.isalnum() or c in "-_")[:50] or "recipe"
                txt_path = REPORTS_DIR / f"RECIPE_{safe_name}_thermal.txt"
                try:
                    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
                    with open(txt_path, 'w', encoding='utf-8') as f:
                        f.write(text)
                except Exception:
                    app.logger.exception("[THERMAL PRINT] Could not save recipe text file")
                try:
                    port = bridge_services.probe_and_choose_port(THERMAL_PORT, candidates=[THERMAL_PORT, '/dev/ttyAMA3', '/dev/ttyUSB0'])
                except FileNotFoundError:
                    return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
                print_formats.print_thermal_chunked(text, port=port, baud=THERMAL_BAUD)
                return jsonify({'ok': True, 'device': port, 'mode': 'recipe-text', 'file': str(txt_path)})
            except Exception as e:
                app.logger.exception("api_print_thermal recipe failed: %s", e)
                # Fall through to plain text if provided
                if data.get('text'):
                    try:
                        port = bridge_services.probe_and_choose_port(THERMAL_PORT, candidates=[THERMAL_PORT, '/dev/ttyAMA3', '/dev/ttyUSB0'])
                        print_formats.print_thermal_chunked(data.get('text'), port=port, baud=THERMAL_BAUD)
                        return jsonify({'ok': True, 'device': port, 'mode': 'text'})
                    except Exception:
                        pass
                return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
        text = None
        report_name = data.get('report_name')
        if report_name:
            force_regenerate = _truthy(data.get("force_regenerate"))
            if force_regenerate:
                # Option A: always regenerate fresh 48-char thermal text from report_data.
                report_data = data.get("report_data")
                if report_data:
                    report_data = _apply_factory_context(report_data, override=True)
                    report_data = _apply_rtc_time(report_data)
                    safe_name = "".join(c for c in report_name.replace('_thermal', '') if c.isalnum() or c in "-_.")[:50] or "report"
                    txt_path = REPORTS_DIR / f"{safe_name}_thermal.txt"
                    try:
                        print_formats.generate_text_report(report_data, txt_path, layout='thermal')
                        with open(txt_path, 'r', encoding='utf-8') as f:
                            text = f.read()
                    except Exception:
                        text = None
                if not text:
                    return jsonify({'ok': False, 'error': 'Report layout not found. Please save the report again.'}), 404
            else:
                txt_path = _find_thermal_txt_path(report_name)
                if txt_path:
                    with open(txt_path, 'r', encoding='utf-8') as f:
                        text = f.read()
                else:
                    # No thermal file - prefer generating from report_data (proper 48-char layout)
                    report_data = data.get('report_data')
                    if report_data:
                        report_data = _enrich_report_data(report_data)
                        safe_name = "".join(c for c in report_name.replace('_thermal', '') if c.isalnum() or c in "-_.")[:50] or "report"
                        txt_path = REPORTS_DIR / f"{safe_name}_thermal.txt"
                        try:
                            print_formats.generate_text_report(report_data, txt_path, layout='thermal')
                            with open(txt_path, 'r', encoding='utf-8') as f:
                                text = f.read()
                        except Exception:
                            text = None
                    if not text:
                        a4_txt_path = _find_a4_txt_path(report_name)
                        if a4_txt_path:
                            with open(a4_txt_path, 'r', encoding='utf-8') as f:
                                a4_text = f.read()
                            text = print_formats.convert_a4_to_thermal_layout(a4_text, width=48)
                    if not text:
                        text = data.get('text')
                    if not text:
                        return jsonify({'ok': False, 'error': 'Report layout not found. Please save the report again.'}), 404
        else:
            text = data.get('text')
            if not text:
                return jsonify({'ok': False, 'error': 'Missing required field: text or report_name'}), 400
        if not isinstance(text, str):
            text = str(text)
        if not text.strip():
            return jsonify({'ok': False, 'error': 'Empty print data'}), 400
        try:
            port = bridge_services.probe_and_choose_port(THERMAL_PORT, candidates=[THERMAL_PORT, '/dev/ttyAMA3', '/dev/ttyUSB0'])
        except FileNotFoundError:
            return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500
        print_formats.print_thermal_chunked(text, port=port, baud=THERMAL_BAUD)
        return jsonify({'ok': True, 'device': port})
    except Exception as e:
        app.logger.exception("api_print_thermal failed: %s", e)
        return jsonify({'ok': False, 'error': 'Printer error. Check the printer connection.'}), 500


@app.route('/api/print_test', methods=['GET'])
def api_print_test():
    ts = time.strftime('%Y-%m-%d %H:%M:%S')
    test_text = f"*** PRINTER TEST ***\nTime: {ts}\nHello Printer!\n\n"
    results = {}
    try:
        port_to_use = bridge_services.probe_and_choose_port(A4_PORT, candidates=[A4_PORT, '/dev/ttyAMA4', '/dev/ttyUSB0'])
        print_formats.print_a4_fallback_text_send(test_text, port=port_to_use, baud=A4_BAUD)
        results['a4'] = {'ok': True, 'method': 'uart', 'device': port_to_use}
    except FileNotFoundError as e:
        results['a4'] = {'ok': False, 'error': 'device not found', 'device': A4_PORT}
    except Exception as e:
        results['a4'] = {'ok': False, 'err': str(e)}
    try:
        thermal_port = bridge_services.probe_and_choose_port(THERMAL_PORT)
        print_formats.print_thermal_chunked(test_text, port=thermal_port, baud=THERMAL_BAUD, paper_width=384)
        results['thermal'] = {'ok': True, 'device': thermal_port, 'baud': THERMAL_BAUD}
    except FileNotFoundError as e:
        results['thermal'] = {'ok': False, 'error': 'device not found', 'device': THERMAL_PORT}
    except Exception as e:
        results['thermal'] = {'ok': False, 'err': str(e)}
    return jsonify(results)


@app.route('/api/print_status', methods=['GET'])
def api_print_status():
    status = {
        "a4": {"configured_port": A4_PORT, "configured_baud": A4_BAUD},
        "thermal": {"configured_port": THERMAL_PORT, "configured_baud": THERMAL_BAUD},
        "esp": {"configured_port": ESP_PORT, "configured_baud": ESP_BAUD}
    }
    try:
        status["a4"]["actual_port"] = bridge_services.probe_and_choose_port(A4_PORT)
    except FileNotFoundError:
        status["a4"]["actual_port"] = None
        status["a4"]["port_error"] = "Device not found"
    try:
        status["thermal"]["actual_port"] = bridge_services.probe_and_choose_port(THERMAL_PORT)
    except FileNotFoundError:
        status["thermal"]["actual_port"] = None
        status["thermal"]["port_error"] = "Device not found"
    try:
        status["esp"]["actual_port"] = bridge_services.probe_and_choose_port(ESP_PORT)
    except FileNotFoundError:
        status["esp"]["actual_port"] = None
        status["esp"]["port_error"] = "Device not found"
    return jsonify({"ok": True, "status": status})


# =================== SAVE REPORT PDF ==================

@app.route("/api/save_report_pdf", methods=["POST"])
def api_save_report_pdf():
    try:
        data = request.get_json(force=True, silent=True) or {}
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        if data.get('pdf_base64'):
            pdf_size = len(data['pdf_base64']) * 3 / 4
            if pdf_size > 50 * 1024 * 1024:
                return jsonify({"error": "E3004", "message": "PDF file too large (max 50 MB)"}), 400
            report_name = data.get('report_name', 'report')
            safe_name = "".join(c for c in report_name if c.isalnum() or c in "-_.")[:50]
            p = safe_unique_report_path(safe_name)
            decode_base64_to_file(data['pdf_base64'], p)
            issue = _pdf_quality_issue(p)
            if issue:
                try:
                    p.unlink()
                except OSError:
                    pass
                return jsonify({"error": "E3005", "message": f"Saved PDF validation failed: {issue}"}), 500
            txt_path = p.with_suffix('.txt')
            thermal_txt_path = p.with_name(p.stem + '_thermal.txt')
            report_data = data.get('report_data', {}) or {'name': safe_name, 'createdAt': _now_ist().strftime("%Y-%m-%dT%H:%M:%S")}
            try:
                print_formats.generate_text_report(report_data, txt_path, layout='a4')
            except Exception:
                pass
            try:
                print_formats.generate_text_report(report_data, thermal_txt_path, layout='thermal')
            except Exception:
                pass
            print_formats.enforce_fifo_reports()
            return jsonify({
                "ok": True, "filename": str(p), "relative": str(p.name),
                "text_file": str(txt_path.name) if txt_path.exists() else None,
                "thermal_text_file": str(thermal_txt_path.name) if thermal_txt_path.exists() else None
            })
        if data.get('html'):
            html = data['html']
            report_name = data.get('report_name', 'report')
            safe_name = "".join(c for c in report_name if c.isalnum() or c in "-_.")[:50]
            tmp_pdf = safe_unique_report_path(safe_name)
            tmp_html = tmp_pdf.with_suffix('.html')
            with open(tmp_html, 'w', encoding='utf-8') as f:
                f.write(html)
            try:
                subprocess.check_call([
                    'wkhtmltopdf', '--page-size', 'A4',
                    '--margin-top', '8', '--margin-bottom', '8',
                    '--margin-left', '8', '--margin-right', '8',
                    str(tmp_html), str(tmp_pdf)
                ], timeout=30)
            except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
                CHROME_BIN = shutil.which("chromium") or shutil.which("chromium-browser") or "chromium"
                try:
                    subprocess.check_call([
                        CHROME_BIN, "--headless", "--disable-gpu", "--no-sandbox",
                        "--allow-file-access-from-files", "--disable-web-security",
                        f"--print-to-pdf={tmp_pdf}", f"file://{tmp_html}"
                    ], timeout=40)
                except Exception as e2:
                    if tmp_html.exists():
                        try:
                            tmp_html.unlink()
                        except Exception:
                            pass
                    return jsonify({"error": "E3002", "message": "PDF generation failed"}), 500
            if tmp_html.exists():
                try:
                    tmp_html.unlink()
                except Exception:
                    pass
            issue = _pdf_quality_issue(tmp_pdf)
            if issue:
                try:
                    tmp_pdf.unlink()
                except OSError:
                    pass
                return jsonify({"error": "E3005", "message": f"Generated PDF validation failed: {issue}"}), 500
            txt_path = tmp_pdf.with_suffix('.txt')
            thermal_txt_path = tmp_pdf.with_name(tmp_pdf.stem + '_thermal.txt')
            report_data = data.get('report_data', {}) or {'name': report_name, 'createdAt': _now_ist().strftime("%Y-%m-%dT%H:%M:%S")}
            try:
                print_formats.generate_text_report(report_data, txt_path, layout='a4')
            except Exception:
                pass
            try:
                print_formats.generate_text_report(report_data, thermal_txt_path, layout='thermal')
            except Exception:
                pass
            print_formats.enforce_fifo_reports()
            return jsonify({
                "ok": True, "filename": str(tmp_pdf), "relative": str(tmp_pdf.name),
                "text_file": str(txt_path.name) if txt_path.exists() else None,
                "thermal_text_file": str(thermal_txt_path.name) if thermal_txt_path.exists() else None
            })
        return jsonify({"error": "E3001", "message": "Missing pdf_base64 or html"}), 400
    except Exception as e:
        app.logger.exception("[REPORT] Error saving report PDF")
        return jsonify({"error": "E9999", "message": "Unexpected system error"}), 500


@app.route("/api/list_reports", methods=["GET"])
def api_list_reports():
    try:
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        reports = []
        for f in REPORTS_DIR.iterdir():
            if f.is_file() and f.suffix.lower() == '.pdf':
                st = f.stat()
                reports.append({"name": f.name, "size": st.st_size, "mtime": st.st_mtime})
        reports.sort(key=lambda x: x["mtime"], reverse=True)
        return jsonify({"ok": True, "reports": reports})
    except Exception as e:
        app.logger.exception("list_reports failed")
        return jsonify({"ok": False, "error": str(e)}), 500


# SCSI USB disk devices in /proc/mounts: /dev/sda, /dev/sda1, /dev/sdz99, etc.
_SD_BLOCK_DEV_RE = re.compile(r"^/dev/sd[a-z]+\d*$")
_SD_DISK_PREFIX_RE = re.compile(r"^/dev/(sd[a-z]+)")


def _is_export_sd_device(dev: str) -> bool:
    return bool(dev and _SD_BLOCK_DEV_RE.match(dev))


def _sd_disk_prefix(dev: str) -> str | None:
    m = _SD_DISK_PREFIX_RE.match(dev or "")
    return m.group(1) if m else None


def _mountpoints_from_lsblk_node(node: dict) -> list[str]:
    out = []
    mps = node.get("mountpoints")
    if isinstance(mps, list):
        out.extend(str(m) for m in mps if m)
    mp = node.get("mountpoint")
    if mp:
        out.append(str(mp))
    return out


def _internal_usb_source_device() -> str | None:
    """Device mounted at INTERNAL_ROOT (e.g. /dev/sda1)."""
    try:
        src = subprocess.check_output(
            ["findmnt", "-n", "-o", "SOURCE", str(INTERNAL_ROOT)],
            text=True,
            timeout=5,
        ).strip()
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, FileNotFoundError):
        return None
    return src if src.startswith("/dev/") else None


def _internal_usb_sd_prefix() -> str | None:
    """Disk id for the stick that holds /media/usb_internal (e.g. 'sda' for /dev/sda1)."""
    try:
        src = _internal_usb_source_device() or ""
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, FileNotFoundError):
        return None
    if not src.startswith("/dev/sd"):
        return None
    return _sd_disk_prefix(src)


def _is_internal_usb_device(dev: str) -> bool:
    """True for the internal storage device or any partition on the same USB disk."""
    internal_src = _internal_usb_source_device()
    internal_prefix = _internal_usb_sd_prefix()
    dev_prefix = _sd_disk_prefix(dev)
    if internal_src and dev == internal_src:
        return True
    return bool(internal_prefix and dev_prefix and dev_prefix == internal_prefix)


def _list_unmounted_export_blockdevs() -> list[str]:
    """List external USB partitions with filesystems that are currently unmounted."""
    internal_src = _internal_usb_source_device() or "/dev/sda1"
    internal_prefix = _internal_usb_sd_prefix() or _sd_disk_prefix(internal_src)
    try:
        raw = subprocess.check_output(
            ["lsblk", "-J", "-o", "PATH,MOUNTPOINTS,MOUNTPOINT,FSTYPE,TYPE,RM,TRAN"],
            text=True,
            timeout=8,
        )
        tree = json.loads(raw)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError) as e:
        app.logger.warning("[EXPORT] lsblk failed: %s", e)
        return []
    devices = tree.get("blockdevices") or []

    flat_nodes = []

    def _walk(nodes):
        for node in nodes or []:
            flat_nodes.append(node)
            _walk(node.get("children") or [])

    _walk(devices)
    candidates = []
    for d in flat_nodes:
        path = d.get("path") or ""
        if not _is_export_sd_device(path):
            continue
        if _is_internal_usb_device(path):
            continue
        if _mountpoints_from_lsblk_node(d):
            continue
        fstype = d.get("fstype")
        if not fstype:
            continue
        kind = d.get("type")
        if kind not in ("part", "disk"):
            continue
        if (d.get("tran") or "").lower() not in ("", "usb"):
            continue
        rm = str(d.get("rm", "0")).strip()
        removable_first = 0 if rm == "1" else 1
        candidates.append((removable_first, path))
    if not candidates:
        return []
    candidates.sort(key=lambda x: (x[0], x[1]))
    ordered = [path for _, path in candidates]
    app.logger.info("[EXPORT] Auto-mount candidates=%s (internal source %s, prefix %s)", ordered, internal_src, internal_prefix)
    return ordered


def _try_mount_export_via_helper(devpath: str) -> bool:
    if _is_internal_usb_device(devpath):
        app.logger.warning("[EXPORT] Refusing to mount internal USB device as export target: %s", devpath)
        return False
    script = pathlib.Path("/opt/kiosk/scripts/udev_mount_export_usb.sh")
    if not script.is_file():
        app.logger.error("[EXPORT] Mount helper missing: %s", script)
        return False
    try:
        r = subprocess.run(
            ["sudo", "-n", str(script), devpath],
            capture_output=True,
            text=True,
            timeout=45,
        )
        if r.returncode != 0:
            app.logger.warning("[EXPORT] Mount helper exit %s stderr=%s", r.returncode, (r.stderr or "").strip())
            return False
        return True
    except (OSError, subprocess.TimeoutExpired) as e:
        app.logger.warning("[EXPORT] Mount helper failed: %s", e)
        return False


def _prepare_export_mount_if_needed() -> bool:
    """If no export volume is mounted yet, mount the first suitable USB stick at EXPORT_ROOT."""
    devs = _list_unmounted_export_blockdevs()
    if not devs:
        return False
    for dev in devs:
        if _try_mount_export_via_helper(dev):
            return True
    return False


def _list_export_blockdev_candidates() -> list[str]:
    """List all external USB partition candidates (mounted or unmounted)."""
    internal_src = _internal_usb_source_device() or "/dev/sda1"
    internal_prefix = _internal_usb_sd_prefix() or _sd_disk_prefix(internal_src)
    try:
        raw = subprocess.check_output(
            ["lsblk", "-J", "-o", "PATH,FSTYPE,TYPE,RM,TRAN"],
            text=True,
            timeout=8,
        )
        tree = json.loads(raw)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError):
        return []
    flat_nodes = []

    def _walk(nodes):
        for node in nodes or []:
            flat_nodes.append(node)
            _walk(node.get("children") or [])

    _walk(tree.get("blockdevices") or [])
    out = []
    for d in flat_nodes:
        path = d.get("path") or ""
        if not _is_export_sd_device(path):
            continue
        if _is_internal_usb_device(path):
            continue
        if (d.get("type") or "") not in ("part", "disk"):
            continue
        if not d.get("fstype"):
            continue
        if (d.get("tran") or "").lower() not in ("", "usb"):
            continue
        rm = str(d.get("rm", "0")).strip()
        removable_first = 0 if rm == "1" else 1
        out.append((removable_first, path))
    out.sort(key=lambda x: (x[0], x[1]))
    app.logger.info("[EXPORT] Recovery candidates=%s (internal source %s, prefix %s)", [p for _, p in out], internal_src, internal_prefix)
    return [p for _, p in out]


def _is_export_mount_writable(mount_path: pathlib.Path) -> bool:
    """Quick write check so broken pendrives are rejected before copy."""
    probe_dir = mount_path / "Disintegrator-Reports-Exported"
    probe_file = probe_dir / ".export_write_probe.tmp"
    try:
        probe_dir.mkdir(parents=True, exist_ok=True)
        with open(probe_file, "w", encoding="utf-8") as f:
            f.write("ok")
            f.flush()
            os.fsync(f.fileno())
        probe_file.unlink(missing_ok=True)
        return True
    except Exception as e:
        app.logger.warning("[EXPORT] mount write probe failed at %s: %s", mount_path, e)
        return False


def _recover_export_mount() -> pathlib.Path | None:
    """Try candidate external devices until a writable mount is found."""
    for dev in _list_export_blockdev_candidates():
        if not _try_mount_export_via_helper(dev):
            continue
        try:
            p = _scan_mounted_export_path()
        except RuntimeError:
            continue
        if _is_export_mount_writable(p):
            app.logger.info("[EXPORT] recovered writable mount on %s", p)
            return p
    return None


def _scan_mounted_export_path() -> pathlib.Path:
    """Return mount path for an already-mounted external USB (not internal)."""
    export_root = EXPORT_ROOT
    internal_path = INTERNAL_ROOT
    internal_src = _internal_usb_source_device() or "/dev/sda1"
    internal_prefix = _internal_usb_sd_prefix() or _sd_disk_prefix(internal_src)
    # 1. Prefer /media/usb_export when it is actually mounted (device != parent fs)
    if export_root.exists():
        try:
            if export_root.parent.exists():
                if export_root.stat().st_dev != export_root.parent.stat().st_dev:
                    export_src = subprocess.check_output(
                        ["findmnt", "-n", "-o", "SOURCE", str(export_root)],
                        text=True,
                        timeout=5,
                    ).strip()
                    if export_src and not _is_internal_usb_device(export_src):
                        return export_root
        except OSError:
            pass
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired, FileNotFoundError):
            pass
    internal_st_devs = set()
    try:
        if internal_path.exists():
            internal_st_devs.add(internal_path.stat().st_dev)
    except OSError:
        pass
    skip_prefixes = (
        str(internal_path),
        "/boot",
    )
    candidates = []
    seen_mountpoints = set()
    with open("/proc/mounts", "r") as f:
        for line in f:
            parts = line.split()
            if len(parts) < 2:
                continue
            dev, mnt = parts[0], parts[1]
            if not _is_export_sd_device(dev):
                continue
            if _is_internal_usb_device(dev):
                continue
            if mnt == "/":
                continue
            if any(mnt == p or mnt.startswith(p + "/") for p in skip_prefixes):
                continue
            p = pathlib.Path(mnt)
            try:
                if not p.exists() or not p.is_dir():
                    continue
                st = p.stat().st_dev
            except OSError:
                continue
            if st in internal_st_devs:
                continue
            if mnt in seen_mountpoints:
                continue
            seen_mountpoints.add(mnt)
            prefer_non_sda = 0 if dev.startswith("/dev/sda") else 1
            candidates.append((prefer_non_sda, dev, p))
    if candidates:
        candidates.sort(key=lambda x: (-x[0], x[1]))
        chosen = candidates[0]
        app.logger.info("[EXPORT] Using mount %s (device %s, internal source %s, prefix %s)", chosen[2], chosen[1], internal_src, internal_prefix)
        return chosen[2]
    raise RuntimeError("Export pendrive not found in /proc/mounts")


def find_export_mount():
    """Find (or prepare) a mounted external USB volume for report export.

    Uses /proc/mounts first. If a stick is plugged but not mounted, runs the mount helper
    via passwordless sudo and retries. No UUID matching.
    """
    try:
        return _scan_mounted_export_path()
    except RuntimeError:
        pass
    try:
        if _prepare_export_mount_if_needed():
            return _scan_mounted_export_path()
    except Exception as e:
        app.logger.error("[EXPORT] prepare mount failed: %s", e)
    try:
        return _scan_mounted_export_path()
    except RuntimeError:
        raise
    except Exception as e:
        app.logger.error("[EXPORT] Error finding export mount: %s", e)
        raise RuntimeError(f"Failed to find export pendrive: {e}") from e


def _request_is_loopback() -> bool:
    addr = (request.remote_addr or "").strip().lower()
    if addr in ("127.0.0.1", "::1"):
        return True
    return addr.endswith("127.0.0.1")


@app.route("/api/prepare_export_usb", methods=["GET", "POST"])
def api_prepare_export_usb():
    """Mount external USB at EXPORT_ROOT if present (call at user login)."""
    try:
        path = _scan_mounted_export_path()
        if _is_export_mount_writable(path):
            app.logger.info("[EXPORT] prepare: mounted and writable at %s", path)
            return jsonify({"ok": True, "path": str(path), "action": "already_mounted"})
        recovered = _recover_export_mount()
        if recovered is not None:
            app.logger.info("[EXPORT] prepare: switched to writable mount at %s", recovered)
            return jsonify({"ok": True, "path": str(recovered), "action": "mounted"})
        app.logger.warning("[EXPORT] prepare: mounted path is not writable")
        return jsonify({"ok": False, "message": "no_external_usb_ready", "action": "none"}), 200
    except RuntimeError:
        pass
    if _prepare_export_mount_if_needed():
        try:
            path = _scan_mounted_export_path()
            if _is_export_mount_writable(path):
                app.logger.info("[EXPORT] prepare: mounted at %s", path)
                return jsonify({"ok": True, "path": str(path), "action": "mounted"})
            recovered = _recover_export_mount()
            if recovered is not None:
                app.logger.info("[EXPORT] prepare: recovered writable mount at %s", recovered)
                return jsonify({"ok": True, "path": str(recovered), "action": "mounted"})
            app.logger.warning("[EXPORT] prepare: mount found but not writable")
            return jsonify({"ok": False, "message": "no_external_usb_ready", "action": "none"}), 200
        except RuntimeError as e:
            app.logger.warning("[EXPORT] prepare: mount helper ran but scan failed: %s", e)
            return jsonify({"ok": False, "error": str(e), "action": "mount_incomplete"}), 200
    app.logger.info("[EXPORT] prepare: no external USB or mount skipped")
    return jsonify({"ok": False, "message": "no_external_usb_ready", "action": "none"}), 200


def find_pendrive_mount():
    try:
        mounts = []
        with open('/proc/mounts', 'r') as f:
            for line in f:
                parts = line.split()
                if len(parts) >= 2:
                    dev, mnt = parts[0], parts[1]
                    if dev.startswith('/dev/sd') or dev.startswith('/dev/mmcblk') or dev.startswith('/dev/sg'):
                        mounts.append((dev, mnt))
        if not mounts:
            return None
        for dev, mnt in mounts:
            if dev.startswith('/dev/sda'):
                return mnt
        return mounts[0][1]
    except Exception as e:
        app.logger.exception("find_pendrive_mount failed: %s", e)
        return None


_PDF_FN_TS_RE = re.compile(r"_(\d{8}T\d{6})(Z|IST)\.pdf$", re.IGNORECASE)


def _local_tzinfo():
    return IST_TZ


def _iso_to_utc_timestamp(val) -> float | None:
    """Parse report ISO datetime to UTC epoch seconds (naive treated as local wall time)."""
    if not val:
        return None
    t = str(val).strip()
    try:
        if t.endswith("Z"):
            d = datetime.fromisoformat(t[:-1].split(".")[0]).replace(tzinfo=timezone.utc)
            return d.timestamp()
        if "+" in t[10:] or (t.count("-") > 2 and "T" in t):
            d = datetime.fromisoformat(t.replace("Z", "+00:00").split(".")[0])
            if d.tzinfo is None:
                return None
            return d.astimezone(timezone.utc).timestamp()
        d = datetime.fromisoformat(t.split(".")[0])
        if d.tzinfo is None:
            d = d.replace(tzinfo=_local_tzinfo())
        return d.astimezone(timezone.utc).timestamp()
    except (ValueError, TypeError, OSError):
        return None


def _pdf_suffix_utc_timestamp(filename: str) -> float | None:
    m = _PDF_FN_TS_RE.search(filename)
    if not m:
        return None
    try:
        d = datetime.strptime(m.group(1).upper(), "%Y%m%dT%H%M%S")
        suffix_tz = m.group(2).upper()
        d = d.replace(tzinfo=timezone.utc if suffix_tz == "Z" else IST_TZ)
        return d.timestamp()
    except ValueError:
        return None


def _is_non_empty_pdf(path: pathlib.Path) -> bool:
    try:
        return path.is_file() and path.stat().st_size > 0
    except OSError:
        return False


_PDF_BROWSER_ERROR_MARKERS = (
    "your file couldn't be accessed",
    "your file couldn\u2019t be accessed",
    "err_file_not_found",
    "it may have been moved, edited, or deleted",
)


def _pdf_quality_issue(path: pathlib.Path) -> str | None:
    """Return an issue string if a PDF is incomplete, corrupt, or a browser error page."""
    if not _is_non_empty_pdf(path):
        return "PDF file is missing or empty"
    try:
        with open(path, "rb") as f:
            head = f.read(4096)
    except OSError as e:
        return f"PDF cannot be read: {e}"
    if not head.startswith(b"%PDF"):
        return "PDF header is invalid"

    pdfinfo = shutil.which("pdfinfo")
    if pdfinfo:
        try:
            res = subprocess.run([pdfinfo, str(path)], text=True, capture_output=True, timeout=10)
            if res.returncode != 0:
                return (res.stderr or res.stdout or "PDF structure is invalid").strip()
        except Exception as e:
            return f"PDF validation failed: {e}"

    pdftotext = shutil.which("pdftotext")
    if pdftotext:
        try:
            res = subprocess.run([pdftotext, str(path), "-"], text=True, capture_output=True, timeout=10)
            if res.returncode != 0:
                return (res.stderr or "PDF text extraction failed").strip()
            text = " ".join(res.stdout.split()).strip()
            lowered = text.lower()
            for marker in _PDF_BROWSER_ERROR_MARKERS:
                if marker in lowered:
                    return "PDF is a browser file-access error page"
            if len(text) < 20:
                return "PDF has no extractable report text"
        except Exception as e:
            return f"PDF text validation failed: {e}"
    else:
        lowered = head.decode("utf-8", errors="ignore").lower()
        for marker in _PDF_BROWSER_ERROR_MARKERS:
            if marker in lowered:
                return "PDF is a browser file-access error page"

    return None


def _is_exportable_pdf(path: pathlib.Path) -> bool:
    return _pdf_quality_issue(path) is None


def _resolve_report_pdf_on_disk(r: dict) -> pathlib.Path | None:
    """Locate saved PDF for one reports.json row.

    Metadata often omits ``file`` (bridge vs browser storage). Filenames may truncate long
    ``safe_name_id`` to 50 chars, so the numeric id is not always in the name — match by
    UTC timestamp suffix from ``safe_unique_report_path`` and optional basket number.
    """
    for key in ('file', 'filename', 'relative'):
        v = r.get(key)
        if not v:
            continue
        name = pathlib.Path(str(v).replace("\\", "/")).name
        pdf_path = REPORTS_DIR / name
        if _is_exportable_pdf(pdf_path):
            return pdf_path
    rid = r.get('id')
    if rid is not None:
        rid_s = str(rid)
        candidates = [p for p in REPORTS_DIR.glob("*.pdf") if _is_exportable_pdf(p) and rid_s in p.name]
        if candidates:
            candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
            return candidates[0]
    if r.get('name') and rid is not None:
        safe_name = "".join(c for c in str(r['name']) if c.isalnum() or c in "-_.")[:50]
        for pattern in (f"{safe_name}.pdf", f"REPORT_{rid}.pdf"):
            p = REPORTS_DIR / pattern
            if _is_exportable_pdf(p):
                return p
    ref_times = []
    for key in ('completedAt', 'createdAt', 'testEndTime'):
        ts = _iso_to_utc_timestamp(r.get(key))
        if ts is not None:
            ref_times.append(ts)
    if ref_times:
        basket = r.get('basket')
        best_p = None
        best_delta = 1e18
        for f in REPORTS_DIR.glob("*.pdf"):
            if not _is_exportable_pdf(f):
                continue
            fts = _pdf_suffix_utc_timestamp(f.name)
            if fts is None:
                continue
            if basket is not None:
                needle = f"_Basket_{basket}_"
                if needle not in f.name.replace(" ", "_") and f"Basket_{basket}_" not in f.name.replace(" ", "_"):
                    continue
            for rt in ref_times:
                delta = abs(fts - rt)
                if delta < best_delta:
                    best_delta = delta
                    best_p = f
        if best_p is not None and best_delta <= 30:
            return best_p
    return None


def _list_all_report_pdfs() -> list[pathlib.Path]:
    """Every non-empty PDF already saved under internal storage (source of truth for bulk export)."""
    return sorted(
        (f for f in REPORTS_DIR.glob("*.pdf") if _is_exportable_pdf(f)),
        key=lambda p: p.name.lower(),
    )


def _safe_report_stem_for_pdf(r: dict) -> str:
    rid = str(r.get("id") or "report")
    rname = str(r.get("name") or "report")
    base = f"{rname}_{rid}".strip("_")
    safe = "".join(c for c in base if c.isalnum() or c in "-_.")[:50]
    return safe or f"report_{rid}"


def _build_preview_like_html(report_row: dict) -> str:
    """Build a table-based, preview-like HTML report from stored metadata."""
    def esc(v):
        if v is None:
            return "N/A"
        return html.escape(str(v))

    enriched_row = _apply_factory_context(report_row, override=False)
    fs = dict(enriched_row.get("factorySettings") or {})

    def _first_value(*values):
        for value in values:
            if value is None:
                continue
            value_s = str(value).strip()
            if value_s and value_s.upper() != "N/A":
                return value
        return "N/A"

    def _fmt_dt(val):
        if not val:
            return "N/A"
        try:
            d = datetime.fromisoformat(str(val).replace("Z", "+00:00"))
            if d.tzinfo is None:
                d = d.replace(tzinfo=IST_TZ)
            d = d.astimezone(IST_TZ)
            return d.strftime("%d/%m/%Y, %H:%M:%S")
        except Exception:
            return str(val)

    def _fmt_duration(val):
        try:
            total = int(float(val or 0))
            return f"{total // 3600:02d}:{(total % 3600) // 60:02d}:{total % 60:02d}"
        except (TypeError, ValueError):
            return esc(val or "N/A")

    def _fmt_temp(val):
        try:
            return f"{float(val):.2f}&deg;C"
        except (TypeError, ValueError):
            return esc(val or "N/A")

    title = esc(enriched_row.get("name") or f"Report {enriched_row.get('id', '')}")
    rtype = str(enriched_row.get("type") or "").strip().lower()
    basket = enriched_row.get("basket") or enriched_row.get("beaker") or 1
    basket_s = str(basket)
    product = enriched_row.get("productName2") if basket_s == "2" else enriched_row.get("productName1")
    batch = enriched_row.get("batch2") if basket_s == "2" else enriched_row.get("batch1")

    duration_seconds = enriched_row.get("durationSeconds")
    if duration_seconds is None:
        duration_seconds = enriched_row.get("duration")

    company_name = _first_value(fs.get("companyName"), enriched_row.get("companyName"), "Client Company Name")
    model_no = _first_value(enriched_row.get("modelNo"), fs.get("modelNo"))
    serial_no = _first_value(enriched_row.get("serialNo"), fs.get("serialNo"))
    instrument_no = _first_value(
        enriched_row.get("instrumentNo"),
        enriched_row.get("instrumentId"),
        fs.get("instrumentNo"),
        fs.get("instrumentId"),
    )
    location = _first_value(enriched_row.get("location"), fs.get("companyLocation"), fs.get("location"))
    last_validation = _first_value(enriched_row.get("lastValidationDate"), fs.get("lastValidationDate"))
    next_validation = _first_value(
        enriched_row.get("nextValidationDue"),
        enriched_row.get("nextValidationDate"),
        fs.get("nextValidationDate"),
    )

    rows = [
        ("Model No", esc(model_no)),
        ("Serial No", esc(serial_no)),
        ("Instrument No", esc(instrument_no)),
        ("Last Validation Date", esc(last_validation)),
        (f"Product Name ({esc(basket)})", esc(product or enriched_row.get("product") or "N/A")),
        ("Batch Number", esc(batch or enriched_row.get("batch") or "N/A")),
        ("Mode", esc(enriched_row.get("mode") or "N/A")),
        ("Set Temperature", _fmt_temp(enriched_row.get("setTemperature"))),
        ("Test Duration", _fmt_duration(duration_seconds)),
        ("Test Status", esc(enriched_row.get("status") or "N/A")),
        ("Start Time", esc(_fmt_dt(enriched_row.get("testStartTime")))),
        ("End Time", esc(_fmt_dt(enriched_row.get("testEndTime") or enriched_row.get("completedAt")))),
        ("Location", esc(location)),
        ("Next Validation Due", esc(next_validation)),
    ]

    if rtype == "validation":
        rows.extend([
            ("Validation Subtype", esc(enriched_row.get("validationSubtype") or "N/A")),
            ("Measured Temperature", _fmt_temp(enriched_row.get("measuredTemperature"))),
            ("Deviation", esc(enriched_row.get("deviation") or "N/A")),
            ("Calibration Offset", esc(enriched_row.get("calibrationOffset") or "N/A")),
        ])

    table_rows = "".join(f"<tr><th>{k}</th><td>{v}</td></tr>" for k, v in rows)
    tube_table = ""
    mode_key = str(report_row.get("mode") or "").strip().lower()
    if rtype != "validation" and mode_key == "manual":
        try:
            basket_config = int(enriched_row.get("basketConfig") or 0)
        except (TypeError, ValueError):
            basket_config = 0
        vessel_times = enriched_row.get("vesselTimes") or {}
        hole_times = enriched_row.get("holeCompletionTimes") or {}

        def _fmt_seconds(val):
            try:
                total = int(float(val))
                if total < 0:
                    return "N/A"
                return f"{total // 3600:02d}:{(total % 3600) // 60:02d}:{total % 60:02d}"
            except (TypeError, ValueError):
                return "N/A"

        if basket_config > 0:
            tube_rows = []
            for idx in range(1, basket_config + 1):
                value = vessel_times.get(str(idx), vessel_times.get(idx))
                if value is None:
                    value = hole_times.get(str(idx), hole_times.get(idx))
                    value = _fmt_seconds(value)
                tube_rows.append(f"<tr><td>Tube {idx}</td><td>{esc(value or '--:--:--')}</td></tr>")
            tube_table = (
                f"<h3>Basket {esc(basket)} TUBE COMPLETION STATUS</h3>"
                "<table><tr><th>Tube</th><th>Time (MM:SS)</th></tr>"
                + "".join(tube_rows)
                + "</table>"
            )
    min_temp = enriched_row.get("minTemp")
    max_temp = enriched_row.get("maxTemp")
    minmax = ""
    if min_temp is not None or max_temp is not None:
        minmax = f"<p><strong>Min/Max Temperature:</strong> {_fmt_temp(min_temp)} / {_fmt_temp(max_temp)}</p>"
    operator = esc(enriched_row.get("operatorName") or "N/A")
    employee = esc(enriched_row.get("operatorId") or "N/A")
    return (
        "<!doctype html><html><head><meta charset='utf-8'>"
        "<style>"
        "body{font-family:'Times New Roman',serif;margin:0;padding:0;color:#111;background:#fff;font-size:10pt;}"
        ".report-preview-container{max-width:210mm;margin:0 auto;padding:8mm 10mm;}"
        ".brand{text-align:center;font-size:14pt;font-weight:bold;margin:0 0 2px 0;}"
        ".company{text-align:center;font-size:10pt;margin:0 0 6px 0;}"
        "h1{text-align:center;font-size:12pt;margin:0 0 8px 0;}h2{text-align:center;font-size:11pt;margin:0 0 10px 0;color:#111;}"
        "table{width:100%;border-collapse:collapse;margin-top:8px;}"
        "th,td{border:1px solid #000;padding:5px;vertical-align:top;}"
        "th{width:34%;background:#f3f4f6;text-align:left;font-weight:bold;}"
        "h3{font-size:11pt;margin:12px 0 4px 0;text-align:center;}"
        "p{margin:6px 0;}"
        "</style></head><body><div class='report-preview-container'>"
        "<div class='brand'>RAISE LAB EQUIPMENT</div>"
        f"<div class='company'>{esc(company_name)}</div>"
        f"<h2>{'VALIDATION REPORT' if rtype == 'validation' else 'TEST REPORT'}</h2>"
        f"<h1>{title}</h1>"
        f"<table>{table_rows}</table>"
        f"{tube_table}"
        f"{minmax}"
        f"<p><strong>Operator Name:</strong> {operator}</p>"
        f"<p><strong>Employee ID:</strong> {employee}</p>"
        "<p><strong>Remarks:</strong></p>"
        "<p><strong>Reviewed By:</strong></p>"
        "</div></body></html>"
    )


def _render_report_json_pdf(report_row: dict) -> pathlib.Path:
    """Generate a unique PDF from one reports.json row."""
    ts = _now_ist().strftime("%Y%m%dT%H%M%SIST")
    stem = _safe_report_stem_for_pdf(report_row)
    out_pdf = REPORTS_DIR / f"{stem}_{ts}.pdf"
    preview_html = report_row.get("previewHtml") or report_row.get("reportHtml") or report_row.get("html")
    if isinstance(preview_html, str) and preview_html.strip():
        html_text = preview_html
    else:
        html_text = _build_preview_like_html(report_row)
    try:
        print_formats.html_to_pdf_with_wkhtmltopdf(html_text, out_pdf)
    except Exception:
        tmp_html = REPORTS_DIR / f"{stem}_{ts}.html"
        with open(tmp_html, "w", encoding="utf-8") as f:
            f.write(html_text)
        chrome_bin = shutil.which("chromium") or shutil.which("chromium-browser") or "chromium"
        subprocess.check_call(
            [
                chrome_bin, "--headless", "--disable-gpu", "--no-sandbox",
                "--allow-file-access-from-files", "--disable-web-security",
                f"--print-to-pdf={out_pdf}", f"file://{tmp_html}"
            ],
            timeout=45,
        )
        try:
            tmp_html.unlink()
        except Exception:
            pass
    issue = _pdf_quality_issue(out_pdf)
    if issue:
        raise RuntimeError(f"Generated PDF is invalid for report id={report_row.get('id')}: {issue}")
    return out_pdf


def _resolve_preview_pdf_strict(r: dict) -> pathlib.Path | None:
    """Resolve exact saved PDF reference from metadata fields only."""
    for key in ("file", "filename", "relative"):
        v = r.get(key)
        if not v:
            continue
        name = pathlib.Path(str(v).replace("\\", "/")).name
        p = REPORTS_DIR / name
        if _is_exportable_pdf(p):
            return p
    # Legacy rows may miss file metadata. Match only the browser preview PDF
    # naming pattern, not backend-regenerated fallback names.
    rid = r.get("id")
    rname = str(r.get("name") or "").strip()
    if rid is not None and rname:
        safe = "".join(c if (c.isascii() and (c.isalnum() or c in "-_ ")) else "_" for c in rname)
        safe = re.sub(r"\s+", "_", safe.strip())
        expected_prefix = f"{safe}_{rid}"
        cands = [p for p in REPORTS_DIR.glob(f"{expected_prefix}*.pdf") if _is_exportable_pdf(p)]
        if cands:
            cands.sort(key=lambda x: x.stat().st_mtime, reverse=True)
            return cands[0]
    return None


def _verified_copy_file(src: pathlib.Path, dest: pathlib.Path) -> None:
    """Copy report with stability + hash verification to avoid partial exported data."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_name(dest.name + ".~part")
    try:
        if tmp.exists():
            tmp.unlink()
    except OSError:
        pass
    src_stat_1 = src.stat()
    src_sz = src_stat_1.st_size
    if src_sz <= 0:
        raise OSError("source PDF is empty")
    if src.suffix.lower() == ".pdf":
        issue = _pdf_quality_issue(src)
        if issue:
            raise OSError(f"source PDF is not exportable: {issue}")
    time.sleep(0.2)
    src_stat_2 = src.stat()
    if src_stat_1.st_size != src_stat_2.st_size or src_stat_1.st_mtime_ns != src_stat_2.st_mtime_ns:
        raise OSError("source file still being written")

    src_hash = hashlib.sha256()
    with open(src, "rb") as inf:
        with open(tmp, "wb") as outf:
            while True:
                chunk = inf.read(1024 * 1024)
                if not chunk:
                    break
                src_hash.update(chunk)
                outf.write(chunk)
            outf.flush()
            os.fsync(outf.fileno())
    st_tmp = tmp.stat().st_size
    if st_tmp != src_sz:
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        raise OSError(f"incomplete write: {st_tmp} != {src_sz}")
    os.replace(tmp, dest)
    if dest.stat().st_size != src_sz:
        raise OSError("final size mismatch after replace")

    dest_hash = hashlib.sha256()
    with open(dest, "rb") as df:
        while True:
            chunk = df.read(1024 * 1024)
            if not chunk:
                break
            dest_hash.update(chunk)
    if dest_hash.digest() != src_hash.digest():
        raise OSError("hash mismatch after copy")
    if dest.suffix.lower() == ".pdf":
        issue = _pdf_quality_issue(dest)
        if issue:
            raise OSError(f"exported PDF is not valid: {issue}")


@app.route("/api/export_reports", methods=["POST"])
def api_export_reports():
    try:
        mount_path = find_export_mount()
        if not _is_export_mount_writable(mount_path):
            recovered = _recover_export_mount()
            if recovered is None:
                raise RuntimeError("Pendrive mount exists but is not writable")
            mount_path = recovered
        export_dir = mount_path / 'Disintegrator-Reports-Exported'
    except RuntimeError as e:
        # Pendrive not mounted or not found
        return jsonify({"error": "E4001", "message": "Pendrive not detected. Please connect the pendrive and try USB export again."}), 400
    try:
        data = request.get_json(force=True, silent=True) or {}
        report_id = data.get('report_id')
        explicit_name = (data.get('report_file') or data.get('file') or data.get('filename') or data.get('relative') or '').strip()
        filter_type = (data.get('filter') or 'all')
        if isinstance(filter_type, str):
            filter_type = filter_type.strip().lower()
        if filter_type in ('', 'preview', 'all_reports'):
            filter_type = 'all'
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        export_dir.mkdir(parents=True, exist_ok=True)
        exported = []
        failed = []
        reports_meta = []
        meta_file = STORAGE_DIR / "reports.json"
        if meta_file.exists():
            try:
                with open(meta_file, 'r', encoding='utf-8') as f:
                    reports_meta = json.load(f)
                if not isinstance(reports_meta, list):
                    reports_meta = []
            except Exception:
                pass
        pdfs_to_export = []
        missing_sources = []
        if report_id:
            rmatch = next(
                (r for r in reports_meta if r.get('id') == report_id or str(r.get('id')) == str(report_id)),
                None,
            )
            if rmatch:
                p = _resolve_preview_pdf_strict(rmatch) or _resolve_report_pdf_on_disk(rmatch)
                if p:
                    pdfs_to_export.append(p)
                else:
                    try:
                        repaired = _render_report_json_pdf(rmatch)
                        pdfs_to_export.append(repaired)
                        app.logger.warning("[EXPORT] repaired missing/invalid report PDF for id=%s -> %s", report_id, repaired.name)
                    except Exception as repair_error:
                        app.logger.warning("[EXPORT] repair failed for report id=%s: %s", report_id, repair_error)
                        missing_sources.append(str(rmatch.get("id") or report_id))
            elif explicit_name:
                safe_explicit = pathlib.Path(explicit_name.replace("\\", "/")).name
                safe_explicit = "".join(c for c in safe_explicit if c.isalnum() or c in "-_.")
                if safe_explicit:
                    p = REPORTS_DIR / safe_explicit
                    if _is_non_empty_pdf(p):
                        pdfs_to_export.append(p)
            else:
                rid_s = str(report_id)
                candidates = [p for p in REPORTS_DIR.glob("*.pdf") if _is_non_empty_pdf(p) and rid_s in p.name]
                candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
                if candidates:
                    pdfs_to_export.append(candidates[0])
                else:
                    missing_sources.append(rid_s)
        else:
            # Bulk export prefers saved PDFs. If an older saved PDF is corrupt,
            # regenerate that report from metadata so the USB never gets a bad PDF.
            seen_names = set()
            if filter_type == 'all':
                seen_report_ids = set()
                for r in reports_meta:
                    rid = str(r.get("id") or "")
                    if rid:
                        seen_report_ids.add(rid)
                    p = _resolve_preview_pdf_strict(r) or _resolve_report_pdf_on_disk(r)
                    if p is None:
                        try:
                            p = _render_report_json_pdf(r)
                            app.logger.warning("[EXPORT] repaired missing/invalid report PDF for id=%s -> %s", rid or "unknown", p.name)
                        except Exception as repair_error:
                            app.logger.warning("[EXPORT] repair failed for report id=%s: %s", rid or "unknown", repair_error)
                            missing_sources.append(rid or "unknown")
                            continue
                    if p.name not in seen_names:
                        pdfs_to_export.append(p)
                        seen_names.add(p.name)
                for p in _list_all_report_pdfs():
                    if p.name not in seen_names:
                        pdfs_to_export.append(p)
                        seen_names.add(p.name)
            else:
                for r in reports_meta:
                    rtype = str(r.get("type") or "").strip().lower()
                    if filter_type and filter_type not in rtype and rtype not in filter_type:
                        continue
                    p = _resolve_preview_pdf_strict(r) or _resolve_report_pdf_on_disk(r)
                    if p is None:
                        try:
                            p = _render_report_json_pdf(r)
                            app.logger.warning("[EXPORT] repaired missing/invalid report PDF for id=%s -> %s", r.get("id") or "unknown", p.name)
                        except Exception as repair_error:
                            app.logger.warning("[EXPORT] repair failed for report id=%s: %s", r.get("id") or "unknown", repair_error)
                            missing_sources.append(str(r.get("id") or "unknown"))
                            continue
                    if p and p.name not in seen_names:
                        pdfs_to_export.append(p)
                        seen_names.add(p.name)
            app.logger.info("[EXPORT] bulk: %d PDF(s) from %s (client filter=%s)", len(pdfs_to_export), REPORTS_DIR, filter_type)
        if not pdfs_to_export:
            if missing_sources:
                return jsonify({
                    "error": "E4005",
                    "message": "Saved report PDF source is missing for one or more reports.",
                    "missing_report_ids": missing_sources,
                }), 400
            return jsonify({
                "error": "E4002",
                "message": "No report PDFs found to export. Ensure reports are saved and that the device has report files (or sync storage to bridge if using filtered export)."
            }), 400
        for pdf_path in pdfs_to_export:
            dest = export_dir / pdf_path.name
            try:
                src_sz = pdf_path.stat().st_size
                _verified_copy_file(pdf_path, dest)
                if dest.stat().st_size != src_sz:
                    raise OSError("post-copy size mismatch")
                app.logger.info("[EXPORT] copied %s -> %s (%d bytes)", pdf_path.name, dest, src_sz)
                exported.append(str(dest))
            except Exception as e:
                app.logger.warning("[EXPORT] failed %s: %s", pdf_path, e)
                failed.append({"file": str(pdf_path), "error": str(e)})
                try:
                    if dest.exists():
                        dest.unlink()
                except OSError:
                    pass
        if not report_id and meta_file.exists():
            try:
                meta_dest = export_dir / meta_file.name
                _verified_copy_file(meta_file, meta_dest)
                exported.append(str(meta_dest))
                app.logger.info("[EXPORT] copied reports.json (%d bytes)", meta_dest.stat().st_size)
            except Exception as e:
                app.logger.warning("[EXPORT] reports.json: %s", e)
                failed.append({"file": "reports.json", "error": str(e)})
        if failed:
            return jsonify({
                "ok": False,
                "error": "E4003",
                "message": "Export incomplete: not all files were written to the USB. Safely remove and reconnect the pendrive, then try again.",
                "exported": exported,
                "failed": failed,
            }), 400
        try:
            os.sync()
        except (AttributeError, OSError):
            pass
        total_bytes = 0
        for ep in exported:
            try:
                p = pathlib.Path(ep)
                if p.suffix.lower() == ".pdf" and p.is_file():
                    total_bytes += p.stat().st_size
            except OSError:
                pass
        return jsonify({
            "ok": True,
            "exported": exported,
            "pdf_count": len(pdfs_to_export),
            "total_bytes": total_bytes,
        })
    except Exception as e:
        app.logger.exception("Export failed")
        err_str = str(e).lower()
        pendrive_keywords = ['mount', 'no such file', 'no such device', 'read-only', 'permission denied', 'input/output error', 'pendrive']
        if any(k in err_str for k in pendrive_keywords):
            return jsonify({
                "error": "E4001",
                "message": "Pendrive not detected. Please connect the pendrive and try USB export again."
            }), 400
        return jsonify({
            "error": "E4004",
            "message": f"Export failed: {str(e) or 'unknown export error'}"
        }), 400


@app.route('/api/latest_temps', methods=['GET'])
def api_latest_temps():
    try:
        d = bridge_services.get_latest_temps()
        ts = d.get("timestamp") or 0
        if ts <= 0:
            return jsonify({"t1": None, "t2": None, "ext1": None, "ext2": None, "ts": None})
        return jsonify({
            "t1": d.get("IR1"), "t2": d.get("IR2"),
            "ext1": d.get("EXT1"), "ext2": d.get("EXT2"),
            "ts": ts
        })
    except Exception as e:
        app.logger.exception("api_latest_temps failed: %s", e)
        return jsonify({"t1": None, "t2": None, "ext1": None, "ext2": None, "ts": None})


@app.route('/api/connection_status', methods=['GET'])
def api_connection_status():
    status = bridge_services.get_connection_status()
    try:
        temps = bridge_services.get_latest_temps()
        status["last_temps"] = (temps.get("timestamp") or 0) > 0
    except Exception:
        status["last_temps"] = False
    return jsonify(status)


@app.route('/api/validation_status', methods=['GET'])
def api_validation_status():
    basket = request.args.get('basket')
    if not basket:
        return jsonify({'ok': False, 'error': 'missing_basket'}), 400
    return jsonify({'ok': True, 'strokes': 0})


def list_all_report_ids():
    return [f.stem for f in REPORTS_DIR.glob("*.pdf") if f.is_file()]


def get_report_ids_by_type(filter_type):
    meta_path = STORAGE_DIR / "reports.json"
    reports_meta = []
    if meta_path.exists():
        try:
            with open(meta_path, 'r') as f:
                reports_meta = json.load(f)
        except Exception:
            pass
    matching_ids = []
    for f in REPORTS_DIR.glob("*.pdf"):
        if not f.is_file():
            continue
        name = f.stem
        report_meta = next((r for r in reports_meta if r.get('id') in name or name in r.get('id', '')), None)
        if report_meta:
            report_type = (report_meta.get('type') or '').lower()
            if filter_type.lower() in report_type or report_type in filter_type.lower():
                matching_ids.append(name)
        elif filter_type.lower() in name.lower():
            matching_ids.append(name)
    return matching_ids


@app.route('/api/export', methods=['POST'])
def api_export():
    data = request.get_json(silent=True)
    if not data:
        return jsonify({"error": "missing json body"}), 400
    report_id = data.get('report_id')
    filter_type = data.get('filter')

    def fetch_report_bytes(rid):
        candidates = [p for p in REPORTS_DIR.glob(f"*{rid}*")]
        if not candidates:
            raise FileNotFoundError(f"Report {rid} not found")
        path = candidates[0]
        with open(path, 'rb') as f:
            return f.read(), path.name

    try:
        if report_id:
            content, name = fetch_report_bytes(report_id)
            return send_file(io.BytesIO(content), as_attachment=True, download_name=name)
        if filter_type:
            if filter_type == 'all':
                report_ids = list_all_report_ids()
            else:
                report_ids = get_report_ids_by_type(filter_type)
            if not report_ids:
                return jsonify({"error": "no reports match filter", "filter": filter_type}), 404
            mem = io.BytesIO()
            with zipfile.ZipFile(mem, 'w', zipfile.ZIP_DEFLATED) as z:
                for rid in report_ids:
                    try:
                        content, name = fetch_report_bytes(rid)
                        z.writestr(name, content)
                    except FileNotFoundError:
                        pass
            mem.seek(0)
            return send_file(mem, as_attachment=True, download_name=f"reports_{filter_type}.zip")
        return jsonify({"error": "must provide report_id or filter"}), 400
    except Exception as e:
        app.logger.exception("Export failed")
        return jsonify({"error": str(e)}), 500


@app.route('/api/export_report', methods=['POST'])
def api_export_report():
    try:
        data = request.get_json(force=True)
        report_id = data.get('report_id')
        if not report_id:
            return jsonify({'ok': False, 'error': 'missing_report_id'}), 400
        src = None
        rmatch = None
        meta_file = STORAGE_DIR / "reports.json"
        if meta_file.exists():
            try:
                with open(meta_file, "r", encoding="utf-8") as f:
                    reports_meta = json.load(f)
                if isinstance(reports_meta, list):
                    rmatch = next((r for r in reports_meta if r.get("id") == report_id or str(r.get("id")) == str(report_id)), None)
                    if rmatch:
                        src = _resolve_preview_pdf_strict(rmatch) or _resolve_report_pdf_on_disk(rmatch)
            except Exception as e:
                app.logger.warning("api_export_report preview resolution failed: %s", e)
        if src is None:
            candidates = [p for p in REPORTS_DIR.glob(f"*{report_id}*")]
            if not candidates:
                if rmatch:
                    try:
                        src = _render_report_json_pdf(rmatch)
                        app.logger.warning("[EXPORT] repaired missing/invalid report PDF for id=%s -> %s", report_id, src.name)
                    except Exception as repair_error:
                        app.logger.warning("[EXPORT] repair failed for report id=%s: %s", report_id, repair_error)
                        return jsonify({'ok': False, 'error': 'report_not_found', 'report_id': report_id}), 404
                else:
                    return jsonify({'ok': False, 'error': 'report_not_found', 'report_id': report_id}), 404
            else:
                valid_candidates = [p for p in candidates if _is_exportable_pdf(p)]
                if valid_candidates:
                    valid_candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
                    src = valid_candidates[0]
                elif rmatch:
                    src = _render_report_json_pdf(rmatch)
                else:
                    return jsonify({'ok': False, 'error': 'report_not_found', 'report_id': report_id}), 404
        try:
            mount_path = find_export_mount()
            if not _is_export_mount_writable(mount_path):
                recovered = _recover_export_mount()
                if recovered is None:
                    raise RuntimeError("export mount is not writable")
                mount_path = recovered
        except RuntimeError:
            return jsonify({'ok': False, 'error': 'pendrive_not_found'}), 500
        dest_dir = mount_path / 'Disintegrator-Reports-Exported'
        dest_dir.mkdir(parents=True, exist_ok=True)
        dest = dest_dir / src.name
        _verified_copy_file(src, dest)
        return jsonify({'ok': True, 'device': str(mount_path), 'path': str(dest)})
    except Exception as e:
        app.logger.exception("api_export_report failed: %s", e)
        return jsonify({'ok': False, 'error': str(e)}), 500


@app.route("/api/factory_reset", methods=["POST"])
def api_factory_reset():
    """Delete all report files (PDF, txt, thermal txt, tmp HTML) and clear reports.json. Frontend handles users/recipes via storage."""
    try:
        deleted_count = 0
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        for f in REPORTS_DIR.iterdir():
            if f.is_file():
                try:
                    f.unlink()
                    deleted_count += 1
                except Exception as e:
                    app.logger.warning("Could not delete report file %s: %s", f.name, e)
        reports_json = STORAGE_DIR / "reports.json"
        if reports_json.exists():
            with open(reports_json, "w", encoding="utf-8") as fp:
                json.dump([], fp)
        return jsonify({"ok": True, "deleted_reports": deleted_count}), 200
    except Exception as e:
        app.logger.exception("factory_reset failed: %s", e)
        return jsonify({"ok": False, "error": str(e)}), 500


@app.route('/api/set_device_datetime', methods=['POST'])
def api_set_device_datetime():
    role = request.headers.get('X-User-Role', '').lower()
    if role not in ALLOWED_DATETIME_ROLES:
        return jsonify({'ok': False, 'error': 'forbidden'}), 403

    try:
        data = request.get_json(force=True, silent=True) or {}
        ts = data.get('datetime')
        if not ts:
            return jsonify({'ok': False, 'error': 'missing_datetime'}), 400

        user_dt = _parse_ist_wall_time(ts)
        return jsonify(_set_system_and_rtc_ist(user_dt))
    except subprocess.CalledProcessError as e:
        err_msg = (e.stderr or e.stdout or str(e)).strip() or "Failed to set system/RTC time"
        app.logger.exception("timedatectl/hwclock failed: %s", err_msg)
        return jsonify({'ok': False, 'error': 'set_time_failed', 'detail': err_msg}), 500
    except subprocess.TimeoutExpired as e:
        app.logger.exception("setting system/RTC time timed out: %s", e)
        return jsonify({'ok': False, 'error': 'set_time_timeout'}), 500
    except ValueError as e:
        return jsonify({'ok': False, 'error': 'invalid_datetime', 'detail': str(e)}), 400
    except Exception as e:
        app.logger.exception("api_set_device_datetime failed: %s", e)
        return jsonify({'ok': False, 'error': str(e)}), 500


def _get_ipv4_addresses_for_display():
    try:
        proc = subprocess.run(["hostname", "-I"], capture_output=True, text=True, timeout=10)
        raw = (proc.stdout or "").strip()
        if raw:
            parts = [p for p in raw.split() if p]
            non_lo = [p for p in parts if not p.startswith("127.")]
            return " ".join(non_lo if non_lo else parts)
    except (OSError, subprocess.TimeoutExpired, FileNotFoundError):
        pass
    for ip_cmd in (["ip", "-4", "-o", "addr", "show", "scope", "global"], ["/sbin/ip", "-4", "-o", "addr", "show", "scope", "global"]):
        try:
            proc = subprocess.run(ip_cmd, capture_output=True, text=True, timeout=10)
            if proc.returncode != 0:
                continue
            found = re.findall(r"\binet (\d+\.\d+\.\d+\.\d+)/", proc.stdout or "")
            if found:
                return " ".join(found)
        except (OSError, subprocess.TimeoutExpired, FileNotFoundError):
            continue
    return ""


def _factory_support_run_systemctl_ssh():
    errors = []
    for cmd in (["sudo", "systemctl", "enable", "ssh"], ["sudo", "systemctl", "start", "ssh"]):
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            if proc.returncode != 0:
                err = (proc.stderr or proc.stdout or "").strip() or f"exit {proc.returncode}"
                errors.append(f"{' '.join(cmd)}: {err}")
        except subprocess.TimeoutExpired:
            errors.append(f"{' '.join(cmd)}: timeout")
        except Exception as e:
            errors.append(f"{' '.join(cmd)}: {e}")
    return errors


@app.route("/api/support/factory/ping", methods=["GET"])
def factory_support_ping():
    return jsonify({"ok": True, "factory_support_api": True}), 200


@app.route("/api/support/factory/enable-ssh", methods=["POST"])
def factory_support_enable_ssh():
    errors = _factory_support_run_systemctl_ssh()
    if errors:
        return jsonify({"ok": False, "error": "; ".join(errors)}), 200
    return jsonify({"ok": True}), 200


@app.route("/api/support/factory/verify", methods=["POST"])
def factory_support_verify():
    try:
        data = request.get_json(force=True, silent=True) or {}
        username = (data.get("username") or "").strip()
        password = data.get("password") or ""
        if username != _FACTORY_SUPPORT_USER or password != _FACTORY_SUPPORT_PASSWORD:
            return jsonify({"error": "Invalid username or password"}), 401
        ssh_errors = _factory_support_run_systemctl_ssh()
        addresses = _get_ipv4_addresses_for_display()
        return jsonify(
            {
                "ok": True,
                "addresses": addresses,
                "ssh_ok": len(ssh_errors) == 0,
                "ssh_error": "; ".join(ssh_errors) if ssh_errors else "",
            }
        ), 200
    except Exception:
        app.logger.exception("factory_support_verify")
        return jsonify({"error": "Could not complete factory support request"}), 500


# =================== MAIN =======================

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=True)
