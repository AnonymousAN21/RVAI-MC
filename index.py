from __future__ import annotations

import io
import itertools
import logging
import math
import queue
import sys
import threading
import time
import tkinter as tk
from collections import deque
from dataclasses import dataclass
from logging.handlers import RotatingFileHandler

import requests

try:
    from PIL import Image, ImageDraw, ImageOps, ImageTk
except ImportError:
    Image = None

API_URL = "https://rvai-be-henna.vercel.app/api/absen/scan"
FIELD = "token"
TIMEOUT = 5                 # seconds a single API request may take
IMAGE_TIMEOUT = 4
IMAGE_CACHE_MAX = 50
WORKERS = 5                 # how many requests can be in flight at the same time
RESET_MS = 2600             # how long a result stays on screen
FAST_RESET_MS = 1400        # shorter when more results are waiting to be shown
KEY_GAP = 0.3
DUPLICATE_COOLDOWN = 2.0    # seconds before the same account can be scanned again
FPS_MS = 16

# Scanner input (Windows Raw Input: every scanner gets its own buffer)
RAW_VID_PID = ["VID_26F1&PID_8801"]   # only these devices count as scanners; your normal keyboard is ignored
RAW_KEY_GAP = 0.3                     # seconds of silence after which a half-typed code is dropped

# Real tokens are 58 characters long. Anything outside this range is treated as a corrupted scan.
MIN_LEN = 40
MAX_LEN = 80

LOG_FILE = "scanner.log"
LOG_BODY_MAX = 2000

COLORS = {
    "idle":    ("#111827", "#ffffff", "#9ca3af", "#38bdf8"),
    "wait":    ("#facc15", "#1f2937", "#4b5563", "#1f2937"),
    "success": ("#16a34a", "#ffffff", "#dcfce7", "#ffffff"),
    "error":   ("#dc2626", "#ffffff", "#fee2e2", "#ffffff"),
}

NAME_KEYS = (
    "nama_lengkap",
    "nama_siswa",
    "nama",
    "full_name",
    "name",
    "student_name",
    "siswa_name",
    "display_name",
    "username",
)
PICTURE_KEYS = ("profile_picture", "foto", "photo", "avatar", "picture", "image")
PHOTO_SCALES = (0.15, 0.3, 0.45, 0.6, 0.75, 0.88, 0.96, 1.0, 1.05)


def setup_logger() -> logging.Logger:
    logger = logging.getLogger("scanner")
    logger.setLevel(logging.DEBUG)
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")

    file_handler = RotatingFileHandler(LOG_FILE, maxBytes=1_000_000, backupCount=3, encoding="utf-8")
    file_handler.setFormatter(fmt)
    console = logging.StreamHandler()
    console.setFormatter(fmt)

    logger.addHandler(file_handler)
    logger.addHandler(console)
    return logger


log = setup_logger()


def short(text: str, limit: int = LOG_BODY_MAX) -> str:
    text = (text or "").strip()
    return text if len(text) <= limit else f"{text[:limit]}... [+{len(text) - limit} chars]"


def mask(token: str) -> str:
    """Never write full tokens to the log."""
    return f"{token[:6]}...{token[-4:]}" if len(token) > 12 else "***"


def _search_name_recursive(obj, depth: int = 0) -> str:
    if depth > 4 or not isinstance(obj, dict):
        return ""
    for k in NAME_KEYS:
        val = obj.get(k)
        if isinstance(val, str) and val.strip():
            return val.strip()
    first = obj.get("first_name") or obj.get("nama_depan")
    last = obj.get("last_name") or obj.get("nama_belakang")
    if isinstance(first, str) and first.strip():
        full = f"{first.strip()} {last.strip()}" if isinstance(last, str) and last.strip() else first.strip()
        return full
    for k, val in obj.items():
        if isinstance(val, str) and val.strip():
            lk = k.lower()
            if ("nama" in lk or "name" in lk) and not any(
                skip in lk for skip in ("file", "class", "kelas", "event", "status", "role", "type")
            ):
                return val.strip()
    for val in obj.values():
        if isinstance(val, dict):
            found = _search_name_recursive(val, depth + 1)
            if found:
                return found
    return ""


def find_student(data: dict) -> tuple[str, str]:
    inner = data.get("data") if isinstance(data.get("data"), dict) else {}
    holders = (
        data,
        inner,
        data.get("siswa"),
        inner.get("siswa"),
        data.get("user"),
        inner.get("user"),
        data.get("student"),
        inner.get("student"),
        data.get("result"),
        data.get("payload"),
    )

    name = ""
    url = ""
    for holder in holders:
        if not isinstance(holder, dict):
            continue
        if not name:
            for k in NAME_KEYS:
                val = holder.get(k)
                if isinstance(val, str) and val.strip():
                    name = val.strip()
                    break
        if not url:
            for k in PICTURE_KEYS:
                val = holder.get(k)
                if isinstance(val, str) and val.startswith(("http://", "https://")):
                    url = val
                    break

    if not name:
        name = _search_name_recursive(data)

    return name, url


def get_initials(name: str) -> str:
    parts = [p for p in name.split() if p]
    if not parts:
        return ""
    if len(parts) == 1:
        return parts[0][:2].upper()
    return (parts[0][0] + parts[-1][0]).upper()


def blend(hex1: str, hex2: str, t: float) -> str:
    t = max(0.0, min(1.0, t))
    r1, g1, b1 = int(hex1[1:3], 16), int(hex1[3:5], 16), int(hex1[5:7], 16)
    r2, g2, b2 = int(hex2[1:3], 16), int(hex2[3:5], 16), int(hex2[5:7], 16)
    return f"#{int(r1 + (r2 - r1) * t):02x}{int(g1 + (g2 - g1) * t):02x}{int(b1 + (b2 - b1) * t):02x}"


def ease_out_back(t: float) -> float:
    t = max(0.0, min(1.0, t))
    c1 = 1.70158
    c3 = c1 + 1.0
    return 1.0 + c3 * ((t - 1.0) ** 3) + c1 * ((t - 1.0) ** 2)


def ease_out_cubic(t: float) -> float:
    t = max(0.0, min(1.0, t))
    return 1.0 - ((1.0 - t) ** 3)


def ease_in_cubic(t: float) -> float:
    t = max(0.0, min(1.0, t))
    return t ** 3


# ---- per-device keyboard input (Windows Raw Input) -----------------------------
#
# HID scanners type like keyboards. With several scanners, Tk cannot tell which
# keystroke came from which device, so their characters mix into one garbage token.
# Raw Input reports the source device of every keystroke, so each scanner gets its
# own buffer here.

RawKeyboardReader = None

if sys.platform == "win32":
    import ctypes
    from ctypes import wintypes

    _user32 = ctypes.WinDLL("user32", use_last_error=True)
    _kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    _LRESULT = ctypes.c_ssize_t
    _WNDPROC = ctypes.WINFUNCTYPE(_LRESULT, wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM)

    _WM_INPUT = 0x00FF
    _RID_INPUT = 0x10000003
    _RIDI_DEVICENAME = 0x20000007
    _RIDEV_INPUTSINK = 0x00000100
    _RIM_TYPEKEYBOARD = 1
    _RI_KEY_BREAK = 0x01

    _VK_RETURN = 0x0D
    _VK_SHIFT = 0x10
    _VK_CAPITAL = 0x14
    _VK_LSHIFT = 0xA0
    _VK_RSHIFT = 0xA1

    class _WNDCLASSW(ctypes.Structure):
        _fields_ = [
            ("style", wintypes.UINT),
            ("lpfnWndProc", _WNDPROC),
            ("cbClsExtra", ctypes.c_int),
            ("cbWndExtra", ctypes.c_int),
            ("hInstance", wintypes.HINSTANCE),
            ("hIcon", wintypes.HANDLE),
            ("hCursor", wintypes.HANDLE),
            ("hbrBackground", wintypes.HANDLE),
            ("lpszMenuName", wintypes.LPCWSTR),
            ("lpszClassName", wintypes.LPCWSTR),
        ]

    class _RAWINPUTDEVICE(ctypes.Structure):
        _fields_ = [
            ("usUsagePage", wintypes.USHORT),
            ("usUsage", wintypes.USHORT),
            ("dwFlags", wintypes.DWORD),
            ("hwndTarget", wintypes.HWND),
        ]

    class _RAWINPUTHEADER(ctypes.Structure):
        _fields_ = [
            ("dwType", wintypes.DWORD),
            ("dwSize", wintypes.DWORD),
            ("hDevice", wintypes.HANDLE),
            ("wParam", wintypes.WPARAM),
        ]

    class _RAWKEYBOARD(ctypes.Structure):
        _fields_ = [
            ("MakeCode", wintypes.USHORT),
            ("Flags", wintypes.USHORT),
            ("Reserved", wintypes.USHORT),
            ("VKey", wintypes.USHORT),
            ("Message", wintypes.UINT),
            ("ExtraInformation", wintypes.ULONG),
        ]

    _user32.DefWindowProcW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
    _user32.DefWindowProcW.restype = _LRESULT
    _user32.RegisterClassW.argtypes = [ctypes.POINTER(_WNDCLASSW)]
    _user32.RegisterClassW.restype = wintypes.ATOM
    _user32.CreateWindowExW.argtypes = [
        wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD,
        ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
        wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, wintypes.LPVOID,
    ]
    _user32.CreateWindowExW.restype = wintypes.HWND
    _user32.RegisterRawInputDevices.argtypes = [ctypes.POINTER(_RAWINPUTDEVICE), wintypes.UINT, wintypes.UINT]
    _user32.RegisterRawInputDevices.restype = wintypes.BOOL
    _user32.GetRawInputData.argtypes = [
        wintypes.HANDLE, wintypes.UINT, wintypes.LPVOID, ctypes.POINTER(wintypes.UINT), wintypes.UINT,
    ]
    _user32.GetRawInputData.restype = wintypes.UINT
    _user32.GetRawInputDeviceInfoW.argtypes = [
        wintypes.HANDLE, wintypes.UINT, wintypes.LPVOID, ctypes.POINTER(wintypes.UINT),
    ]
    _user32.GetRawInputDeviceInfoW.restype = wintypes.UINT
    _user32.GetMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT]
    _user32.GetMessageW.restype = ctypes.c_int
    _user32.TranslateMessage.argtypes = [ctypes.POINTER(wintypes.MSG)]
    _user32.DispatchMessageW.argtypes = [ctypes.POINTER(wintypes.MSG)]
    _user32.ToUnicode.argtypes = [
        wintypes.UINT, wintypes.UINT, ctypes.POINTER(ctypes.c_ubyte), wintypes.LPWSTR, ctypes.c_int, wintypes.UINT,
    ]
    _user32.ToUnicode.restype = ctypes.c_int
    _user32.GetKeyState.argtypes = [ctypes.c_int]
    _user32.GetKeyState.restype = ctypes.c_short
    _kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
    _kernel32.GetModuleHandleW.restype = wintypes.HINSTANCE

    class RawKeyboardReader:
        def __init__(self, on_scan, vid_pid=None, gap: float = RAW_KEY_GAP, on_error=None) -> None:
            """
            on_scan : callback(code, device_label), called from the reader thread
            vid_pid : only accept devices whose path contains one of these strings
            gap     : seconds of silence after which a half-typed buffer is dropped
            on_error: callback(message) when the reader cannot start
            """
            self.on_scan = on_scan
            self.on_error = on_error
            self.filters = tuple(v.upper() for v in (vid_pid or []))
            self.gap = gap
            self._devices: dict = {}   # device handle -> (label, path, allowed)
            self._state: dict = {}     # device handle -> {"buf", "last", "shift"}
            self._wndproc = None

        def start(self) -> None:
            threading.Thread(target=self._run, name="rawinput", daemon=True).start()

        def _run(self) -> None:
            try:
                hinst = _kernel32.GetModuleHandleW(None)
                self._wndproc = _WNDPROC(self._wnd_proc)  # keep a reference or it gets garbage collected

                wc = _WNDCLASSW()
                wc.lpfnWndProc = self._wndproc
                wc.hInstance = hinst
                wc.lpszClassName = "RawKbdSink"
                _user32.RegisterClassW(ctypes.byref(wc))

                hwnd = _user32.CreateWindowExW(0, "RawKbdSink", "rawkbd", 0, 0, 0, 0, 0, None, None, hinst, None)
                if not hwnd:
                    raise ctypes.WinError(ctypes.get_last_error())

                rid = _RAWINPUTDEVICE(1, 6, _RIDEV_INPUTSINK, hwnd)  # generic desktop / keyboard
                if not _user32.RegisterRawInputDevices(ctypes.byref(rid), 1, ctypes.sizeof(rid)):
                    raise ctypes.WinError(ctypes.get_last_error())

                log.info("Raw input reader started (filters: %s)", ", ".join(self.filters) or "none")

                msg = wintypes.MSG()
                while _user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                    _user32.TranslateMessage(ctypes.byref(msg))
                    _user32.DispatchMessageW(ctypes.byref(msg))
            except Exception:
                log.exception("Raw input reader crashed")
                if self.on_error:
                    self.on_error("Scanner input gagal dimulai")

        def _wnd_proc(self, hwnd, msg, wparam, lparam):
            if msg == _WM_INPUT:
                try:
                    self._on_input(lparam)
                except Exception:
                    log.exception("Raw input error")
            return _user32.DefWindowProcW(hwnd, msg, wparam, lparam)  # required for WM_INPUT cleanup

        def _device_path(self, handle) -> str:
            size = wintypes.UINT(0)
            _user32.GetRawInputDeviceInfoW(handle, _RIDI_DEVICENAME, None, ctypes.byref(size))
            if not size.value:
                return ""
            buf = ctypes.create_unicode_buffer(size.value)
            _user32.GetRawInputDeviceInfoW(handle, _RIDI_DEVICENAME, buf, ctypes.byref(size))
            return buf.value

        def _device_info(self, handle):
            info = self._devices.get(handle)
            if info:
                return info
            path = self._device_path(handle)
            allowed = not self.filters or any(f in path.upper() for f in self.filters)
            label = f"kbd-{len(self._devices) + 1}"
            info = (label, path, allowed)
            self._devices[handle] = info
            log.info("Raw input device %s: %s%s", label, path, "" if allowed else "  (ignored)")
            return info

        def _on_input(self, lparam) -> None:
            hdr_size = ctypes.sizeof(_RAWINPUTHEADER)
            size = wintypes.UINT(0)
            _user32.GetRawInputData(lparam, _RID_INPUT, None, ctypes.byref(size), hdr_size)
            if not size.value:
                return
            buf = ctypes.create_string_buffer(size.value)
            if _user32.GetRawInputData(lparam, _RID_INPUT, buf, ctypes.byref(size), hdr_size) != size.value:
                return

            header = _RAWINPUTHEADER.from_buffer(buf)
            if header.dwType != _RIM_TYPEKEYBOARD:
                return
            kb = _RAWKEYBOARD.from_buffer(buf, hdr_size)

            handle = header.hDevice
            label, _path, allowed = self._device_info(handle)
            if not allowed:
                return

            st = self._state.setdefault(handle, {"buf": "", "last": 0.0, "shift": False})
            is_up = bool(kb.Flags & _RI_KEY_BREAK)
            vk = kb.VKey

            if vk in (_VK_SHIFT, _VK_LSHIFT, _VK_RSHIFT):
                st["shift"] = not is_up
                return
            if is_up or vk == 0xFF:
                return

            now = time.monotonic()
            if now - st["last"] > self.gap:
                st["buf"] = ""
            st["last"] = now

            if vk == _VK_RETURN:
                code, st["buf"] = st["buf"].strip(), ""
                if code:
                    self.on_scan(code, label)
                return

            ch = self._to_char(vk, kb.MakeCode, st["shift"])
            if ch:
                st["buf"] += ch

        @staticmethod
        def _to_char(vk: int, make_code: int, shift: bool) -> str:
            state = (ctypes.c_ubyte * 256)()
            if shift:
                state[_VK_SHIFT] = 0x80
            if _user32.GetKeyState(_VK_CAPITAL) & 1:
                state[_VK_CAPITAL] = 1
            out = ctypes.create_unicode_buffer(8)
            n = _user32.ToUnicode(vk, make_code, state, out, 8, 4)  # flag 4: do not change keyboard state
            if n > 0:
                text = out.value[:n]
                if text.isprintable():
                    return text
            return ""


@dataclass
class ScanJob:
    seq: int          # running number, shown in the log as #12
    code: str         # the scanned token
    source: str       # "kbd-N" (raw input), "keyboard" or a serial port name
    queued_at: float  # time.monotonic() when it entered the queue


class ImageCache:
    """Photo cache shared by all worker threads."""

    def __init__(self, max_items: int = IMAGE_CACHE_MAX) -> None:
        self._items: dict = {}
        self._lock = threading.Lock()
        self._max = max_items

    def get(self, key):
        with self._lock:
            return self._items.get(key)

    def put(self, key, value) -> None:
        with self._lock:
            if len(self._items) >= self._max:
                self._items.pop(next(iter(self._items)))
            self._items[key] = value


class ScanApp:
    def __init__(self, root: tk.Tk, ports: list[str] | None = None, use_raw: bool = False) -> None:
        self.root = root

        # Pipeline: input -> enqueue() -> jobs -> worker threads -> events -> poll() -> display_queue -> screen
        self.jobs: queue.Queue = queue.Queue()       # scans waiting to be sent, shared by all workers
        self.events: queue.Queue = queue.Queue()     # messages for the UI thread
        self.display_queue: deque = deque()          # finished results waiting to be shown
        self.cache = ImageCache()
        self.seq = itertools.count(1)

        self.inflight: set[str] = set()              # codes that are queued or being sent right now
        self.recent: dict[str, float] = {}           # code -> time of last scan/finish (cooldown)
        self.outstanding = 0                         # scans accepted whose result has not been shown yet

        self.buffer = ""
        self.last_key = 0.0
        self.reset_job = None
        self.display_ms = RESET_MS

        self.scan_count = 0
        self.streak = 0

        self.state = "idle"
        self.state_time = time.monotonic()
        self.title_text = "Scan QR"
        self.sub_text = "Arahkan QR ke scanner"
        self.student_name = ""
        self.photo_frames: list[tuple[float, ImageTk.PhotoImage]] = []

        root.title("Absen Scanner")
        root.attributes("-fullscreen", True)
        root.bind("<Escape>", lambda e: root.destroy())
        if not use_raw:
            # Shared buffer: only safe with a single keyboard-mode scanner.
            root.bind("<Key>", self.on_key)

        self.width = root.winfo_screenwidth()
        self.height = root.winfo_screenheight()
        self.photo_side = int(min(self.height * 0.31, self.width * 0.40))

        self.canvas = tk.Canvas(root, width=self.width, height=self.height, highlightthickness=0, bd=0)
        self.canvas.pack(fill="both", expand=True)

        self.idle()
        root.focus_force()
        root.after(50, self.poll)
        root.after(FPS_MS, self.animate)

        for n in range(1, WORKERS + 1):
            threading.Thread(target=self.worker, name=f"worker-{n}", daemon=True).start()

        for port in ports or []:
            threading.Thread(target=self.serial_loop, args=(port,), name=f"serial-{port}", daemon=True).start()

        self.raw = None
        if use_raw and RawKeyboardReader is not None:
            self.raw = RawKeyboardReader(
                lambda code, dev: self.events.put(("scan", code, dev)),
                vid_pid=RAW_VID_PID,
                on_error=lambda msg: self.events.put(("notice", msg)),
            )
            self.raw.start()

    # ---- state -------------------------------------------------------------

    def show(
        self,
        state: str,
        text: str,
        subtext: str = "",
        name: str = "",
        photo_frames: list[tuple[float, ImageTk.PhotoImage]] | None = None,
    ) -> None:
        self.state = state
        self.state_time = time.monotonic()
        self.title_text = text
        self.sub_text = subtext
        self.student_name = name
        self.photo_frames = photo_frames or []
        self.canvas.configure(bg=COLORS[state][0])

    def idle(self) -> None:
        self.reset_job = None
        self.show("idle", "Scan QR", "Arahkan QR ke scanner")

    def _cancel_reset(self) -> None:
        if self.reset_job:
            self.root.after_cancel(self.reset_job)
            self.reset_job = None

    # ---- input -------------------------------------------------------------

    def on_key(self, event: tk.Event) -> None:
        now = time.time()
        if now - self.last_key > KEY_GAP:
            self.buffer = ""
        self.last_key = now

        if event.keysym in ("Return", "KP_Enter"):
            code, self.buffer = self.buffer.strip(), ""
            if code:
                self.enqueue(code, "keyboard")
        elif event.char and event.char.isprintable():
            self.buffer += event.char

    def serial_loop(self, port: str) -> None:
        try:
            import serial

            with serial.Serial(port, 9600, timeout=1) as ser:
                while True:
                    code = ser.readline().decode(errors="ignore").strip()
                    if code:
                        self.events.put(("scan", code, port))
        except Exception as e:
            log.exception("Serial error on %s", port)
            self.events.put(("notice", f"Serial error: {e}"))

    # ---- queueing (UI thread) ----------------------------------------------

    def enqueue(self, code: str, source: str) -> None:
        """Every scan goes into the queue, unless it looks corrupted, the same account is
        already being handled, or it was scanned less than DUPLICATE_COOLDOWN seconds ago."""
        now = time.monotonic()

        if not (MIN_LEN <= len(code) <= MAX_LEN):
            log.warning("Dropped malformed scan from %s (len=%d) token=%s", source, len(code), mask(code))
            self.outstanding += 1
            self.push_display(False, "Kode tidak lengkap, scan ulang", "", None)
            return

        if code in self.inflight:
            return
        last = self.recent.get(code)
        if last is not None and now - last < DUPLICATE_COOLDOWN:
            return

        if len(self.recent) > 200:
            self.recent = {c: t for c, t in self.recent.items() if now - t < 60}

        job = ScanJob(next(self.seq), code, source, now)
        self.inflight.add(code)
        self.recent[code] = now
        self.outstanding += 1
        self.jobs.put(job)
        log.info("#%d queued from %s (waiting in queue: %d) token=%s", job.seq, source, self.jobs.qsize(), mask(code))

        if self.state == "idle":
            self.show("wait", "Wait")

    def handle_result(self, job: ScanJob, ok: bool, msg: str, name: str, image) -> None:
        self.inflight.discard(job.code)
        self.recent[job.code] = time.monotonic()  # cooldown restarts when the request finishes
        self.push_display(ok, msg, name, image)

    def push_display(self, ok: bool, msg: str, name: str, image) -> None:
        self.display_queue.append((ok, msg, name, image))
        if self.state in ("idle", "wait"):
            self.show_next()

    def show_next(self) -> None:
        """Shows the next finished result. Called when a result arrives on a free screen,
        and again when the current result has been on screen long enough."""
        self._cancel_reset()

        if not self.display_queue:
            if self.outstanding > 0:
                self.show("wait", "Wait")
            else:
                self.idle()
            return

        ok, msg, name, image = self.display_queue.popleft()
        self.outstanding = max(0, self.outstanding - 1)
        self.display_ms = FAST_RESET_MS if self.outstanding > 0 else RESET_MS

        if ok:
            self.scan_count += 1
            self.streak += 1
            frames = self.build_photo_frames(image)

            stat = f"Hadir ke-{self.scan_count}"
            if self.streak >= 3:
                stat += f"  |  Streak {self.streak}x"
            sub = f"{msg}  |  {stat}" if msg else stat

            self.show("success", "Success", sub, name=name, photo_frames=frames)
        else:
            self.streak = 0
            self.show("error", "Try Again", msg)

        self.reset_job = self.root.after(self.display_ms, self.show_next)

    def waiting_count(self) -> int:
        """Scans that are not on screen yet (shown as the queue badge)."""
        if self.state == "wait":
            return max(0, self.outstanding - 1)
        if self.state in ("success", "error"):
            return self.outstanding
        return 0

    # ---- workers (background threads, never touch Tk) ------------------------

    def worker(self) -> None:
        while True:
            job = self.jobs.get()
            if job is None:
                return
            ok, msg, name, image = self.send(job)
            self.events.put(("result", job, ok, msg, name, image))

    def send(self, job: ScanJob) -> tuple[bool, str, str, object]:
        tag = f"#{job.seq}"
        code = job.code
        image = None
        name = ""
        ok = False
        msg = ""
        started = time.monotonic()
        queued_ms = (started - job.queued_at) * 1000

        try:
            r = requests.post(API_URL, json={FIELD: code}, timeout=TIMEOUT)
            ms = (time.monotonic() - started) * 1000

            try:
                data = r.json()
            except ValueError:
                data = {}
            if not isinstance(data, dict):
                data = {}

            ok = r.ok and bool(data.get("success"))
            msg = str(data.get("message") or "")

            if r.status_code >= 500:
                log.error(
                    "%s POST %s -> HTTP %s in %.0f ms (queued %.0f ms)\n  token: %s\n  content-type: %s\n  body: %s",
                    tag, API_URL, r.status_code, ms, queued_ms, mask(code),
                    r.headers.get("Content-Type", "-"), short(r.text),
                )
                msg = f"{msg or 'Server error'} (HTTP {r.status_code})"
            elif not ok:
                log.warning(
                    "%s Scan rejected: HTTP %s from %s token=%s body=%s",
                    tag, r.status_code, job.source, mask(code), short(r.text),
                )
            else:
                log.info("%s Scan ok: HTTP %s in %.0f ms (queued %.0f ms)", tag, r.status_code, ms, queued_ms)

            name, url = find_student(data)
            if ok and url:
                image = self.load_picture(url)

        except requests.Timeout:
            ok, msg = False, "Server terlalu lama merespons"
            log.error("%s Timeout after %ss: POST %s token=%s", tag, TIMEOUT, API_URL, mask(code))
        except requests.ConnectionError as e:
            ok, msg = False, "Tidak bisa terhubung ke server"
            log.error("%s Connection error: %s", tag, e)
        except Exception:
            ok, msg = False, "Terjadi kesalahan pada scanner"
            log.exception("%s Unexpected error while handling scan token=%s", tag, mask(code))

        return ok, msg, name, image

    def load_picture(self, url: str):
        if Image is None:
            return None

        side = self.photo_side
        key = (url, side)
        cached = self.cache.get(key)
        if cached is not None:
            return cached

        try:
            r = requests.get(url, timeout=IMAGE_TIMEOUT)
            r.raise_for_status()

            img = ImageOps.exif_transpose(Image.open(io.BytesIO(r.content))).convert("RGBA")
            img = ImageOps.fit(img, (side, side), method=Image.Resampling.LANCZOS)

            mask_img = Image.new("L", (side * 4, side * 4), 0)
            ImageDraw.Draw(mask_img).ellipse((0, 0, side * 4 - 1, side * 4 - 1), fill=255)
            img.putalpha(mask_img.resize((side, side), Image.Resampling.LANCZOS))
        except Exception as e:
            log.warning("Failed to load photo %s: %s", url, e)
            return None

        self.cache.put(key, img)
        return img

    # ---- UI thread loops -----------------------------------------------------

    def build_photo_frames(self, img) -> list[tuple[float, ImageTk.PhotoImage]]:
        if img is None or Image is None:
            return []
        frames = []
        base = self.photo_side
        for s in PHOTO_SCALES:
            px = max(8, int(base * s))
            resized = img.resize((px, px), Image.Resampling.BILINEAR)
            frames.append((s, ImageTk.PhotoImage(resized)))
        return frames

    def get_photo_for_scale(self, scale: float):
        if not self.photo_frames:
            return None
        return min(self.photo_frames, key=lambda item: abs(item[0] - scale))[1]

    def poll(self) -> None:
        while True:
            try:
                event = self.events.get_nowait()
            except queue.Empty:
                break
            try:
                kind = event[0]
                if kind == "scan":
                    self.enqueue(event[1], event[2])
                elif kind == "result":
                    self.handle_result(*event[1:])
                elif kind == "notice":
                    self.outstanding += 1
                    self.push_display(False, event[1], "", None)
            except Exception:
                log.exception("Error handling %s event", event[0])
        self.root.after(50, self.poll)

    def _compute_pop_scale(self, elapsed: float, has_exit: bool) -> float:
        in_dur = 0.34
        out_dur = 0.24
        total_dur = self.display_ms / 1000.0

        if elapsed < in_dur:
            return ease_out_back(elapsed / in_dur)
        if has_exit and elapsed > (total_dur - out_dur):
            u = (elapsed - (total_dur - out_dur)) / out_dur
            return max(0.0, 1.0 - ease_in_cubic(u))
        return 1.0

    def animate(self) -> None:
        w = self.canvas.winfo_width() or self.width
        h = self.canvas.winfo_height() or self.height
        now = time.monotonic()
        elapsed = now - self.state_time
        bg, fg, muted, accent = COLORS[self.state]

        self.canvas.delete("all")

        if self.state == "idle":
            self._draw_idle(w, h, now, elapsed, bg, fg, muted, accent)
        elif self.state == "wait":
            self._draw_wait(w, h, elapsed, bg, fg)
        elif self.state == "success":
            self._draw_success(w, h, elapsed, bg, fg, muted, accent)
        elif self.state == "error":
            self._draw_error(w, h, elapsed, bg, fg, muted)

        self._draw_queue_badge(w, h, muted)

        self.root.after(FPS_MS, self.animate)

    def _draw_queue_badge(self, w: int, h: int, muted: str) -> None:
        waiting = self.waiting_count()
        if waiting <= 0:
            return
        size = max(16, int(h * 0.03))
        self.canvas.create_text(
            w - 18, 14, text=f"Antrian: {waiting}", anchor="ne", fill=muted,
            font=("Helvetica", -size, "bold"),
        )

    def _draw_idle(self, w: int, h: int, now: float, elapsed: float, bg: str, fg: str, muted: str, accent: str) -> None:
        scale = ease_out_cubic(min(1.0, elapsed / 0.28))
        if scale <= 0.05:
            return

        cx = w * 0.5
        cy = h * 0.36
        pulse = math.sin(now * 2.6) * 5
        half = (min(w, h) * 0.095 + pulse) * scale
        corner = half * 0.45
        stroke = max(3, int(5 * scale))

        # for sx, sy in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
        #     x0, y0 = cx + sx * half, cy + sy * half
        #     self.canvas.create_line(x0, y0, x0 - sx * corner, y0, fill=accent, width=stroke, capstyle="round")
        #     self.canvas.create_line(x0, y0, x0, y0 - sy * corner, fill=accent, width=stroke, capstyle="round")

        # inner = half * 0.38
        # self.canvas.create_rectangle(
        #     cx - inner, cy - inner, cx + inner, cy + inner,
        #     outline=blend(bg, accent, 0.55), width=max(2, int(3 * scale)),
        # )

        title_size = int(min(w // 8, h // 5) * scale)
        sub_size = int(max(min(w // 8, h // 5) // 6, 20) * scale)
        if title_size >= 8:
            self.canvas.create_text(cx, h * 0.58, text=self.title_text, fill=fg, font=("Helvetica", -title_size, "bold"))
        if sub_size >= 8:
            self.canvas.create_text(cx, h * 0.72, text=self.sub_text, fill=muted, font=("Helvetica", -sub_size))

    def _draw_wait(self, w: int, h: int, elapsed: float, bg: str, fg: str) -> None:
        scale = ease_out_back(min(1.0, elapsed / 0.26))
        if scale <= 0.05:
            return

        cx = w * 0.5
        cy = h * 0.38
        r = min(w, h) * 0.085 * scale
        stroke = max(4, int(8 * scale))

        self.canvas.create_oval(cx - r, cy - r, cx + r, cy + r, outline=blend(bg, fg, 0.2), width=stroke)
        self.canvas.create_arc(
            cx - r, cy - r, cx + r, cy + r,
            start=-(elapsed * 340) % 360, extent=115, style="arc", outline=fg, width=stroke,
        )

        title_size = int(min(w // 8, h // 5) * scale)
        if title_size >= 8:
            self.canvas.create_text(cx, h * 0.60, text=self.title_text, fill=fg, font=("Helvetica", -title_size, "bold"))

    def _draw_success(self, w: int, h: int, elapsed: float, bg: str, fg: str, muted: str, accent: str) -> None:
        scale = self._compute_pop_scale(elapsed, has_exit=True)
        cx = w * 0.5
        cy = h * 0.28
        is_milestone = self.scan_count % 10 == 0
        ring_color = accent if is_milestone else fg

        if elapsed < 0.75:
            t = ease_out_cubic(elapsed / 0.75)
            pr = (self.photo_side * 0.5) + t * (min(w, h) * 0.16)
            self.canvas.create_oval(
                cx - pr, cy - pr, cx + pr, cy + pr,
                outline=blend(ring_color, bg, elapsed / 0.75), width=4,
            )

        if scale > 0.04:
            photo = self.get_photo_for_scale(scale)
            avatar_r = (self.photo_side * 0.5) * scale

            if photo is not None:
                ring_r = avatar_r + 5 * scale
                self.canvas.create_oval(
                    cx - ring_r, cy - ring_r, cx + ring_r, cy + ring_r,
                    outline=ring_color, width=max(2, int(5 * scale)),
                )
                self.canvas.create_image(cx, cy, image=photo, anchor="center")
            else:
                avatar_r = (self.photo_side * 0.44) * scale
                self.canvas.create_oval(
                    cx - avatar_r, cy - avatar_r, cx + avatar_r, cy + avatar_r,
                    fill=blend(bg, fg, 0.18), outline=ring_color, width=max(2, int(5 * scale)),
                )
                initials = get_initials(self.student_name)
                if initials:
                    init_size = int(avatar_r * 0.68)
                    if init_size >= 8:
                        self.canvas.create_text(
                            cx, cy, text=initials, fill=fg, font=("Helvetica", -init_size, "bold")
                        )
                else:
                    self._draw_vector_person(cx, cy, avatar_r * 0.55, fg)

            badge_r = max(16.0, self.photo_side * 0.12) * scale
            bx = cx + avatar_r * 0.72
            by = cy + avatar_r * 0.72
            self.canvas.create_oval(
                bx - badge_r, by - badge_r, bx + badge_r, by + badge_r,
                fill=fg, outline=bg, width=max(2, int(4 * scale)),
            )
            check_progress = ease_out_cubic(min(1.0, max(0.0, (elapsed - 0.12) / 0.22)))
            self._draw_vector_check(bx, by, badge_r * 0.52, bg, check_progress, max(2, int(4 * scale)))

            if self.student_name:
                base_name = max(38, min(w // 13, h // 10))
                if len(self.student_name) > 22:
                    base_name = int(base_name * (22 / len(self.student_name)) ** 0.6)
                name_size = int(base_name * scale)
                status_size = int(max(24, min(w // 22, h // 18)) * scale)
                sub_size = int(max(18, int(h * 0.028)) * scale)

                if name_size >= 8:
                    self.canvas.create_text(
                        cx, h * 0.55, text=self.student_name, fill=fg,
                        font=("Helvetica", -name_size, "bold"), width=int(w * 0.88), justify="center",
                    )
                if status_size >= 8:
                    self.canvas.create_text(
                        cx, h * 0.68, text=self.title_text, fill=accent,
                        font=("Helvetica", -status_size, "bold"),
                    )
                if sub_size >= 8:
                    self.canvas.create_text(
                        cx, h * 0.78, text=self.sub_text, fill=muted,
                        font=("Helvetica", -sub_size, "bold"), width=int(w * 0.92), justify="center",
                    )
            else:
                title_size = int(max(42, min(w // 11, h // 7)) * scale)
                sub_size = int(max(20, int(h * 0.032)) * scale)
                if title_size >= 8:
                    self.canvas.create_text(
                        cx, h * 0.58, text=self.title_text, fill=fg,
                        font=("Helvetica", -title_size, "bold"),
                    )
                if sub_size >= 8:
                    self.canvas.create_text(
                        cx, h * 0.72, text=self.sub_text, fill=muted,
                        font=("Helvetica", -sub_size, "bold"), width=int(w * 0.92), justify="center",
                    )

        self._draw_timer_bar(w, h, elapsed, bg, fg)

    def _draw_error(self, w: int, h: int, elapsed: float, bg: str, fg: str, muted: str) -> None:
        scale = self._compute_pop_scale(elapsed, has_exit=True)
        if scale <= 0.04:
            self._draw_timer_bar(w, h, elapsed, bg, fg)
            return

        shake = math.sin(elapsed * 45) * 14 * (1 - elapsed / 0.4) if elapsed < 0.4 else 0
        cx = w * 0.5 + shake
        cy = h * 0.36
        r = min(w, h) * 0.085 * scale
        stroke = max(2, int(5 * scale))

        self.canvas.create_oval(cx - r, cy - r, cx + r, cy + r, outline=fg, width=stroke)

        cross_progress = ease_out_cubic(min(1.0, max(0.0, (elapsed - 0.1) / 0.2)))
        self._draw_vector_cross(cx, cy, r * 0.42, fg, cross_progress, stroke)

        title_size = int(min(w // 9, h // 6) * scale)
        sub_size = int(max(20, int(h * 0.032)) * scale)
        if title_size >= 8:
            self.canvas.create_text(cx, h * 0.56, text=self.title_text, fill=fg, font=("Helvetica", -title_size, "bold"))
        if sub_size >= 8:
            self.canvas.create_text(
                w * 0.5, h * 0.71, text=self.sub_text, fill=muted,
                font=("Helvetica", -sub_size), width=int(w * 0.85), justify="center",
            )

        self._draw_timer_bar(w, h, elapsed, bg, fg)

    def _draw_vector_check(self, cx: float, cy: float, r: float, color: str, progress: float, width: int) -> None:
        if progress <= 0.0:
            return
        p1 = (cx - r * 0.85, cy + r * 0.05)
        p2 = (cx - r * 0.2, cy + r * 0.72)
        p3 = (cx + r * 0.9, cy - r * 0.65)

        if progress < 0.45:
            t = progress / 0.45
            mx = p1[0] + (p2[0] - p1[0]) * t
            my = p1[1] + (p2[1] - p1[1]) * t
            self.canvas.create_line(p1[0], p1[1], mx, my, fill=color, width=width, capstyle="round")
        else:
            t = (progress - 0.45) / 0.55
            mx = p2[0] + (p3[0] - p2[0]) * t
            my = p2[1] + (p3[1] - p2[1]) * t
            self.canvas.create_line(
                p1[0], p1[1], p2[0], p2[1], mx, my,
                fill=color, width=width, capstyle="round", joinstyle="round",
            )

    def _draw_vector_cross(self, cx: float, cy: float, r: float, color: str, progress: float, width: int) -> None:
        if progress <= 0.0:
            return
        t1 = min(1.0, progress / 0.5)
        self.canvas.create_line(
            cx - r, cy - r,
            cx - r + (2 * r * t1), cy - r + (2 * r * t1),
            fill=color, width=width, capstyle="round",
        )
        if progress > 0.5:
            t2 = (progress - 0.5) / 0.5
            self.canvas.create_line(
                cx + r, cy - r,
                cx + r - (2 * r * t2), cy - r + (2 * r * t2),
                fill=color, width=width, capstyle="round",
            )

    def _draw_vector_person(self, cx: float, cy: float, r: float, color: str) -> None:
        head_r = r * 0.42
        self.canvas.create_oval(
            cx - head_r, cy - r * 0.75, cx + head_r, cy - r * 0.75 + head_r * 2,
            fill=color, outline="",
        )
        self.canvas.create_arc(
            cx - r * 0.85, cy + r * 0.05, cx + r * 0.85, cy + r * 1.45,
            start=0, extent=180, fill=color, outline="",
        )

    def _draw_timer_bar(self, w: int, h: int, elapsed: float, bg: str, fg: str) -> None:
        rem = max(0.0, 1.0 - (elapsed * 1000.0) / self.display_ms)
        bar_h = 8
        self.canvas.create_rectangle(0, h - bar_h, w, h, fill=blend(bg, fg, 0.2), outline="")
        self.canvas.create_rectangle(0, h - bar_h, w * rem, h, fill=fg, outline="")


if __name__ == "__main__":
    # Usage:
    #   python scanner.py                 -> Windows Raw Input (one buffer per scanner)
    #   python scanner.py COM3 COM4       -> also read serial scanners
    #   python scanner.py --no-raw        -> old behaviour, one shared keyboard buffer
    ports = [a for a in sys.argv[1:] if not a.startswith("--")]
    use_raw = RawKeyboardReader is not None and "--no-raw" not in sys.argv

    root = tk.Tk()
    root.report_callback_exception = lambda exc, val, tb: log.error(
        "Tkinter callback error", exc_info=(exc, val, tb)
    )
    log.info("Scanner started, API=%s, workers=%d, raw_input=%s", API_URL, WORKERS, use_raw)
    ScanApp(root, ports, use_raw=use_raw)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        pass