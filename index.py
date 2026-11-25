import io
import math
import queue
import sys
import threading
import time
import tkinter as tk

import requests

try:
    from PIL import Image, ImageDraw, ImageOps, ImageTk
except ImportError:
    Image = None

API_URL = "http://localhost:5000/api/absen/scan"
FIELD = "token"
TIMEOUT = 5
IMAGE_TIMEOUT = 4
IMAGE_CACHE_MAX = 50
RESET_MS = 2600
KEY_GAP = 0.3
DUPLICATE_COOLDOWN = 2.0
FPS_MS = 16

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


class ScanApp:
    def __init__(self, root: tk.Tk, port: str | None = None) -> None:
        self.root = root
        self.busy = False
        self.buffer = ""
        self.last_key = 0.0
        self.last_code = ""
        self.last_scan_time = 0.0
        self.reset_job = None

        self.scan_count = 0
        self.streak = 0

        self.state = "idle"
        self.state_time = time.monotonic()
        self.title_text = "Scan QR"
        self.sub_text = "Arahkan QR ke scanner"
        self.student_name = ""
        self.photo_frames: list[tuple[float, ImageTk.PhotoImage]] = []

        self.cache: dict = {}
        self.events: queue.Queue = queue.Queue()

        root.title("Absen Scanner")
        root.attributes("-fullscreen", True)
        root.bind("<Escape>", lambda e: root.destroy())
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

        if port:
            threading.Thread(target=self.serial_loop, args=(port,), daemon=True).start()

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

    def on_key(self, event: tk.Event) -> None:
        now = time.time()
        if now - self.last_key > KEY_GAP:
            self.buffer = ""
        self.last_key = now

        if event.keysym in ("Return", "KP_Enter"):
            code, self.buffer = self.buffer.strip(), ""
            if code:
                self.submit(code)
        elif event.char and event.char.isprintable():
            self.buffer += event.char

    def serial_loop(self, port: str) -> None:
        import serial

        try:
            with serial.Serial(port, 9600, timeout=1) as ser:
                while True:
                    code = ser.readline().decode(errors="ignore").strip()
                    if code:
                        self.events.put(("scan", code))
        except Exception as e:
            self.events.put(("result", False, f"Serial error: {e}", "", None))

    def submit(self, code: str) -> None:
        if self.busy:
            return
        now = time.time()
        if code == self.last_code and (now - self.last_scan_time) < DUPLICATE_COOLDOWN:
            return

        self.busy = True
        self.last_code = code
        self.last_scan_time = now

        if self.reset_job:
            self.root.after_cancel(self.reset_job)
            self.reset_job = None

        self.show("wait", "Wait")
        threading.Thread(target=self.send, args=(code,), daemon=True).start()

    def send(self, code: str) -> None:
        image = None
        name = ""
        try:
            r = requests.post(API_URL, json={FIELD: code}, timeout=TIMEOUT)
            try:
                data = r.json()
            except ValueError:
                data = {}
            if not isinstance(data, dict):
                data = {}

            ok = r.ok and bool(data.get("success"))
            msg = str(data.get("message") or "")
            name, url = find_student(data)

            if ok and url:
                image = self.load_picture(url)
        except requests.RequestException:
            ok, msg = False, "Tidak bisa terhubung ke server"

        self.events.put(("result", ok, msg, name, image))

    def load_picture(self, url: str):
        if Image is None:
            return None

        cached = self.cache.get(url)
        if cached is not None:
            return cached

        side = self.photo_side
        try:
            r = requests.get(url, timeout=IMAGE_TIMEOUT)
            r.raise_for_status()

            img = ImageOps.exif_transpose(Image.open(io.BytesIO(r.content))).convert("RGBA")
            img = ImageOps.fit(img, (side, side), method=Image.Resampling.LANCZOS)

            mask = Image.new("L", (side * 4, side * 4), 0)
            ImageDraw.Draw(mask).ellipse((0, 0, side * 4 - 1, side * 4 - 1), fill=255)
            img.putalpha(mask.resize((side, side), Image.Resampling.LANCZOS))
        except Exception:
            return None

        if len(self.cache) >= IMAGE_CACHE_MAX:
            self.cache.pop(next(iter(self.cache)))
        self.cache[url] = img
        return img

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
        try:
            while True:
                event = self.events.get_nowait()
                if event[0] == "scan":
                    self.submit(event[1])
                else:
                    _, ok, msg, name, image = event
                    self.busy = False
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
                    self.reset_job = self.root.after(RESET_MS, self.idle)
        except queue.Empty:
            pass
        self.root.after(50, self.poll)

    def _compute_pop_scale(self, elapsed: float, has_exit: bool) -> float:
        in_dur = 0.34
        out_dur = 0.24
        total_dur = RESET_MS / 1000.0

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

        self.root.after(FPS_MS, self.animate)

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
                        font=("Helvetica", -sub_size, "bold"),
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
                        font=("Helvetica", -sub_size, "bold"),
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
        rem = max(0.0, 1.0 - (elapsed * 1000.0) / RESET_MS)
        bar_h = 8
        self.canvas.create_rectangle(0, h - bar_h, w, h, fill=blend(bg, fg, 0.2), outline="")
        self.canvas.create_rectangle(0, h - bar_h, w * rem, h, fill=fg, outline="")


if __name__ == "__main__":
    port = sys.argv[1] if len(sys.argv) > 1 else None
    root = tk.Tk()
    ScanApp(root, port)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        pass