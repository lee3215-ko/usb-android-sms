import base64
import ctypes
import io
import json
import mimetypes
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import urllib.request
import re
import winsound
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk

from PIL import Image, ImageGrab, ImageTk


APP_TITLE = "USB 안드로이드 문자 관리"
CHAT_BG = "#E7EEF6"
BUBBLE_IN = "#FFFFFF"
BUBBLE_OUT = "#0B57D0"
BUBBLE_FAIL = "#C5221F"
TEXT_IN = "#1A1A1A"
TEXT_OUT = "#FFFFFF"
META_IN = "#3E4C59"
META_OUT = "#0B57D0"
BRIDGE_PACKAGE = "com.codex.usbsmsbridge"
BRIDGE_ACTIVITY = f"{BRIDGE_PACKAGE}/.MainActivity"
BRIDGE_PERMISSIONS = (
    "android.permission.READ_SMS",
    "android.permission.SEND_SMS",
    "android.permission.READ_PHONE_STATE",
)


def app_dir():
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


CONFIG_PATH = app_dir() / "settings.json"


def find_adb():
    base = app_dir()
    candidates = [
        base / "adb" / "adb.exe",
        base / "platform-tools" / "adb.exe",
        shutil.which("adb"),
        r"C:\platform-tools\adb.exe",
    ]
    return next((str(Path(p)) for p in candidates if p and Path(p).exists()), None)


def normalize_phone(address):
    digits = re.sub(r"[^0-9]", "", str(address or ""))
    if digits.startswith("82") and len(digits) >= 10:
        digits = "0" + digits[2:]
    return digits or str(address or "")


def same_phone(left, right):
    return normalize_phone(left) == normalize_phone(right)


class SmsManagerApp:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("1320x800")
        self.root.minsize(1050, 650)
        self.adb = find_adb()
        self.config = self.load_config()
        self.devices, self.device_rows, self.messages = {}, {}, {}
        self.active_serial = self.active_address = None
        self.attachment = None
        self.attachment_preview = None
        self.image_refs = []
        self.sent_notices = []
        self.media_cache = {}
        self.media_loading = set()
        self.status_hold_until = 0
        self.message_sync_running = False
        self.fast_sync_running = False
        self.message_lock = threading.Lock()
        self.alert_ready = set()
        self.alert_known = {}
        self.fresh_marks = set()
        self._arrival_popup = None
        self._arrival_popup_after = None
        self.polling = False
        self.suppress_selection = False
        self._suppress_token = 0
        self._render_queued = False
        self._render_dirty = False
        self.chat_limit = {}
        self.chat_pages = {}
        self.message_index = {}
        self._index_size = {}
        self._prefix_max = {}
        self._session_baselined = set()
        self._unread_total = {}
        self._unread_by_address = {}
        self._full_sync_at = time.time() + 45
        self._paint_token = 0
        self._visible_chat_page = None
        self._save_after = None
        self.status = tk.StringVar(value="휴대폰을 검색하는 중...")
        self.chat_title = tk.StringVar(value="대화를 선택하세요")
        self.attachment_text = tk.StringVar(value="첨부 이미지 없음")
        self.auto_send_image = tk.BooleanVar(value=True)
        self.thread_search = tk.StringVar()
        self._build()
        self.refresh_devices()
        self.root.after(2000, self.poll_messages)
        self.root.after(5000, self.poll)
        self.update_check_running = False
        self.root.after(1500, lambda: self.check_updates(manual=False))

    def _configure_tree_style(self, style_name):
        style = ttk.Style(self.root)
        style.configure(style_name, font=("맑은 고딕", 10), rowheight=32)
        style.configure(f"{style_name}.Heading", font=("맑은 고딕", 9, "bold"))

    def _build(self):
        outer = ttk.Frame(self.root, padding=10)
        outer.pack(fill="both", expand=True)
        top = ttk.Frame(outer)
        top.pack(fill="x", pady=(0, 8))
        ttk.Label(top, text=APP_TITLE, font=("맑은 고딕", 17, "bold")).pack(side="left")
        ttk.Button(top, text="업데이트 확인", command=lambda: self.check_updates(manual=True)).pack(side="right")
        ttk.Button(top, text="브리지 앱 설치/업데이트", command=self.install_bridge).pack(side="right", padx=(0, 6))
        ttk.Button(top, text="새로고침", command=self.refresh_devices).pack(side="right", padx=6)

        self.notice_bar = tk.Frame(outer, background="#C2410C", cursor="hand2")
        self.notice_label = tk.Label(
            self.notice_bar, text="", background="#C2410C", foreground="#FFFFFF",
            font=("맑은 고딕", 13, "bold"), anchor="w", cursor="hand2", padx=14, pady=9,
        )
        self.notice_label.pack(fill="x")
        self.notice_bar.bind("<Button-1>", lambda _event: self._open_newest_unread())
        self.notice_label.bind("<Button-1>", lambda _event: self._open_newest_unread())
        self.panes = ttk.Panedwindow(outer, orient="horizontal")
        self.panes.pack(fill="both", expand=True)
        panes = self.panes
        device_box = ttk.LabelFrame(panes, text="연결된 스마트폰", padding=6)
        thread_box = ttk.LabelFrame(panes, text="대화 목록", padding=6)
        chat_box = ttk.Frame(panes)
        panes.add(device_box, weight=1)
        panes.add(thread_box, weight=2)
        panes.add(chat_box, weight=5)

        device_list = ttk.Frame(device_box)
        device_list.pack(fill="both", expand=True)
        self._configure_tree_style("Devices.Treeview")
        self.device_tree = ttk.Treeview(
            device_list, columns=("state",), show="tree", selectmode="browse", style="Devices.Treeview")
        self.device_tree.tag_configure("unread", background="#FF9F1C", foreground="#1A1206", font=("맑은 고딕", 10, "bold"))
        self.device_tree.tag_configure("read", background="#FFFFFF", foreground="#1A1A1A", font=("맑은 고딕", 10))
        device_scroll = ttk.Scrollbar(device_list, orient="vertical", command=self.device_tree.yview)
        self.device_tree.configure(yscrollcommand=device_scroll.set)
        self.device_tree.pack(side="left", fill="both", expand=True)
        device_scroll.pack(side="right", fill="y")
        self.device_tree.bind("<<TreeviewSelect>>", self.on_device_select)
        ttk.Button(device_box, text="선택한 스마트폰 이름 변경", command=self.rename_device).pack(fill="x", pady=(6, 0))

        search_row = ttk.Frame(thread_box)
        search_row.pack(fill="x", pady=(0, 6))
        ttk.Label(search_row, text="검색").pack(side="left", padx=(0, 5))
        ttk.Entry(search_row, textvariable=self.thread_search).pack(side="left", fill="x", expand=True)
        ttk.Button(search_row, text="지우기", command=lambda: self.thread_search.set("")).pack(side="left", padx=(5, 0))
        self.thread_search.trace_add("write", lambda *_: self.render_threads())
        ttk.Button(thread_box, text="+ 신규 번호로 메시지", command=self.new_conversation).pack(fill="x", pady=(0, 6))
        thread_list = ttk.Frame(thread_box)
        thread_list.pack(fill="both", expand=True)
        self._configure_tree_style("Threads.Treeview")
        self.thread_tree = ttk.Treeview(
            thread_list, columns=("open", "number", "preview"), show="headings", selectmode="browse",
            style="Threads.Treeview")
        self.thread_tree.tag_configure("unread", background="#FF9F1C", foreground="#1A1206", font=("맑은 고딕", 11, "bold"))
        self.thread_tree.tag_configure("read", background="#FFFFFF", foreground="#1A1A1A", font=("맑은 고딕", 10))
        self.thread_tree.heading("open", text="스마트폰")
        self.thread_tree.heading("number", text="번호")
        self.thread_tree.heading("preview", text="최근 내용")
        self.thread_tree.column("open", width=74, anchor="center", stretch=False)
        self.thread_tree.column("number", width=118, anchor="w", stretch=False)
        self.thread_tree.column("preview", width=150, stretch=True)
        thread_scroll = ttk.Scrollbar(thread_list, orient="vertical", command=self.thread_tree.yview)
        self.thread_tree.configure(yscrollcommand=thread_scroll.set)
        self.thread_tree.pack(side="left", fill="both", expand=True)
        thread_scroll.pack(side="right", fill="y")
        self.thread_tree.bind("<<TreeviewSelect>>", self.on_thread_select)
        self.thread_tree.bind("<Button-1>", self.on_thread_shortcut)

        ttk.Label(chat_box, textvariable=self.chat_title, font=("맑은 고딕", 13, "bold")).pack(anchor="w", padx=8)
        chat_area = ttk.Frame(chat_box)
        chat_area.pack(fill="both", expand=True, padx=8, pady=6)
        self.chat_canvas = tk.Canvas(chat_area, background=CHAT_BG, highlightthickness=0, bd=0)
        chat_scroll = ttk.Scrollbar(chat_area, orient="vertical", command=self.chat_canvas.yview)
        self.chat_canvas.configure(yscrollcommand=chat_scroll.set)
        self.chat_canvas.pack(side="left", fill="both", expand=True)
        chat_scroll.pack(side="right", fill="y")
        self.chat_inner = tk.Frame(self.chat_canvas, background=CHAT_BG)
        self.chat_window = self.chat_canvas.create_window((0, 0), window=self.chat_inner, anchor="nw")
        self.chat_inner.bind("<Configure>", self._sync_chat_scroll)
        self.chat_canvas.bind("<Configure>", self._stretch_chat)
        self.root.bind_all("<MouseWheel>", self._chat_wheel, add="+")

        attach = ttk.Frame(chat_box)
        attach.pack(fill="x", padx=8)
        ttk.Button(attach, text="이미지 선택", command=self.choose_image).pack(side="left")
        ttk.Button(attach, text="이미지 바로 보내기", command=self.choose_and_send_image).pack(side="left", padx=(5, 0))
        ttk.Button(attach, text="화면 캡처", command=self.capture_screen).pack(side="left", padx=5)
        ttk.Button(attach, text="캡처 바로 보내기", command=self.capture_and_send_screen).pack(side="left")
        ttk.Button(attach, text="첨부 해제", command=self.clear_attachment).pack(side="left")
        ttk.Label(attach, textvariable=self.attachment_text).pack(side="left", padx=10)
        ttk.Checkbutton(attach, text="이미지 자동 전송", variable=self.auto_send_image).pack(side="right")
        self.attachment_label = ttk.Label(chat_box, text="")
        self.attachment_label.pack(anchor="w", padx=8, pady=(4, 0))

        compose_row = ttk.Frame(chat_box)
        compose_row.pack(fill="x", padx=8, pady=(5, 0))
        self.compose = tk.Text(compose_row, height=5, wrap="word")
        self.compose.pack(side="left", fill="both", expand=True)
        self.compose.bind("<Control-v>", self.paste)
        self.compose.bind("<Control-V>", self.paste)
        self.root.bind_all("<Control-v>", self.paste)
        self.root.bind_all("<Control-V>", self.paste)
        self.compose.bind("<Return>", self.on_compose_enter)
        self.compose.bind("<Shift-Return>", self.on_compose_shift_enter)
        self.compose.bind("<Control-Return>", lambda _e: self.send_message())
        ttk.Button(compose_row, text="전송\nEnter", command=self.send_message).pack(side="right", fill="y", padx=(6, 0))
        ttk.Label(outer, textvariable=self.status).pack(fill="x", pady=(5, 0))

    def load_config(self):
        try:
            data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        except Exception:
            data = {}
        data.setdefault("names", {})
        data.setdefault("seen", {})
        data.setdefault("initialized", [])
        return data

    def save_config(self):
        CONFIG_PATH.write_text(json.dumps(self.config, ensure_ascii=False, indent=2), encoding="utf-8")

    def adb_run(self, serial, *args, timeout=30):
        cmd = [self.adb] + (["-s", serial] if serial else []) + list(args)
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        return subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=timeout, creationflags=flags,
        )

    def api(self, port, path, payload=None, binary=False, quiet=False):
        try:
            data = json.dumps(payload).encode("utf-8") if payload is not None else None
            req = urllib.request.Request(f"http://127.0.0.1:{port}{path}", data=data,
                headers={"Content-Type": "application/json"}, method="POST" if data else "GET")
            with urllib.request.urlopen(req, timeout=15) as res:
                raw = res.read()
                return raw if binary else json.loads(raw.decode("utf-8"))
        except Exception as exc:
            if not quiet:
                self.set_status(f"브리지 통신 오류: {exc}")
            return None

    def refresh_devices(self):
        if not self.adb:
            messagebox.showerror("ADB 없음", "adb.exe를 찾지 못했습니다.")
            return
        threading.Thread(target=self._refresh_worker, daemon=True).start()

    def _refresh_worker(self, reload_messages=True):
        result = self.adb_run(None, "devices", "-l")
        found = []
        for line in result.stdout.splitlines()[1:]:
            p = line.split()
            if len(p) >= 2 and p[1] == "device":
                found.append((p[0], next((x.split(":", 1)[1] for x in p if x.startswith("model:")), p[0])))
        devices = {}
        messages_loaded = False
        for i, (serial, model) in enumerate(found):
            port = 18765 + i
            status = self.ensure_bridge(serial, port)
            devices[serial] = {"model": model, "port": port, "online": bool(status and status.get("ok"))}
            if devices[serial]["online"] and (reload_messages or serial not in self.messages):
                messages_loaded = True
                loaded, complete = self.collect_messages(serial, port)
                self._accept_snapshot(serial, loaded, complete)
                self._full_sync_at = time.time() + 90
        fingerprint = tuple(
            (serial, device["model"], device["port"], device["online"])
            for serial, device in devices.items()
        )
        self.devices = devices
        if messages_loaded or fingerprint != getattr(self, "_device_fingerprint", None):
            self._device_fingerprint = fingerprint
            self.root.after(0, self.render_all)
        self.set_status(f"연결된 스마트폰 {len(devices)}대")

    def collect_messages(self, serial, port, include_archive=True):
        messages = []
        data = self.api(port, "/messages", quiet=True)
        complete = bool(data and data.get("ok"))
        if complete:
            messages.extend(data["messages"])
        if include_archive:
            messages.extend(self.fetch_im_messages(serial))
            messages.extend(self.fetch_im_files(serial))
        messages.sort(key=lambda item: item.get("date") or 0)
        return messages, complete

    def _accept_snapshot(self, serial, loaded, complete):
        if not complete:
            return False, []
        with self.message_lock:
            changed = self._replace_messages(serial, loaded)
            if serial not in self._session_baselined:
                self._baseline_history(serial)
                return changed, []
            return changed, self._absorb_arrivals(serial, full_snapshot=True)

    def fetch_im_messages(self, serial):
        query = "content query --uri content://im/chat --projection _id:address:body:date:type:content_type"
        result = self.adb_run(serial, "shell", query, timeout=20)
        messages = []
        for line in (result.stdout or "").splitlines():
            if not line.startswith("Row:"):
                continue
            fields = self.parse_content_row(line)
            kind = fields.get("type")
            if kind not in {"1", "2"}:
                continue
            body = fields.get("body") or ""
            if body in {"", "NULL"}:
                content_type = fields.get("content_type") or ""
                body = "[이미지]" if content_type.startswith("image/") else ""
            try:
                date = int(fields.get("date") or 0)
            except ValueError:
                continue
            messages.append({
                "key": f"im:{fields.get('_id')}",
                "kind": "im",
                "address": fields.get("address") or "",
                "body": "" if body == "NULL" else body,
                "date": date,
                "incoming": kind == "1",
                "images": [],
            })
        return messages

    def fetch_im_files(self, serial):
        query = "content query --uri content://im/ft --projection _id:address:date:type:content_type:hidden"
        result = self.adb_run(serial, "shell", query, timeout=20)
        messages = []
        for line in (result.stdout or "").splitlines():
            if not line.startswith("Row:"):
                continue
            fields = self.parse_content_row(line)
            if fields.get("hidden") not in {None, "", "0", "NULL"}:
                continue
            content_type = fields.get("content_type") or ""
            if not content_type.startswith("image/"):
                continue
            kind = fields.get("type")
            if kind not in {"1", "2"}:
                continue
            try:
                date = int(fields.get("date") or 0)
                ft_id = int(fields.get("_id") or 0)
            except ValueError:
                continue
            if ft_id <= 0:
                continue
            messages.append({
                "key": f"ft:{ft_id}",
                "kind": "ft",
                "address": fields.get("address") or "",
                "body": "",
                "date": date,
                "incoming": kind == "1",
                "images": [{"id": f"ft:{ft_id}", "source": "ft"}],
            })
        return messages

    def read_ft_image(self, serial, ft_id):
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        try:
            result = subprocess.run(
                [self.adb, "-s", serial, "exec-out", "content", "read", "--uri", f"content://im/ft_original/{ft_id}"],
                capture_output=True, timeout=20, creationflags=flags,
            )
        except Exception:
            return None
        raw = result.stdout or b""
        if raw.startswith((b"\x89PNG", b"\xff\xd8\xff", b"GIF8", b"RIFF", b"BM")):
            return raw
        return None

    def parse_content_row(self, line):
        payload = line.split(" ", 2)[-1]
        parts = []
        current = ""
        for token in payload.split(", "):
            if "=" in token and current:
                parts.append(current)
                current = token
            elif current:
                current += ", " + token
            else:
                current = token
        if current:
            parts.append(current)
        fields = {}
        for part in parts:
            if "=" not in part:
                continue
            key, value = part.split("=", 1)
            fields[key.strip()] = value
        return fields

    def poll_messages(self):
        if self.devices and not self.fast_sync_running:
            self.fast_sync_running = True
            threading.Thread(target=self._fast_sync, daemon=True).start()
        if self.devices and not self.message_sync_running and time.time() >= self._full_sync_at:
            self._full_sync_at = time.time() + 90
            self.message_sync_running = True
            threading.Thread(target=self._sync_messages, daemon=True).start()
        self.root.after(1000, self.poll_messages)

    def _sync_messages(self):
        try:
            changed = False
            arrivals = []
            for serial, device in list(self.devices.items()):
                if not device.get("online"):
                    continue
                messages, complete = self.collect_messages(serial, device["port"])
                changed_now, found = self._accept_snapshot(serial, messages, complete)
                if changed_now:
                    changed = True
                arrivals.extend(found)
            before = len(self.sent_notices)
            self.sent_notices = [notice for notice in self.sent_notices if not self._notice_confirmed(notice)]
            self._schedule_sync_result(changed or len(self.sent_notices) != before, arrivals)
        finally:
            self.message_sync_running = False

    def _fast_sync(self):
        try:
            serials = [serial for serial, device in list(self.devices.items()) if device.get("online")]
            jobs = []
            for serial in serials:
                jobs.append((serial, "sms", self._recent_since(serial, "sms:")))
                jobs.append((serial, "im", self._recent_since(serial, "im:")))
            if not jobs:
                return
            from concurrent.futures import ThreadPoolExecutor

            def work(job):
                serial, kind, since = job
                if kind == "sms":
                    query = f'content query --uri content://sms --projection _id:address:body:date:type --where "date>{since}"'
                else:
                    query = (
                        "content query --uri content://im/chat "
                        "--projection _id:address:body:date:type:content_type "
                        f'--where "date>{since}"'
                    )
                result = self.adb_run(serial, "shell", query, timeout=12)
                return serial, self._messages_from_query(result.stdout or "", kind)

            changed = False
            arrivals = []
            with ThreadPoolExecutor(max_workers=min(4, len(jobs))) as pool:
                for serial, rows in pool.map(work, jobs):
                    with self.message_lock:
                        if serial in self._session_baselined and self._merge_messages(serial, rows):
                            changed = True
                            arrivals.extend(self._absorb_arrivals(serial, full_snapshot=False))
                        elif self._merge_messages(serial, rows):
                            changed = True
            before = len(self.sent_notices)
            self.sent_notices = [notice for notice in self.sent_notices if not self._notice_confirmed(notice)]
            self._schedule_sync_result(changed or len(self.sent_notices) != before, arrivals)
        finally:
            self.fast_sync_running = False

    def _recent_since(self, serial, prefix):
        stamp = self._prefix_max.get(serial, {}).get(prefix, 0)
        if stamp:
            return stamp - 2000
        return int(time.time() * 1000) - 120000

    def _content_rows(self, text):
        current = ""
        for line in text.splitlines():
            if line.startswith("Row:"):
                if current:
                    yield current
                current = line
            elif current:
                current += "\n" + line
        if current:
            yield current

    def _messages_from_query(self, text, kind):
        messages = []
        for line in self._content_rows(text):
            fields = self.parse_content_row(line)
            message_type = fields.get("type")
            if message_type not in {"1", "2"}:
                continue
            try:
                date = int(fields.get("date") or 0)
                message_id = int(fields.get("_id") or 0)
            except ValueError:
                continue
            if message_id <= 0:
                continue
            body = fields.get("body") or ""
            if body in {"", "NULL"}:
                content_type = fields.get("content_type") or ""
                body = "[이미지]" if content_type.startswith("image/") else ""
            messages.append({
                "key": f"{kind}:{message_id}",
                "kind": kind,
                "address": fields.get("address") or "",
                "body": "" if body == "NULL" else body,
                "date": date,
                "incoming": message_type == "1",
                "images": [],
            })
        return messages

    def _merge_messages(self, serial, fresh):
        current = self.messages.setdefault(serial, [])
        known = {item.get("key") for item in current}
        added = [item for item in fresh if item.get("key") not in known]
        if not added:
            return False
        current.extend(added)
        current.sort(key=lambda item: item.get("date") or 0)
        self._reindex_messages(serial)
        return True

    def _replace_messages(self, serial, messages):
        newest = max((item["date"] for item in messages), default=0)
        incoming_keys = {item.get("key") for item in messages}
        kept = [
            item for item in self.messages.get(serial, [])
            if item.get("key") not in incoming_keys and item["date"] >= newest - 5000
        ]
        merged = messages + kept
        merged.sort(key=lambda item: item.get("date") or 0)
        old_keys = [item.get("key") for item in self.messages.get(serial, [])]
        self.messages[serial] = merged
        self._reindex_messages(serial)
        return old_keys != [item.get("key") for item in merged]

    def _reindex_messages(self, serial):
        grouped = defaultdict(list)
        prefix_max = {}
        for message in self.messages.get(serial, []):
            norm = message.get("norm") or normalize_phone(message.get("address")) or "알 수 없음"
            message["norm"] = norm
            grouped[norm].append(message)
            key = str(message.get("key") or "")
            if key.startswith("sms:"):
                prefix = "sms:"
            elif key.startswith("im:"):
                prefix = "im:"
            else:
                prefix = ""
            if prefix:
                prefix_max[prefix] = max(prefix_max.get(prefix, 0), message.get("date") or 0)
        self.message_index[serial] = grouped
        self._index_size[serial] = len(self.messages.get(serial, []))
        self._prefix_max[serial] = prefix_max
        self._recount_unread(serial)

    def _recount_unread(self, serial):
        if serial not in self._session_baselined:
            self._unread_total[serial] = 0
            self._unread_by_address[serial] = {}
            return
        seen = self.config["seen"].get(serial, {})
        counts = {}
        total = 0
        for norm, items in self.message_index.get(serial, {}).items():
            seen_at = seen.get(norm, 0)
            count = sum(1 for message in items if message.get("incoming") and (message.get("date") or 0) > seen_at)
            if count:
                counts[norm] = count
                total += count
        self._unread_by_address[serial] = counts
        self._unread_total[serial] = total

    def _baseline_history(self, serial):
        if serial in self._session_baselined:
            return
        seen = self.config["seen"].setdefault(serial, {})
        keys = set()
        for norm, items in self.message_index.get(serial, {}).items():
            latest = 0
            for message in items:
                if not message.get("incoming"):
                    continue
                latest = max(latest, message.get("date") or 0)
                if message.get("key"):
                    keys.add(message["key"])
            if latest > seen.get(norm, 0):
                seen[norm] = latest
        self.alert_known[serial] = keys
        self.alert_ready.add(serial)
        self._session_baselined.add(serial)
        if serial not in self.config["initialized"]:
            self.config["initialized"].append(serial)
        self._recount_unread(serial)
        self._save_config_soon()

    def _thread_messages(self, serial, address):
        total = len(self.messages.get(serial, []))
        if self._index_size.get(serial) != total:
            self._reindex_messages(serial)
        norm = normalize_phone(address) or "알 수 없음"
        return self.message_index.get(serial, {}).get(norm, [])

    def _mark_open_thread_seen(self):
        serial, address = self.active_serial, self.active_address
        if not serial or not address:
            return
        dates = [
            item["date"] for item in self._thread_messages(serial, address)
            if item.get("incoming")
        ]
        if not dates:
            return
        seen = self.config["seen"].setdefault(serial, {})
        norm = normalize_phone(address)
        latest = max(dates)
        if latest > seen.get(norm, 0):
            seen[norm] = latest
            self._recount_unread(serial)
            self.save_config()

    def _absorb_arrivals(self, serial, full_snapshot):
        current = [
            item for item in self.messages.get(serial, [])
            if item.get("incoming") and item.get("key")
        ]
        keys = {item["key"] for item in current}
        if serial not in self.alert_ready:
            if full_snapshot:
                self.alert_ready.add(serial)
                self.alert_known[serial] = keys
            return []
        known = self.alert_known.setdefault(serial, set())
        fresh = [item for item in current if item["key"] not in known]
        known.update(keys)
        if full_snapshot:
            cutoff = int(time.time() * 1000) - 180000
            fresh = [item for item in fresh if (item.get("date") or 0) >= cutoff]
        arrivals = []
        for item in fresh:
            address = normalize_phone(item.get("address")) or "알 수 없음"
            self.fresh_marks.add((serial, address, item["key"]))
            arrivals.append({
                "serial": serial,
                "key": item["key"],
                "address": item.get("address") or address,
                "body": item.get("body") or "",
                "date": item.get("date") or 0,
                "images": bool(item.get("images")),
            })
        arrivals.sort(key=lambda item: item["date"], reverse=True)
        return arrivals

    def _schedule_sync_result(self, changed, arrivals):
        unique = []
        seen = set()
        for item in arrivals:
            token = (item.get("serial"), item.get("key"))
            if token in seen:
                continue
            seen.add(token)
            unique.append(item)

        def apply():
            if self._app_is_active():
                self._mark_open_thread_seen()
            if changed or unique:
                self.render_all()
            else:
                self._refresh_notice_bar()
            if unique:
                self._announce_arrivals(unique)

        self.root.after(0, apply)

    def _app_is_active(self):
        try:
            if str(self.root.state()) == "iconic":
                return False
            return bool(self.root.focus_displayof())
        except tk.TclError:
            return False

    def _phone_name(self, serial):
        device = self.devices.get(serial) or {}
        return self.config["names"].get(serial, device.get("model") or serial)

    def render_all(self):
        self._render_dirty = True
        if self._render_queued:
            return
        self._render_queued = True
        self.root.after(40, self._flush_render)

    def _flush_render(self):
        self._render_queued = False
        self._render_dirty = False
        self.render_devices()
        if self.active_serial in self.devices:
            self.render_threads()
            if self.active_address:
                self.render_chat()
        self._refresh_notice_bar()
        if self._render_dirty:
            self.render_all()

    def unread_for(self, serial, address=None):
        if serial not in self._session_baselined:
            return 0
        if address is None:
            return self._unread_total.get(serial, 0)
        norm = normalize_phone(address) or "알 수 없음"
        return self._unread_by_address.get(serial, {}).get(norm, 0)

    def render_devices(self):
        selected = self.active_serial
        rows = []
        for serial, device in self.devices.items():
            name = self.config["names"].get(serial, device["model"])
            unread = self.unread_for(serial)
            state = "연결됨" if device["online"] else "브리지 실행 필요"
            if unread:
                label = f"● {name}    새 메시지 {unread}건"
                tags = ("unread",)
            else:
                label = name
                tags = ("read",)
            rows.append((serial, label, state, tags))
        signature = (selected, tuple(rows))
        if signature == getattr(self, "_device_signature", None):
            return
        self._device_signature = signature
        self.suppress_selection = True
        self._suppress_token += 1
        token = self._suppress_token
        self.device_tree.delete(*self.device_tree.get_children())
        self.device_rows.clear()
        for serial, label, state, tags in rows:
            self.device_rows[serial] = self.device_tree.insert(
                "", "end", iid=serial, text=label, values=(state,), tags=tags)
        if selected in self.devices:
            self.device_tree.selection_set(selected)
        elif self.devices:
            first = next(iter(self.devices))
            self.device_tree.selection_set(first)
            self.select_device(first)
        self.root.after_idle(lambda token=token: self._release_selection_suppress(token))

    def ensure_bridge(self, serial, port):
        self.adb_run(serial, "forward", f"tcp:{port}", "tcp:8765")
        status = self.api(port, "/status", quiet=True)
        if status and status.get("ok"):
            return status
        installed = self.adb_run(serial, "shell", "pm", "path", BRIDGE_PACKAGE)
        apk = app_dir() / "UsbSmsBridge.apk"
        if "package:" not in (installed.stdout or ""):
            if apk.exists():
                self.set_status("새 스마트폰에 브리지를 설치하는 중... 휴대폰에서 USB 설치를 허용해 주세요.")
                self.adb_run(serial, "install", "-r", str(apk), timeout=180)
        for permission in BRIDGE_PERMISSIONS:
            self.adb_run(serial, "shell", "pm", "grant", BRIDGE_PACKAGE, permission)
        self.adb_run(serial, "shell", "am", "start", "-n", BRIDGE_ACTIVITY)
        for _ in range(12):
            time.sleep(0.4)
            status = self.api(port, "/status", quiet=True)
            if status and status.get("ok"):
                return status
        return None

    def on_device_select(self, _event=None):
        if self.suppress_selection:
            return
        selected = self.device_tree.selection()
        if not selected:
            return
        serial = selected[0]
        if serial == self.active_serial and self.devices.get(serial, {}).get("online"):
            return
        self.select_device(serial)

    def select_device(self, serial):
        switching = serial != self.active_serial
        self.active_serial = serial
        if switching:
            self.active_address = None
            self.render_threads()
            self.clear_chat()
        if self.devices.get(serial, {}).get("online"):
            return
        self.set_status("휴대폰 브리지를 시작하는 중...")
        threading.Thread(target=self._bring_device_online, args=(serial,), daemon=True).start()

    def _bring_device_online(self, serial):
        device = self.devices.get(serial)
        if not device:
            return
        status = self.ensure_bridge(serial, device["port"])
        device["online"] = bool(status and status.get("ok"))
        if device["online"]:
            loaded, complete = self.collect_messages(serial, device["port"])
            self._accept_snapshot(serial, loaded, complete)
            self._full_sync_at = time.time() + 90
            self.root.after(0, self.render_all)
            self.set_status(f"{device['model']} 연결됨")
        else:
            self.set_status("브리지를 시작하지 못했습니다. 휴대폰에서 문자 권한을 허용해 주세요.")

    def render_threads(self):
        selected = self.active_address
        query = self.thread_search.get().strip().lower()
        serial = self.active_serial
        if self._index_size.get(serial) != len(self.messages.get(serial, [])):
            self._reindex_messages(serial)
        groups = self.message_index.get(serial, {})
        unread_counts = self._unread_by_address.get(serial, {}) if serial in self._session_baselined else {}
        selected_norm = normalize_phone(selected) if selected else ""
        pending_preview = {}
        for notice in self.sent_notices:
            if notice.get("serial") != serial or self._notice_confirmed(notice):
                continue
            pending_preview[normalize_phone(notice.get("address"))] = notice.get("text") or notice.get("label") or ""
        ranked = sorted(
            groups.items(),
            key=lambda item: (0 if unread_counts.get(item[0]) else 1, -(item[1][-1]["date"] if item[1] else 0)),
        )
        rows = []
        for address, items in ranked:
            if query:
                searchable = address + "\n" + "\n".join((item.get("body") or "") for item in items)
                if query not in searchable.lower():
                    continue
            latest = items[-1]
            preview = pending_preview.get(address) or latest.get("body") or ("[이미지]" if latest.get("images") else "")
            unread = unread_counts.get(address, 0)
            preview_text = preview.replace("\n", " ")
            if unread:
                label = f"● {address}    새 {unread}건"
                preview_text = f"새 메시지  {preview_text[:48]}"
                tags = ("unread",)
            else:
                label = address
                preview_text = preview_text[:35]
                tags = ("read",)
            rows.append((address, label, preview_text, tags))
        if selected_norm and selected_norm not in groups and (not query or query in selected_norm.lower()):
            rows.insert(0, (selected_norm, selected_norm, "[새 메시지]", ("read",)))
        signature = (self.active_serial, selected_norm, tuple(rows))
        if signature == getattr(self, "_thread_signature", None):
            return
        self._thread_signature = signature
        self.suppress_selection = True
        self._suppress_token += 1
        token = self._suppress_token
        self.thread_tree.delete(*self.thread_tree.get_children())
        for address, label, preview_text, tags in rows:
            self.thread_tree.insert("", "end", iid=address, values=("열기", label, preview_text), tags=tags)
        if selected_norm and self.thread_tree.exists(selected_norm):
            self.thread_tree.selection_set(selected_norm)
        self.root.after_idle(lambda token=token: self._release_selection_suppress(token))

    def _release_selection_suppress(self, token):
        if token == self._suppress_token:
            self.suppress_selection = False

    def new_conversation(self):
        if not self.active_serial or not self.devices.get(self.active_serial, {}).get("online"):
            messagebox.showwarning("스마트폰 선택", "메시지를 보낼 스마트폰을 먼저 선택하세요.")
            return
        number = simpledialog.askstring("신규 번호", "메시지를 보낼 전화번호를 입력하세요.")
        if not number:
            return
        number = re.sub(r"[^0-9+]", "", number)
        if not number:
            messagebox.showwarning("번호 확인", "올바른 전화번호를 입력하세요.")
            return
        self.active_address = number
        self.thread_search.set("")
        self.render_threads()
        if self.thread_tree.exists(number):
            self.thread_tree.selection_set(number)
            self.thread_tree.see(number)
        self.render_chat()
        self.compose.focus_set()

    def on_thread_select(self, _event=None):
        if self.suppress_selection or getattr(self, "_opening_thread", False):
            return
        selected = self.thread_tree.selection()
        if not selected:
            return
        self._opening_thread = True
        try:
            self.active_address = selected[0]
            serial = self.active_serial
            norm = normalize_phone(self.active_address)
            items = self._thread_messages(serial, self.active_address)
            if items:
                seen = self.config["seen"].setdefault(serial, {})
                latest = max(item["date"] for item in items)
                if latest > seen.get(norm, 0):
                    seen[norm] = latest
                    self._recount_unread(serial)
                    self._save_config_soon()
            self.fresh_marks = {mark for mark in self.fresh_marks if not (mark[0] == serial and mark[1] == norm)}
            self._mark_thread_row_read(norm)
            self.render_chat()
        finally:
            self._opening_thread = False

    def _save_config_soon(self):
        if self._save_after:
            return
        self._save_after = self.root.after(400, self._flush_config_save)

    def _flush_config_save(self):
        self._save_after = None
        self.save_config()

    def _mark_thread_row_read(self, address):
        if not self.thread_tree.exists(address):
            return
        values = list(self.thread_tree.item(address, "values"))
        if len(values) < 3:
            return
        preview = str(values[2])
        if preview.startswith("새 메시지"):
            preview = preview.replace("새 메시지  ", "", 1).strip()
        values[1] = address
        values[2] = preview[:35]
        self.thread_tree.item(address, values=values, tags=("read",))

    def on_thread_shortcut(self, event):
        if self.thread_tree.identify_column(event.x) != "#1":
            return
        row = self.thread_tree.identify_row(event.y)
        if row:
            self.open_phone_conversation(row)

    def _phone_lock_state(self, serial):
        result = self.adb_run(
            serial, "shell",
            "dumpsys power | grep -m 1 mWakefulness=; dumpsys window | grep -m 1 isKeyguardShowing=",
            timeout=8,
        )
        text = result.stdout or ""
        wake = re.search(r"mWakefulness=(\w+)", text)
        guard = re.search(r"isKeyguardShowing=(true|false)", text)
        asleep = not wake or wake.group(1) != "Awake"
        locked = bool(guard and guard.group(1) == "true")
        return asleep, locked

    def _display_size(self, serial):
        result = self.adb_run(serial, "shell", "wm", "size", timeout=8)
        found = None
        for line in (result.stdout or "").splitlines():
            if "size:" not in line or "x" not in line:
                continue
            part = line.split(":", 1)[-1].strip()
            width, height = part.split("x", 1)
            if width.isdigit() and height.isdigit():
                found = (int(width), int(height))
                if line.strip().startswith("Override"):
                    return found
        return found or (1080, 2400)

    def _wake_for_open(self, serial):
        asleep, locked = self._phone_lock_state(serial)
        if not asleep and not locked:
            return False
        if asleep:
            self.adb_run(serial, "shell", "input", "keyevent", "KEYCODE_WAKEUP", timeout=8)
            time.sleep(0.45)
        self.adb_run(serial, "shell", "wm", "dismiss-keyguard", timeout=8)
        time.sleep(0.25)
        _, locked = self._phone_lock_state(serial)
        if locked:
            self.adb_run(serial, "shell", "input", "keyevent", "82", timeout=8)
            time.sleep(0.2)
            _, locked = self._phone_lock_state(serial)
        if locked:
            width, height = self._display_size(serial)
            x = str(width // 2)
            self.adb_run(
                serial, "shell", "input", "swipe",
                x, str(int(height * 0.78)), x, str(int(height * 0.28)), "180",
                timeout=8,
            )
            time.sleep(0.25)
        return True

    def open_phone_conversation(self, address):
        serial = self.active_serial
        number = re.sub(r"[^0-9+]", "", address or "")
        if not serial or not number:
            self.set_status("스마트폰에서 열 대화를 찾지 못했습니다.")
            return

        def work():
            woke = self._wake_for_open(serial)
            result = self.adb_run(
                serial, "shell", "am", "start",
                "-a", "android.intent.action.VIEW",
                "-d", f"sms:{number}",
                "-p", "com.samsung.android.messaging",
            )
            output = f"{result.stdout}\n{result.stderr}"
            if result.returncode != 0 or "Error" in output:
                self.adb_run(
                    serial, "shell", "am", "start",
                    "-a", "android.intent.action.VIEW",
                    "-d", f"sms:{number}",
                )
            self.set_status(f"스마트폰에서 {number} 대화를 열었습니다.")

        threading.Thread(target=work, daemon=True).start()

    def update_unread_labels(self):
        for serial in self.devices:
            if self.device_tree.exists(serial):
                name = self.config["names"].get(serial, self.devices[serial]["model"])
                unread = self.unread_for(serial)
                if unread:
                    label = f"● {name}    새 메시지 {unread}건"
                    tags = ("unread",)
                else:
                    label = name
                    tags = ("read",)
                self.device_tree.item(serial, text=label, tags=tags)
        for address in self.thread_tree.get_children():
            unread = self.unread_for(self.active_serial, address)
            values = list(self.thread_tree.item(address, "values"))
            if len(values) >= 3:
                if unread:
                    values[1] = f"● {address}    새 {unread}건"
                    preview = values[2]
                    if not str(preview).startswith("새 메시지"):
                        values[2] = f"새 메시지  {preview}"
                    tags = ("unread",)
                else:
                    values[1] = address
                    preview = str(values[2])
                    if preview.startswith("새 메시지"):
                        values[2] = preview.replace("새 메시지  ", "", 1).strip()
                    tags = ("read",)
                self.thread_tree.item(address, values=values, tags=tags)
        self._refresh_notice_bar()

    def _sync_chat_scroll(self, _event=None):
        self.chat_canvas.configure(scrollregion=self.chat_canvas.bbox("all") or (0, 0, 0, 0))

    def _stretch_chat(self, event):
        self.chat_canvas.itemconfigure(self.chat_window, width=event.width)

    def _chat_wheel(self, event):
        widget = event.widget
        while widget is not None:
            if widget == self.chat_canvas:
                self.chat_canvas.yview_scroll(int(-event.delta / 120), "units")
                return
            widget = getattr(widget, "master", None)

    def clear_chat(self):
        self._paint_token += 1
        self.chat_title.set("대화를 선택하세요")
        self._rendered_address = None
        self._chat_signature = None
        self._visible_chat_page = None
        for page in self.chat_pages.values():
            page["frame"].destroy()
        self.chat_pages.clear()
        self.image_refs = []

    def render_chat(self):
        serial, address = self.active_serial, self.active_address
        if not serial or not address:
            return
        unread = self.unread_for(serial, address)
        title = f"{address}  ·  {self.config['names'].get(serial, self.devices[serial]['model'])}"
        if unread:
            title = f"● 새 메시지 {unread}건  ·  {title}"
        self.chat_title.set(title)
        items = [
            message for message in self._thread_messages(serial, address)
            if not self._shown_as_notice(serial, message)
        ]
        for notice in self.sent_notices:
            if notice["serial"] != serial or not same_phone(notice["address"], address) or self._notice_confirmed(notice):
                continue
            label = notice.get("label") or ""
            show_label = bool(notice.get("image")) or label not in {"전송됨", "이미지 전송됨"}
            items.append({
                "incoming": False,
                "date": int(notice["at"] * 1000),
                "body": notice.get("text") or "",
                "local_image": notice.get("image"),
                "sent_label": label if show_label else "",
            })
        items.sort(key=lambda item: item["date"])
        thread_key = (serial, normalize_phone(address))
        limit = self.chat_limit.get(thread_key, 80)
        hidden = max(0, len(items) - limit)
        shown = items[-limit:]
        signature = (thread_key, hidden, tuple(self._chat_item_token(serial, item) for item in shown))
        cached = self.chat_pages.get(thread_key)
        anchor = getattr(self, "_chat_anchor", "stick")
        self._chat_anchor = "stick"
        if cached and cached["signature"] == signature:
            self._chat_signature = signature
            self._rendered_address = thread_key
            show_anchor = "keep" if anchor == "stick" and cached is not self._visible_chat_page else anchor
            self._show_chat_page(cached, show_anchor)
            return
        if cached:
            if self._visible_chat_page is cached:
                self._visible_chat_page = None
            cached["frame"].destroy()
        self._paint_token += 1
        token = self._paint_token
        frame = tk.Frame(self.chat_inner, background=CHAT_BG)
        page = {
            "frame": frame,
            "signature": signature,
            "images": [],
            "token": token,
            "view": (0.0, 1.0),
        }
        self.chat_pages[thread_key] = page
        self._remember_chat_page(thread_key)
        self._chat_signature = signature
        self._rendered_address = thread_key
        self._show_chat_page(page, "top" if anchor == "top" else "stick")
        if hidden:
            tk.Button(
                frame, text=f"이전 메시지 {hidden}건 보기",
                command=self._show_older_messages, relief="flat",
                background="#D5DEE8", activebackground="#C5D0DC",
                font=("맑은 고딕", 9), padx=10, pady=4,
            ).pack(pady=(8, 2))
        if not shown:
            tk.Label(
                frame, text="이 번호와 주고받은 문자가 없습니다.",
                background=CHAT_BG, foreground=META_IN, font=("맑은 고딕", 11),
            ).pack(pady=24)
            return
        width = max(self.chat_canvas.winfo_width(), 420)
        wrap = max(220, min(360, int(width * 0.62)))
        self.root.after(
            1, lambda: self._paint_chat_slice(token, thread_key, shown, 0, None, wrap, serial, anchor)
        )

    def _remember_chat_page(self, thread_key):
        order = [
            key for key in getattr(self, "_chat_page_order", [])
            if key != thread_key and key in self.chat_pages
        ]
        order.append(thread_key)
        self._chat_page_order = order
        while len(order) > 4:
            old = order.pop(0)
            page = self.chat_pages.get(old)
            if page and page is self._visible_chat_page:
                order.append(old)
                if order[0] == old:
                    break
                continue
            self.chat_pages.pop(old, None)
            if page:
                page["token"] = None
                try:
                    page["frame"].destroy()
                except tk.TclError:
                    pass

    def _show_chat_page(self, page, anchor):
        current = self._visible_chat_page
        if current is not None and current is not page:
            try:
                current["view"] = self.chat_canvas.yview()
                current["frame"].pack_forget()
            except tk.TclError:
                pass
        if not page["frame"].winfo_ismapped():
            page["frame"].pack(fill="x")
        self._visible_chat_page = page
        self.image_refs = page["images"]
        self.chat_inner.update_idletasks()
        self._sync_chat_scroll()
        if anchor == "top":
            self.chat_canvas.yview_moveto(0)
        elif anchor == "keep" and page.get("view"):
            self.chat_canvas.yview_moveto(page["view"][0])
        else:
            self.chat_canvas.yview_moveto(1)

    def _paint_chat_slice(self, token, thread_key, shown, index, last_day, wrap, serial, anchor):
        page = self.chat_pages.get(thread_key)
        if not page or page.get("token") != token:
            return
        frame = page["frame"]
        end = min(index + 10, len(shown))
        for message in shown[index:end]:
            stamp = datetime.fromtimestamp((message.get("date") or 0) / 1000)
            day = stamp.strftime("%Y년 %m월 %d일")
            if day != last_day:
                last_day = day
                tk.Label(
                    frame, text=day, background="#D5DEE8", foreground="#243140",
                    font=("맑은 고딕", 8), padx=10, pady=3,
                ).pack(pady=(12, 4))
            self._add_message_bubble(
                message, serial, stamp.strftime("%H:%M"), wrap, frame, page["images"]
            )
        visible = self._visible_chat_page is page
        if visible:
            self.chat_inner.update_idletasks()
            self._sync_chat_scroll()
            if anchor == "top":
                self.chat_canvas.yview_moveto(0)
            elif index == 0 or anchor != "keep":
                self.chat_canvas.yview_moveto(1)
        if end < len(shown):
            self.root.after(
                1, lambda i=end, day=last_day: self._paint_chat_slice(
                    token, thread_key, shown, i, day, wrap, serial, anchor
                )
            )
            return
        self._prefetch_recent_images(serial, shown)

    def _chat_item_token(self, serial, message):
        images = tuple(
            (str(image.get("id")), (serial, str(image.get("id"))) in self.media_cache)
            for image in (message.get("images") or [])
        )
        fresh = (
            serial, normalize_phone(message.get("address")), message.get("key")
        ) in self.fresh_marks
        return (
            message.get("key"), message.get("date"), bool(message.get("incoming")),
            message.get("body") or "", message.get("sent_label") or "",
            str(message.get("local_image") or ""), fresh, images,
        )

    def _show_older_messages(self):
        serial, address = self.active_serial, self.active_address
        if not serial or not address:
            return
        key = (serial, normalize_phone(address))
        self.chat_limit[key] = self.chat_limit.get(key, 80) + 80
        self._chat_signature = None
        self._chat_anchor = "top"
        self.render_chat()

    def _add_message_bubble(self, message, serial, clock, wrap, parent=None, image_store=None):
        incoming = bool(message.get("incoming"))
        failed = message.get("sent_label") == "전송 실패"
        fresh = incoming and (
            serial, normalize_phone(message.get("address")), message.get("key")
        ) in self.fresh_marks
        bubble_bg = "#FFF4E5" if fresh else (BUBBLE_IN if incoming else (BUBBLE_FAIL if failed else BUBBLE_OUT))
        text_color = TEXT_IN if incoming else TEXT_OUT
        hint_color = "#9A3412" if fresh else ("#5C6B7A" if incoming else "#D6E4FF")
        who = "새 메시지 · 받음" if fresh else ("상대 · 받음" if incoming else "나 · 보냄")
        who_color = "#C2410C" if fresh else (META_IN if incoming else META_OUT)
        row = tk.Frame(parent or self.chat_inner, background=CHAT_BG)
        row.pack(fill="x", padx=12, pady=3)
        holder = tk.Frame(row, background=CHAT_BG)
        holder.pack(side="left" if incoming else "right", anchor="w" if incoming else "e")
        if fresh:
            tk.Label(
                holder, text="방금 도착", background="#C2410C", foreground="#FFFFFF",
                font=("맑은 고딕", 8, "bold"), padx=6, pady=1,
            ).pack(anchor="w", padx=4, pady=(0, 2))
        tk.Label(
            holder, text=f"{who}   {clock}", background=CHAT_BG, foreground=who_color,
            font=("맑은 고딕", 8, "bold"),
        ).pack(anchor="w" if incoming else "e", padx=4)
        bubble = tk.Frame(
            holder, background=bubble_bg, padx=10, pady=8,
            highlightthickness=3 if fresh else (1 if incoming else 0),
            highlightbackground="#C2410C" if fresh else "#C5D0DC",
        )
        bubble.pack(anchor="w" if incoming else "e")
        body = (message.get("body") or "").strip()
        if body:
            label = tk.Label(
                bubble, text=body, background=bubble_bg, foreground=text_color,
                font=("맑은 고딕", 11), wraplength=wrap, justify="left",
            )
            label.pack(anchor="w")
            self._bind_bubble_copy(label, body)
        pictures = []
        if message.get("local_image"):
            pictures.append((message["local_image"], "sent_image.png"))
        else:
            for image in message.get("images") or []:
                raw = self.media_cache.get((serial, str(image["id"])))
                if not raw:
                    pictures.append((None, None))
                    continue
                suffix = "png" if raw.startswith(b"\x89PNG") else "jpg"
                pictures.append((raw, f"message_image_{image['id']}.{suffix}"))
        for raw, filename in pictures:
            if not raw:
                pending = tk.Label(bubble, text="이미지 불러오는 중", background=bubble_bg, foreground=hint_color, font=("맑은 고딕", 9))
                pending.pack(anchor="w", pady=(4, 0))
                continue
            self._add_bubble_image(bubble, raw, filename, bubble_bg, image_store)
            hint = tk.Label(bubble, text="클릭하면 크게 보기", background=bubble_bg, foreground=hint_color, font=("맑은 고딕", 8))
            hint.pack(anchor="w")
        status = message.get("sent_label")
        if status:
            tk.Label(bubble, text=status, background=bubble_bg, foreground=hint_color, font=("맑은 고딕", 8)).pack(anchor="e", pady=(4, 0))

    def _bind_bubble_copy(self, widget, text):
        def copy(_event=None, payload=text):
            self.root.clipboard_clear()
            self.root.clipboard_append(payload)
            return "break"
        widget.bind("<Control-c>", copy)
        widget.bind("<Control-C>", copy)

    def _add_bubble_image(self, parent, raw, filename, background, image_store=None):
        try:
            thumb = Image.open(io.BytesIO(raw)).copy()
            thumb.thumbnail((150, 110))
            photo = ImageTk.PhotoImage(thumb)
        except Exception:
            tk.Label(parent, text="이미지를 표시할 수 없음", background=background, foreground=TEXT_IN, font=("맑은 고딕", 9)).pack(anchor="w")
            return
        label = tk.Label(parent, image=photo, background=background, cursor="hand2", bd=0)
        label.bind("<Button-1>", lambda _e, data=raw, name=filename: self.open_image_viewer(data, name))
        label.pack(anchor="w", pady=(4, 0))
        store = self.image_refs if image_store is None else image_store
        store.append(photo)

    def _prefetch_recent_images(self, serial, items):
        needed = []
        for message in items:
            for image in message.get("images") or []:
                key = (serial, str(image["id"]))
                if key not in self.media_cache and key not in self.media_loading:
                    needed.append(image)
                    self.media_loading.add(key)
        if not needed:
            return
        address = self.active_address

        def work():
            for image in needed:
                key = (serial, str(image["id"]))
                if image.get("source") == "ft":
                    raw = self.read_ft_image(serial, str(image["id"]).split(":", 1)[-1])
                else:
                    raw = self.api(self.devices[serial]["port"], f"/media?id={image['id']}", binary=True, quiet=True)
                if raw:
                    self.media_cache[key] = raw
                self.media_loading.discard(key)
            if self.active_serial == serial and same_phone(self.active_address, address):
                self.root.after(0, self.render_chat)

        threading.Thread(target=work, daemon=True).start()

    def choose_image(self):
        path = filedialog.askopenfilename(filetypes=[("이미지", "*.png *.jpg *.jpeg *.gif *.webp *.bmp")])
        if path:
            self.set_attachment(Path(path))

    def choose_and_send_image(self):
        self.choose_image()
        if self.attachment:
            self.send_message()

    def capture_screen(self):
        try:
            image = ImageGrab.grab(all_screens=True)
            path = Path(tempfile.gettempdir()) / f"pc_sms_capture_{int(time.time())}.png"
            image.save(path)
            self.set_attachment(path)
        except Exception as exc:
            messagebox.showerror("캡처 실패", str(exc))

    def capture_and_send_screen(self):
        self.capture_screen()
        if self.attachment:
            self.send_message()

    def clipboard_image(self):
        try:
            item = ImageGrab.grabclipboard()
        except Exception:
            return None
        if isinstance(item, Image.Image):
            return item
        if isinstance(item, list):
            for entry in item:
                path = Path(entry)
                if path.suffix.lower() in {".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp"} and path.exists():
                    try:
                        return Image.open(path)
                    except Exception:
                        continue
        return None

    def paste(self, _event=None):
        now = time.time()
        if now - getattr(self, "_paste_at", 0) < 0.4:
            return "break"
        self._paste_at = now
        self.root.after(200, self._send_clipboard_image)
        return "break"

    def _send_clipboard_image(self):
        image = self.clipboard_image()
        if image is None:
            self.set_status("클립보드에서 이미지를 읽지 못했습니다. 이미지를 다시 복사해 주세요.")
            return
        path = Path(tempfile.gettempdir()) / f"pc_sms_clipboard_{int(time.time())}.png"
        image.convert("RGBA").save(path)
        self.set_attachment(path)
        self.set_status("이미지를 붙였습니다. Enter를 누르면 전송됩니다.")
        self.compose.focus_set()

    def set_attachment(self, path):
        self.attachment = Path(path)
        self.attachment_text.set(f"첨부: {self.attachment.name}")
        try:
            image = Image.open(self.attachment)
            image.thumbnail((160, 100))
            self.attachment_preview = ImageTk.PhotoImage(image.copy())
            self.attachment_label.configure(image=self.attachment_preview, text=f"  첨부됨: {self.attachment.name}", compound="left")
        except Exception:
            self.attachment_label.configure(image="", text=f"첨부됨: {self.attachment.name}")
        self.compose.focus_set()

    def clear_attachment(self):
        self.attachment = None
        self.attachment_preview = None
        self.attachment_text.set("첨부 이미지 없음")
        self.attachment_label.configure(image="", text="")

    def extension_for_type(self, mime):
        mapping = {"image/png": "png", "image/gif": "gif", "image/webp": "webp", "image/bmp": "bmp"}
        return mapping.get(mime, "jpg")

    def open_image_viewer(self, raw, filename):
        try:
            original = Image.open(io.BytesIO(raw)).convert("RGBA")
        except Exception as exc:
            messagebox.showerror("이미지 열기 실패", str(exc))
            return
        viewer = tk.Toplevel(self.root)
        viewer.title(filename)
        viewer.geometry("1000x760")
        viewer.configure(background="#1B1B1B")
        top = tk.Frame(viewer, background="#1B1B1B")
        top.pack(fill="x")
        tk.Label(
            top, text=f"{filename}  {original.width} x {original.height}   휠로 확대/축소 · 드래그로 이동",
            background="#1B1B1B", foreground="#E8E8E8", font=("맑은 고딕", 9),
        ).pack(side="left", padx=10, pady=8)
        ttk.Button(top, text="컴퓨터에 저장", command=lambda: self.save_image(raw, filename)).pack(side="right", padx=8, pady=6)
        canvas = tk.Canvas(viewer, background="#1B1B1B", highlightthickness=0, bd=0)
        canvas.pack(fill="both", expand=True)
        state = {"zoom": 1.0, "ox": 0, "oy": 0, "photo": None, "user": False, "drag": None}

        def fit_scale():
            width = canvas.winfo_width()
            height = canvas.winfo_height()
            if width < 40 or height < 40:
                width, height = 960, 640
            return min(width / original.width, height / original.height)

        def render():
            scale = max(0.05, state["zoom"])
            resized = original.resize((max(1, int(original.width * scale)), max(1, int(original.height * scale))), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized)
            state["photo"] = photo
            canvas.delete("all")
            canvas.create_image(
                canvas.winfo_width() / 2 + state["ox"],
                canvas.winfo_height() / 2 + state["oy"],
                image=photo, anchor="center",
            )

        def on_configure(_event=None):
            if not state["user"]:
                state["zoom"] = fit_scale()
                state["ox"] = state["oy"] = 0
            render()

        def on_wheel(event):
            state["user"] = True
            factor = 1.12 if event.delta > 0 else 1 / 1.12
            state["zoom"] = min(8.0, max(fit_scale() * 0.2, state["zoom"] * factor))
            render()
            return "break"

        def on_press(event):
            state["drag"] = (event.x, event.y, state["ox"], state["oy"])

        def on_drag(event):
            if not state["drag"]:
                return
            x0, y0, ox, oy = state["drag"]
            state["ox"] = ox + event.x - x0
            state["oy"] = oy + event.y - y0
            render()

        canvas.bind("<Configure>", on_configure)
        canvas.bind("<MouseWheel>", on_wheel)
        canvas.bind("<ButtonPress-1>", on_press)
        canvas.bind("<B1-Motion>", on_drag)
        viewer.bind("<MouseWheel>", on_wheel)

    def save_image(self, raw, filename):
        path = filedialog.asksaveasfilename(
            title="이미지 저장",
            initialfile=filename,
            defaultextension=Path(filename).suffix,
            filetypes=[("이미지", "*.jpg *.jpeg *.png *.gif *.webp *.bmp"), ("모든 파일", "*.*")],
        )
        if path:
            Path(path).write_bytes(raw)
            self.set_status(f"이미지를 저장했습니다: {path}")

    def send_message(self):
        if not self.active_serial or not self.active_address:
            messagebox.showwarning("대화 선택", "메시지를 보낼 번호를 선택하세요.")
            return "break"
        text = self.compose.get("1.0", "end").strip()
        if not text and not self.attachment:
            return "break"
        notice = {
            "serial": self.active_serial,
            "address": self.active_address,
            "image": self.attachment.read_bytes() if self.attachment else None,
            "text": text,
            "at": time.time(),
            "label": "전송 중",
        }
        self.sent_notices.append(notice)
        self.compose.delete("1.0", "end")
        self.render_chat()
        self.render_threads()
        self.set_status("이미지를 전송하는 중..." if self.attachment else "메시지를 보내는 중...")
        threading.Thread(
            target=self._send_worker,
            args=(self.active_serial, self.active_address, text, self.attachment, notice),
            daemon=True,
        ).start()
        return "break"

    def on_compose_enter(self, _event=None):
        return self.send_message()

    def on_compose_shift_enter(self, _event=None):
        self.compose.insert("insert", "\n")
        return "break"

    def _send_worker(self, serial, address, text, attachment, notice=None):
        port = self.devices[serial]["port"]
        if attachment:
            opened = self.open_image_composer(serial, address, attachment, text)
            result = {"ok": bool(opened), "direct": False, "note": "이미지 작성 화면을 열지 못했습니다."}
            if opened:
                sent, detail = self.automate_image_send(serial, address)
                result["ok"] = True
                result["direct"] = sent
                result["note"] = detail
        else:
            result = self.api(port, "/send", {"to": address, "text": text})
        if notice is not None:
            if attachment:
                notice["label"] = "이미지 전송됨" if result and result.get("direct") else "전송 실패"
            else:
                notice["label"] = "전송됨" if result and result.get("ok") else "전송 실패"
            self.root.after(0, self.render_chat)
            self.root.after(0, self.render_threads)
        if result and result.get("ok"):
            self.root.after(0, self.clear_attachment)
            if attachment and result.get("direct"):
                self.set_status("이미지를 전송했습니다.", hold=30)
            elif attachment:
                self.set_status(result.get("note", "이미지 전송에 실패했습니다."), hold=15)
            else:
                self.set_status("메시지를 발송했습니다.")
        elif notice is not None and text and not attachment:
            self.root.after(0, lambda body=text: self._restore_compose(body))
            self.set_status("메시지 전송에 실패했습니다. 내용을 입력창에 다시 넣었습니다.", hold=15)

    def open_image_composer(self, serial, address, attachment, text):
        suffix = attachment.suffix.lower() if attachment.suffix else ".png"
        if suffix not in {".png", ".jpg", ".jpeg", ".webp"}:
            suffix = ".png"
        mime = "image/jpeg" if suffix in {".jpg", ".jpeg"} else "image/png"
        remote = f"/sdcard/Download/pc_sms_out{suffix}"
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        pushed = subprocess.run(
            [self.adb, "-s", serial, "push", str(attachment), remote],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=30, creationflags=flags,
        )
        if pushed.returncode != 0:
            return False
        number = re.sub(r"[^0-9+]", "", address)
        parts = [
            "am start",
            "-a android.intent.action.SEND",
            f"-t {mime}",
            "-p com.samsung.android.messaging",
        ]
        if text:
            escaped = text.replace("'", "'\\''")
            parts.append(f"--es sms_body '{escaped}'")
        parts.append(f"--es address {number}")
        parts.append(f"--eu android.intent.extra.STREAM file://{remote}")
        result = self.adb_run(serial, "shell", " ".join(parts), timeout=15)
        output = f"{result.stdout}\n{result.stderr}"
        return "Error" not in output and result.returncode == 0

    def automate_image_send(self, serial, address):
        number = re.sub(r"[^0-9+]", "", address)
        deadline = time.time() + 8
        filled_recipient = False
        try:
            while time.time() < deadline:
                root = self.dump_window(serial)
                on_recipient = self._find_control(root, ("add_to_recipients_button",), ())
                send_bounds = self._find_send_button(root)
                if send_bounds and not on_recipient:
                    self._tap_bounds(serial, send_bounds)
                    time.sleep(0.45)
                    self._confirm_send_dialog(serial)
                    if not self._has_attached_image(self.dump_window(serial)):
                        return True, "이미지를 PC에서 자동 전송했습니다."
                    self._tap_bounds(serial, send_bounds)
                    time.sleep(0.45)
                    if not self._has_attached_image(self.dump_window(serial)):
                        return True, "이미지를 PC에서 자동 전송했습니다."
                    continue
                if on_recipient and not filled_recipient:
                    filled_recipient = True
                    if not number:
                        return False, "이미지 작성 화면은 열었지만 받는 번호를 자동 입력하지 못했습니다."
                    search = self._find_control(root, ("search_src_text",), ())
                    if search:
                        self._tap_bounds(serial, search)
                        time.sleep(0.4)
                    self.adb_run(serial, "shell", "input", "text", number)
                    time.sleep(0.7)
                    root = self.dump_window(serial)
                    add = self._find_control(root, ("add_to_recipients_button",), ())
                    if add:
                        self._tap_bounds(serial, add)
                        time.sleep(0.8)
                    root = self.dump_window(serial)
                    done = self._find_control(root, ("action_menu_compose",), ("완료",))
                    if done:
                        self._tap_bounds(serial, done)
                        time.sleep(0.8)
                    continue
                time.sleep(0.25)
            return False, "이미지는 첨부됐지만 전송 버튼을 누르지 못했습니다. 휴대폰에서 전송을 눌러 주세요."
        except Exception as exc:
            return False, f"이미지 자동 전송 실패: {exc}"

    def dump_window(self, serial):
        remote = "/sdcard/usb_sms_window.xml"
        self.adb_run(serial, "shell", "uiautomator", "dump", remote, timeout=12)
        result = self.adb_run(serial, "shell", "cat", remote, timeout=10)
        text = result.stdout or ""
        start = text.find("<hierarchy")
        if start < 0:
            return None
        try:
            return ET.fromstring(text[start:])
        except ET.ParseError:
            return None

    def _node_bounds(self, node):
        numbers = [int(x) for x in re.findall(r"\d+", node.attrib.get("bounds", ""))]
        return numbers if len(numbers) == 4 else None

    def _match_control(self, node, resource_names, labels):
        rid = node.attrib.get("resource-id", "")
        if any(rid.endswith(":id/" + name) for name in resource_names):
            return True
        desc = (node.attrib.get("content-desc") or "").strip()
        text = (node.attrib.get("text") or "").strip()
        return desc in labels or text in labels

    def _find_send_button(self, root):
        if root is None:
            return None
        for node in root.iter("node"):
            rid = node.attrib.get("resource-id", "")
            desc = (node.attrib.get("content-desc") or "").strip()
            if not rid.endswith(":id/send_button"):
                continue
            if desc not in ("전송", "보내기", "Send", "Send message"):
                continue
            if node.attrib.get("clickable") != "true" or node.attrib.get("enabled") != "true":
                continue
            bounds = self._node_bounds(node)
            if bounds:
                return bounds
        return None

    def _has_attached_image(self, root):
        if root is None:
            return False
        for node in root.iter("node"):
            desc = node.attrib.get("content-desc") or ""
            rid = node.attrib.get("resource-id") or ""
            if "첨부된 이미지" in desc or rid.endswith(":id/attach_content_view"):
                return True
        return False

    def _find_control(self, root, resource_names, labels):
        if root is None:
            return None
        for node in root.iter("node"):
            if node.attrib.get("enabled") != "true":
                continue
            if not self._match_control(node, resource_names, labels):
                continue
            bounds = self._node_bounds(node)
            if bounds:
                return bounds
        return None

    def _tap_bounds(self, serial, bounds):
        x = (bounds[0] + bounds[2]) // 2
        y = (bounds[1] + bounds[3]) // 2
        self.adb_run(serial, "shell", "input", "tap", str(x), str(y))

    def _confirm_send_dialog(self, serial):
        root = self.dump_window(serial)
        if self._find_control(root, ("send_button", "composer_send_button"), ()):
            return
        confirm = self._find_control(root, ("positive_button",), ("확인", "전송"))
        if confirm:
            self._tap_bounds(serial, confirm)

    def wait_for_resource(self, serial, resource_name, timeout):
        end = time.time() + timeout
        while time.time() < end:
            if self.find_resource_bounds(serial, resource_name):
                return True
            time.sleep(0.7)
        return False

    def wait_and_tap(self, serial, resource_name, timeout):
        end = time.time() + timeout
        while time.time() < end:
            bounds = self.find_resource_bounds(serial, resource_name)
            if bounds:
                x = (bounds[0] + bounds[2]) // 2
                y = (bounds[1] + bounds[3]) // 2
                self.adb_run(serial, "shell", "input", "tap", str(x), str(y))
                time.sleep(1)
                return True
            time.sleep(0.7)
        return False

    def find_resource_bounds(self, serial, resource_name):
        remote = "/sdcard/usb_sms_window.xml"
        self.adb_run(serial, "shell", "uiautomator", "dump", remote, timeout=10)
        result = self.adb_run(serial, "shell", "cat", remote, timeout=10)
        try:
            root = ET.fromstring(result.stdout)
        except ET.ParseError:
            return None
        suffix = ":id/" + resource_name
        for node in root.iter("node"):
            if node.attrib.get("resource-id", "").endswith(suffix) and node.attrib.get("enabled") == "true":
                numbers = [int(x) for x in re.findall(r"\d+", node.attrib.get("bounds", ""))]
                if len(numbers) == 4:
                    return numbers
        return None

    def copy_chat_text(self, _event=None):
        return "break"

    def rename_device(self):
        if not self.active_serial:
            return
        current = self.config["names"].get(self.active_serial, self.devices[self.active_serial]["model"])
        name = simpledialog.askstring("스마트폰 이름 설정", "표시할 이름을 입력하세요.", initialvalue=current)
        if name and name.strip():
            self.config["names"][self.active_serial] = name.strip()
            self.save_config()
            self.render_devices()
            self.render_chat()

    def install_bridge(self):
        apk = app_dir() / "UsbSmsBridge.apk"
        if not apk.exists() or not self.devices:
            messagebox.showwarning("설치 불가", "APK 파일과 연결된 스마트폰을 확인하세요.")
            return
        threading.Thread(target=self._install_worker, args=(apk,), daemon=True).start()

    def _install_worker(self, apk):
        for serial in self.devices:
            self.set_status(f"{serial}: 브리지 앱 설치 중...")
            result = self.adb_run(serial, "install", "-r", str(apk), timeout=120)
            if "Success" in result.stdout:
                self.adb_run(serial, "shell", "am", "start", "-n", BRIDGE_ACTIVITY)
        self.set_status("설치 완료. 휴대폰에서 문자 권한을 허용하세요.")

    def poll(self):
        if not self.polling:
            self.polling = True
            def work():
                try:
                    self._refresh_worker(reload_messages=False)
                finally:
                    self.polling = False
            threading.Thread(target=work, daemon=True).start()
        self.root.after(5000, self.poll)

    def _restore_compose(self, text):
        if not self.compose.get("1.0", "end").strip():
            self.compose.insert("1.0", text)
            self.compose.focus_set()

    def _notice_confirmed(self, notice):
        if notice.get("label") in {"전송 중", "전송 실패"}:
            return False
        sent_ms = notice["at"] * 1000
        text = (notice.get("text") or "").strip()
        for message in self._thread_messages(notice["serial"], notice.get("address")):
            if message.get("incoming"):
                continue
            if notice.get("image"):
                if message.get("images") and abs(message["date"] - sent_ms) < 180000:
                    return True
            elif text and (message.get("body") or "").strip() == text and message["date"] >= sent_ms - 15000:
                return True
        return False

    def _shown_as_notice(self, serial, message):
        if message.get("incoming") or not message.get("images"):
            return False
        sent_ms = message["date"]
        for notice in self.sent_notices:
            if notice["serial"] != serial or not same_phone(notice["address"], message.get("address")):
                continue
            if abs(sent_ms - notice["at"] * 1000) < 180000:
                return True
        return False

    def _notice_pending(self, notice):
        sent_ms = notice["at"] * 1000
        for message in self._thread_messages(notice["serial"], notice.get("address")):
            if message.get("incoming") or not message.get("images"):
                continue
            if message["date"] >= sent_ms - 20000:
                return False
        return True

    def check_updates(self, manual=False):
        if os.environ.get("USBSMS_DEV") == "1" and not manual:
            return
        if self.update_check_running:
            return
        self.update_check_running = True

        def work():
            release, error = None, None
            try:
                from updater import latest_release
                release = latest_release()
            except Exception as exc:
                error = str(exc)
            self.root.after(0, lambda: self._finish_update_check(release, error, manual))

        threading.Thread(target=work, daemon=True).start()

    def _finish_update_check(self, release, error, manual):
        self.update_check_running = False
        if error:
            if manual:
                messagebox.showerror(APP_TITLE, f"업데이트 확인 실패: {error}")
            return
        if release is None:
            if manual:
                from version import APP_VERSION
                messagebox.showinfo(APP_TITLE, f"현재 버전 v{APP_VERSION}은 최신 공개 버전입니다.")
            return
        self._offer_update(release)

    def _offer_update(self, release):
        from version import APP_VERSION
        from updater import RELEASES_URL, prepare_update, start_helper
        if not messagebox.askyesno(
            APP_TITLE,
            f"현재 버전: v{APP_VERSION}\n새 버전: v{release['version']}\n\n"
            "지금 업데이트할까요? 다운로드와 검증 후 프로그램이 자동으로 재시작됩니다.\n"
            "대화 표시 설정은 유지됩니다.",
        ):
            return
        if not getattr(sys, "frozen", False):
            import webbrowser
            webbrowser.open(RELEASES_URL)
            return
        self.set_status("새 버전을 다운로드하고 검증하는 중...")

        def work():
            try:
                plan = prepare_update(release)
            except Exception as exc:
                self.root.after(0, lambda: messagebox.showerror(APP_TITLE, str(exc)))
                self.set_status("업데이트에 실패했습니다.")
                return
            start_helper(plan)
            self.root.after(0, self.root.destroy)
            os._exit(0)

        threading.Thread(target=work, daemon=True).start()

    def _unread_entries(self):
        entries = []
        for serial in self.devices:
            seen_map = self.config["seen"].get(serial, {})
            grouped = defaultdict(list)
            for message in self.messages.get(serial, []):
                if message.get("incoming"):
                    grouped[normalize_phone(message.get("address")) or "알 수 없음"].append(message)
            for address, items in grouped.items():
                seen_at = seen_map.get(address, 0)
                if not seen_at:
                    seen_at = seen_map.get(items[-1].get("address"), 0)
                unread_items = [item for item in items if item["date"] > seen_at]
                if not unread_items:
                    continue
                newest = max(unread_items, key=lambda item: item["date"])
                entries.append({
                    "serial": serial,
                    "address": address,
                    "count": len(unread_items),
                    "date": newest["date"],
                    "body": newest.get("body") or ("[이미지]" if newest.get("images") else ""),
                    "phone": self._phone_name(serial),
                })
        entries.sort(key=lambda item: item["date"], reverse=True)
        return entries

    def _refresh_notice_bar(self):
        entries = self._unread_entries()
        total = sum(item["count"] for item in entries)
        if not total:
            if self.notice_bar.winfo_ismapped():
                self.notice_bar.pack_forget()
            self.root.title(APP_TITLE)
            return
        first = entries[0]
        body = (first["body"] or "[이미지]").replace("\n", " ")[:42]
        self.notice_label.configure(
            text=f"새 메시지 {total}건     {first['phone']}  ·  {first['address']}  ·  {body}          클릭하면 그 대화로 이동"
        )
        if not self.notice_bar.winfo_ismapped():
            self.notice_bar.pack(fill="x", pady=(0, 8), before=self.panes)
        self.root.title(f"{APP_TITLE}  ·  새 메시지 {total}건")

    def _open_newest_unread(self):
        entries = self._unread_entries()
        if entries:
            self._open_arrival(entries[0]["serial"], entries[0]["address"])

    def _announce_arrivals(self, arrivals):
        self._play_alert_sound()
        self._flash_taskbar()
        self._show_arrival_popup(arrivals)
        self._refresh_notice_bar()

    def _play_alert_sound(self):
        def work():
            try:
                winsound.PlaySound("SystemExclamation", winsound.SND_ALIAS | winsound.SND_ASYNC)
                return
            except Exception:
                pass
            try:
                winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
            except Exception:
                pass
            try:
                winsound.Beep(880, 160)
                winsound.Beep(1175, 200)
            except Exception:
                pass

        threading.Thread(target=work, daemon=True).start()

    def _flash_taskbar(self):
        try:
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id()) or self.root.winfo_id()

            class FLASHWINFO(ctypes.Structure):
                _fields_ = [
                    ("cbSize", ctypes.c_uint),
                    ("hwnd", ctypes.c_void_p),
                    ("dwFlags", ctypes.c_uint),
                    ("uCount", ctypes.c_uint),
                    ("dwTimeout", ctypes.c_uint),
                ]

            info = FLASHWINFO(ctypes.sizeof(FLASHWINFO), hwnd, 0x3 | 0xC, 8, 0)
            ctypes.windll.user32.FlashWindowEx(ctypes.byref(info))
        except Exception:
            pass

    def _close_arrival_popup(self):
        popup = getattr(self, "_arrival_popup", None)
        self._arrival_popup = None
        self._arrival_popup_after = None
        if popup is None:
            return
        try:
            if popup.winfo_exists():
                popup.destroy()
        except tk.TclError:
            pass

    def _show_arrival_popup(self, arrivals):
        popup = getattr(self, "_arrival_popup", None)
        exists = False
        if popup is not None:
            try:
                exists = bool(popup.winfo_exists())
            except tk.TclError:
                exists = False
        if not exists:
            popup = tk.Toplevel(self.root)
            popup.title("새 메시지 도착")
            popup.configure(background="#FFF7ED")
            popup.attributes("-topmost", True)
            popup.resizable(False, False)
            popup.protocol("WM_DELETE_WINDOW", self._close_arrival_popup)
            popup.withdraw()
            self._arrival_popup = popup
        for child in popup.winfo_children():
            child.destroy()
        header = tk.Frame(popup, background="#C2410C")
        header.pack(fill="x")
        tk.Label(
            header, text=f"새 메시지 {len(arrivals)}건 도착", background="#C2410C", foreground="#FFFFFF",
            font=("맑은 고딕", 15, "bold"), anchor="w",
        ).pack(fill="x", padx=16, pady=12)
        body = tk.Frame(popup, background="#FFF7ED")
        body.pack(fill="both", padx=14, pady=10)
        for item in arrivals[:5]:
            address = item.get("address") or "번호 없음"
            preview = (item.get("body") or ("[이미지]" if item.get("images") else "(내용 없음)")).replace("\n", " ")
            if len(preview) > 90:
                preview = preview[:90] + "…"
            stamp = datetime.fromtimestamp(item["date"] / 1000).strftime("%H:%M") if item.get("date") else ""
            row = tk.Frame(body, background="#FFFFFF", highlightthickness=2, highlightbackground="#F97316", cursor="hand2")
            row.pack(fill="x", pady=4)
            title = tk.Label(
                row, text=f"{self._phone_name(item['serial'])}    {address}    {stamp}",
                background="#FFFFFF", foreground="#9A3412", font=("맑은 고딕", 9, "bold"),
                anchor="w", cursor="hand2",
            )
            title.pack(fill="x", padx=10, pady=(7, 0))
            text = tk.Label(
                row, text=preview, background="#FFFFFF", foreground="#1A1A1A",
                font=("맑은 고딕", 12), anchor="w", justify="left", wraplength=360, cursor="hand2",
            )
            text.pack(fill="x", padx=10, pady=(2, 8))
            serial, target = item["serial"], address
            for widget in (row, title, text):
                widget.bind("<Button-1>", lambda _event, s=serial, a=target: self._open_arrival(s, a))
        extra = len(arrivals) - 5
        if extra > 0:
            tk.Label(body, text=f"그 외 {extra}건", background="#FFF7ED", foreground="#9A3412", font=("맑은 고딕", 9)).pack(anchor="w", pady=(2, 0))
        buttons = tk.Frame(popup, background="#FFF7ED")
        buttons.pack(fill="x", padx=14, pady=(2, 14))
        first = arrivals[0]
        tk.Button(
            buttons, text="대화 보기",
            command=lambda s=first["serial"], a=first.get("address") or "": self._open_arrival(s, a),
            background="#C2410C", foreground="#FFFFFF", activebackground="#9A3412", activeforeground="#FFFFFF",
            font=("맑은 고딕", 10, "bold"), relief="flat", padx=14, pady=5,
        ).pack(side="left")
        tk.Button(
            buttons, text="닫기", command=self._close_arrival_popup,
            font=("맑은 고딕", 10), padx=14, pady=5,
        ).pack(side="right")
        popup.update_idletasks()
        width = 430
        height = max(popup.winfo_reqheight(), 180)
        popup.geometry(f"{width}x{height}+{popup.winfo_screenwidth() - width - 28}+{popup.winfo_screenheight() - height - 78}")
        self._show_without_focus(popup)
        if self._arrival_popup_after:
            try:
                popup.after_cancel(self._arrival_popup_after)
            except tk.TclError:
                pass
        self._arrival_popup_after = popup.after(25000, self._close_arrival_popup)

    def _show_without_focus(self, popup):
        popup.update_idletasks()
        try:
            hwnd = ctypes.windll.user32.GetParent(popup.winfo_id()) or popup.winfo_id()
            popup.attributes("-topmost", True)
            ctypes.windll.user32.ShowWindow(hwnd, 8)
        except Exception:
            popup.deiconify()
            popup.lift()
            popup.attributes("-topmost", True)

    def _open_arrival(self, serial, address):
        self._close_arrival_popup()
        try:
            self.root.deiconify()
            self.root.lift()
            self.root.focus_force()
        except tk.TclError:
            pass
        norm = normalize_phone(address)
        if serial in self.devices and serial != self.active_serial:
            if self.device_tree.exists(serial):
                self.device_tree.selection_set(serial)
            self.select_device(serial)
        self.active_address = norm
        self.thread_search.set("")
        self.fresh_marks = {mark for mark in self.fresh_marks if not (mark[0] == serial and mark[1] == norm)}
        self.render_threads()
        if self.thread_tree.exists(norm):
            self.thread_tree.selection_set(norm)
            self.thread_tree.see(norm)
        else:
            self.render_chat()
            self._refresh_notice_bar()

    def set_status(self, text, hold=0):
        if hold:
            self.status_hold_until = time.time() + hold
        def apply(message=text, pinned=hold):
            if not pinned and time.time() < self.status_hold_until:
                return
            self.status.set(message)
        self.root.after(0, apply)


if __name__ == "__main__":
    if "--apply-update" in sys.argv:
        from updater import apply_update
        try:
            apply_update(Path(sys.argv[sys.argv.index("--apply-update") + 1]))
        except Exception as exc:
            import ctypes
            ctypes.windll.user32.MessageBoxW(0, str(exc), "USB 문자 관리 업데이트 실패", 0x10)
            raise SystemExit(1)
    else:
        root = tk.Tk()
        try:
            ttk.Style().theme_use("vista")
        except tk.TclError:
            pass
        SmsManagerApp(root)
        root.mainloop()
