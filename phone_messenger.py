import base64
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
        self.polling = False
        self.suppress_selection = False
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

    def _build(self):
        outer = ttk.Frame(self.root, padding=10)
        outer.pack(fill="both", expand=True)
        top = ttk.Frame(outer)
        top.pack(fill="x", pady=(0, 8))
        ttk.Label(top, text=APP_TITLE, font=("맑은 고딕", 17, "bold")).pack(side="left")
        ttk.Button(top, text="업데이트 확인", command=lambda: self.check_updates(manual=True)).pack(side="right")
        ttk.Button(top, text="브리지 앱 설치/업데이트", command=self.install_bridge).pack(side="right", padx=(0, 6))
        ttk.Button(top, text="새로고침", command=self.refresh_devices).pack(side="right", padx=6)

        panes = ttk.Panedwindow(outer, orient="horizontal")
        panes.pack(fill="both", expand=True)
        device_box = ttk.LabelFrame(panes, text="연결된 스마트폰", padding=6)
        thread_box = ttk.LabelFrame(panes, text="대화 목록", padding=6)
        chat_box = ttk.Frame(panes)
        panes.add(device_box, weight=1)
        panes.add(thread_box, weight=2)
        panes.add(chat_box, weight=5)

        device_list = ttk.Frame(device_box)
        device_list.pack(fill="both", expand=True)
        self.device_tree = ttk.Treeview(device_list, columns=("state",), show="tree", selectmode="browse")
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
        self.thread_tree = ttk.Treeview(thread_list, columns=("preview", "phone"), show="tree headings", selectmode="browse")
        self.thread_tree.heading("#0", text="번호")
        self.thread_tree.heading("preview", text="최근 내용")
        self.thread_tree.heading("phone", text="스마트폰")
        self.thread_tree.column("#0", width=120, stretch=False)
        self.thread_tree.column("preview", width=150, stretch=True)
        self.thread_tree.column("phone", width=72, anchor="center", stretch=False)
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

    def _refresh_worker(self):
        result = self.adb_run(None, "devices", "-l")
        found = []
        for line in result.stdout.splitlines()[1:]:
            p = line.split()
            if len(p) >= 2 and p[1] == "device":
                found.append((p[0], next((x.split(":", 1)[1] for x in p if x.startswith("model:")), p[0])))
        devices = {}
        for i, (serial, model) in enumerate(found):
            port = 18765 + i
            status = self.ensure_bridge(serial, port)
            devices[serial] = {"model": model, "port": port, "online": bool(status and status.get("ok"))}
            if devices[serial]["online"]:
                self.messages[serial] = self.collect_messages(serial, port)
                if serial not in self.config["initialized"]:
                    seen = self.config["seen"].setdefault(serial, {})
                    for message in self.messages[serial]:
                        if message.get("incoming"):
                            seen[normalize_phone(message.get("address"))] = max(
                                seen.get(normalize_phone(message.get("address")), 0), message["date"]
                            )
                    self.config["initialized"].append(serial)
                    self.save_config()
        self.devices = devices
        self.root.after(0, self.render_all)
        self.set_status(f"연결된 스마트폰 {len(devices)}대")

    def collect_messages(self, serial, port):
        messages = []
        data = self.api(port, "/messages", quiet=True)
        if data and data.get("ok"):
            messages.extend(data["messages"])
        messages.extend(self.fetch_im_messages(serial))
        messages.extend(self.fetch_im_files(serial))
        messages.sort(key=lambda item: item.get("date") or 0)
        return messages

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
        if self.devices and not self.message_sync_running:
            self.message_sync_running = True
            threading.Thread(target=self._sync_messages, daemon=True).start()
        self.root.after(2000, self.poll_messages)

    def _sync_messages(self):
        try:
            changed = False
            for serial, device in list(self.devices.items()):
                if not device.get("online"):
                    continue
                messages = self.collect_messages(serial, device["port"])
                old_keys = [item.get("key") for item in self.messages.get(serial, [])]
                new_keys = [item.get("key") for item in messages]
                if old_keys != new_keys:
                    self.messages[serial] = messages
                    changed = True
            if changed:
                self.root.after(0, self.render_all)
        finally:
            self.message_sync_running = False

    def render_all(self):
        self.render_devices()
        if self.active_serial in self.devices:
            self.render_threads()
            if self.active_address:
                self.render_chat()

    def unread_for(self, serial, address=None):
        seen_map = self.config["seen"].get(serial, {})
        count = 0
        target = normalize_phone(address) if address else None
        for message in self.messages.get(serial, []):
            if not message.get("incoming"):
                continue
            norm = normalize_phone(message.get("address"))
            if target is not None and norm != target:
                continue
            if message["date"] > seen_map.get(norm, seen_map.get(message.get("address"), 0)):
                count += 1
        return count

    def render_devices(self):
        selected = self.active_serial
        self.suppress_selection = True
        self.device_tree.delete(*self.device_tree.get_children())
        self.device_rows.clear()
        for serial, d in self.devices.items():
            name = self.config["names"].get(serial, d["model"])
            unread = self.unread_for(serial)
            suffix = f"  +{unread}" if unread else ""
            state = "연결됨" if d["online"] else "브리지 실행 필요"
            self.device_rows[serial] = self.device_tree.insert("", "end", iid=serial, text=f"{name}{suffix}", values=(state,))
        if selected in self.devices:
            self.device_tree.selection_set(selected)
        elif self.devices:
            first = next(iter(self.devices))
            self.device_tree.selection_set(first)
            self.select_device(first)
        self.suppress_selection = False

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
            self.messages[serial] = self.collect_messages(serial, device["port"])
            self.root.after(0, self.render_all)
            self.set_status(f"{device['model']} 연결됨")
        else:
            self.set_status("브리지를 시작하지 못했습니다. 휴대폰에서 문자 권한을 허용해 주세요.")

    def render_threads(self):
        selected = self.active_address
        query = self.thread_search.get().strip().lower()
        self.suppress_selection = True
        self.thread_tree.delete(*self.thread_tree.get_children())
        groups = defaultdict(list)
        for m in self.messages.get(self.active_serial, []):
            groups[normalize_phone(m.get("address")) or "알 수 없음"].append(m)
        selected_norm = normalize_phone(selected) if selected else ""
        for address, items in sorted(groups.items(), key=lambda x: x[1][-1]["date"], reverse=True):
            searchable = address + "\n" + "\n".join((item.get("body") or "") for item in items)
            if query and query not in searchable.lower():
                continue
            latest = items[-1]
            preview = latest.get("body") or ("[이미지]" if latest.get("images") else "")
            matched = [notice.get("label", "이미지 전송됨") for notice in self.sent_notices if same_phone(notice["address"], address)]
            if matched:
                preview = matched[-1]
            unread = self.unread_for(self.active_serial, address)
            label = f"{address}  +{unread}" if unread else address
            self.thread_tree.insert("", "end", iid=address, text=label, values=(preview.replace("\n", " ")[:35], "열기"))
        if selected_norm and selected_norm not in groups and (not query or query in selected_norm.lower()):
            self.thread_tree.insert("", 0, iid=selected_norm, text=selected_norm, values=("[새 메시지]", "열기"))
        if selected_norm and self.thread_tree.exists(selected_norm):
            self.thread_tree.selection_set(selected_norm)
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
        if self.suppress_selection:
            return
        selected = self.thread_tree.selection()
        if not selected:
            return
        self.active_address = selected[0]
        items = [m for m in self.messages.get(self.active_serial, []) if same_phone(m.get("address"), self.active_address)]
        if items:
            self.config["seen"].setdefault(self.active_serial, {})[normalize_phone(self.active_address)] = max(m["date"] for m in items)
            self.save_config()
        self.update_unread_labels()
        self.render_chat()

    def on_thread_shortcut(self, event):
        if self.thread_tree.identify_column(event.x) != "#2":
            return
        row = self.thread_tree.identify_row(event.y)
        if row:
            self.open_phone_conversation(row)

    def open_phone_conversation(self, address):
        serial = self.active_serial
        number = re.sub(r"[^0-9+]", "", address or "")
        if not serial or not number:
            self.set_status("스마트폰에서 열 대화를 찾지 못했습니다.")
            return

        def work():
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
                self.device_tree.item(serial, text=f"{name}  +{unread}" if unread else name)
        for address in self.thread_tree.get_children():
            unread = self.unread_for(self.active_serial, address)
            self.thread_tree.item(address, text=f"{address}  +{unread}" if unread else address)

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
        self.chat_title.set("대화를 선택하세요")
        self._rendered_address = None
        for child in self.chat_inner.winfo_children():
            child.destroy()
        self.image_refs.clear()

    def render_chat(self):
        serial, address = self.active_serial, self.active_address
        if not serial or not address:
            return
        self.chat_title.set(f"{address}  ·  {self.config['names'].get(serial, self.devices[serial]['model'])}")
        items = [m for m in self.messages.get(serial, []) if same_phone(m.get("address"), address) and not self._shown_as_notice(serial, m)]
        for notice in self.sent_notices:
            if notice["serial"] == serial and same_phone(notice["address"], address):
                items.append({
                    "incoming": False,
                    "date": int(notice["at"] * 1000),
                    "body": notice.get("text") or "",
                    "local_image": notice.get("image"),
                    "sent_label": notice.get("label", "이미지 전송됨"),
                })
        items.sort(key=lambda item: item["date"])
        thread_key = (serial, normalize_phone(address))
        same_thread = getattr(self, "_rendered_address", None) == thread_key
        view = self.chat_canvas.yview() if same_thread else (0.0, 1.0)
        stick = (not same_thread) or view[1] >= 0.985
        self._rendered_address = thread_key
        for child in self.chat_inner.winfo_children():
            child.destroy()
        self.image_refs.clear()
        if not items:
            tk.Label(
                self.chat_inner, text="이 번호와 주고받은 문자가 없습니다.",
                background=CHAT_BG, foreground=META_IN, font=("맑은 고딕", 11),
            ).pack(pady=24)
        last_day = None
        width = max(self.chat_canvas.winfo_width(), 420)
        wrap = max(220, min(360, int(width * 0.62)))
        for message in items:
            stamp = datetime.fromtimestamp(message["date"] / 1000)
            day = stamp.strftime("%Y년 %m월 %d일")
            if day != last_day:
                last_day = day
                tk.Label(
                    self.chat_inner, text=day, background="#D5DEE8", foreground="#243140",
                    font=("맑은 고딕", 8), padx=10, pady=3,
                ).pack(pady=(12, 4))
            self._add_message_bubble(message, serial, stamp.strftime("%H:%M"), wrap)
        self._prefetch_recent_images(serial, items)
        self.chat_inner.update_idletasks()
        self._sync_chat_scroll()
        if stick:
            self.chat_canvas.yview_moveto(1)
        else:
            self.chat_canvas.yview_moveto(view[0])

    def _add_message_bubble(self, message, serial, clock, wrap):
        incoming = bool(message.get("incoming"))
        failed = message.get("sent_label") == "전송 실패"
        bubble_bg = BUBBLE_IN if incoming else (BUBBLE_FAIL if failed else BUBBLE_OUT)
        text_color = TEXT_IN if incoming else TEXT_OUT
        hint_color = "#5C6B7A" if incoming else "#D6E4FF"
        who = "상대 · 받음" if incoming else "나 · 보냄"
        who_color = META_IN if incoming else META_OUT
        row = tk.Frame(self.chat_inner, background=CHAT_BG)
        row.pack(fill="x", padx=12, pady=3)
        holder = tk.Frame(row, background=CHAT_BG)
        holder.pack(side="left" if incoming else "right", anchor="w" if incoming else "e")
        tk.Label(
            holder, text=f"{who}   {clock}", background=CHAT_BG, foreground=who_color,
            font=("맑은 고딕", 8, "bold"),
        ).pack(anchor="w" if incoming else "e", padx=4)
        bubble = tk.Frame(
            holder, background=bubble_bg, padx=10, pady=8,
            highlightthickness=1 if incoming else 0, highlightbackground="#C5D0DC",
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
            self._add_bubble_image(bubble, raw, filename, bubble_bg)
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

    def _add_bubble_image(self, parent, raw, filename, background):
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
        self.image_refs.append(photo)

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
        notice = None
        if self.attachment:
            notice = {
                "serial": self.active_serial,
                "address": self.active_address,
                "image": self.attachment.read_bytes(),
                "text": text,
                "at": time.time(),
                "label": "전송 중",
            }
            self.sent_notices.append(notice)
            self.render_chat()
            self.set_status("이미지를 전송하는 중...")
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
            notice["label"] = "이미지 전송됨" if result and result.get("direct") else "전송 실패"
            self.root.after(0, self.render_chat)
            self.root.after(0, self.render_threads)
        if result and result.get("ok"):
            self.root.after(0, lambda: self.compose.delete("1.0", "end"))
            self.root.after(0, self.clear_attachment)
            if notice is not None and result.get("direct"):
                self.set_status("이미지를 전송했습니다.", hold=30)
            elif notice is not None:
                self.set_status(result.get("note", "이미지 전송에 실패했습니다."), hold=15)
            else:
                self.set_status(result.get("note", "메시지를 발송했습니다."))
            self._refresh_worker()
            if notice is not None and result.get("direct"):
                self.set_status("이미지를 전송했습니다.", hold=30)

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
                    self._refresh_worker()
                finally:
                    self.polling = False
            threading.Thread(target=work, daemon=True).start()
        self.root.after(5000, self.poll)

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
        for message in self.messages.get(notice["serial"], []):
            if message.get("incoming") or not message.get("images"):
                continue
            if not same_phone(message.get("address"), notice["address"]):
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
