#!/usr/bin/env python3
"""
Sharp Copier Toner Monitor
--------------------------
Native desktop UI (tkinter) that polls Sharp copiers/MFPs over SNMP and shows
toner levels. Add each copier by IP address. No third-party packages needed.

Requirements on the copier:
  * SNMP enabled (Sharp web UI: System Settings > Network Settings > Services
    > SNMP) with SNMP v1/v2c readable, usually community "public".
  * UDP port 161 reachable from this computer.

Data comes from the standard Printer-MIB (RFC 3805) supplies table, so it also
works with most other brands.
"""

import ipaddress
import json
import queue
import random
import re
import socket
import threading
import time
import tkinter as tk
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tkinter import messagebox, ttk

CONFIG_FILE = Path.home() / ".sharp_toner_monitor.json"
LOW_THRESHOLD = 10          # percent at/below which a row is flagged
AUTO_REFRESH_MS = 5 * 60 * 1000
SNMP_TIMEOUT = 2.0
SNMP_RETRIES = 1

# --------------------------------------------------------------------------
# Minimal SNMPv2c client (GETNEXT only) using BER encoding from the stdlib
# --------------------------------------------------------------------------

END = object()  # marker: endOfMibView / noSuchObject / noSuchInstance


def _len(n):
    if n < 0x80:
        return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(b)]) + b


def _tlv(tag, content):
    return bytes([tag]) + _len(len(content)) + content


def _enc_int(v):
    n = max(1, (v.bit_length() + 8) // 8)
    return _tlv(0x02, v.to_bytes(n, "big", signed=True))


def _enc_oid(oid):
    parts = [int(p) for p in oid.strip(".").split(".")]
    body = bytearray([40 * parts[0] + parts[1]])
    for p in parts[2:]:
        chunk = [p & 0x7F]
        p >>= 7
        while p:
            chunk.append(0x80 | (p & 0x7F))
            p >>= 7
        body.extend(reversed(chunk))
    return _tlv(0x06, bytes(body))


def _read_tlv(data, pos):
    tag = data[pos]
    length = data[pos + 1]
    pos += 2
    if length & 0x80:
        n = length & 0x7F
        length = int.from_bytes(data[pos:pos + n], "big")
        pos += n
    return tag, data[pos:pos + length], pos + length


def _dec_oid(content):
    first = content[0]
    parts = [first // 40, first % 40] if first < 80 else [2, first - 80]
    val = 0
    for b in content[1:]:
        val = (val << 7) | (b & 0x7F)
        if not b & 0x80:
            parts.append(val)
            val = 0
    return ".".join(map(str, parts))


def _dec_value(tag, c):
    if tag == 0x02:
        return int.from_bytes(c, "big", signed=True) if c else 0
    if tag in (0x41, 0x42, 0x43, 0x46):      # counter32/gauge32/timeticks/counter64
        return int.from_bytes(c, "big")
    if tag == 0x04:
        return c.decode("utf-8", "replace").strip("\x00").strip()
    if tag == 0x06:
        return _dec_oid(c)
    if tag in (0x80, 0x81, 0x82):
        return END
    return c


def snmp_get_next(sock, ip, community, oid):
    """Send one GETNEXT and return (next_oid, value)."""
    req_id = random.randint(1, 0x7FFFFFFF)
    varbind = _tlv(0x30, _enc_oid(oid) + b"\x05\x00")
    pdu = _tlv(0xA1, _enc_int(req_id) + _enc_int(0) + _enc_int(0) + _tlv(0x30, varbind))
    msg = _tlv(0x30, _enc_int(1) + _tlv(0x04, community.encode()) + pdu)

    last_err = socket.timeout("no response (check IP, SNMP enabled, community string)")
    for _ in range(SNMP_RETRIES + 1):
        sock.sendto(msg, (ip, 161))
        try:
            while True:
                data, _addr = sock.recvfrom(65535)
                _, body, _ = _read_tlv(data, 0)
                _, _, p = _read_tlv(body, 0)            # version
                _, _, p = _read_tlv(body, p)            # community
                _, pdu_body, _ = _read_tlv(body, p)     # response PDU
                _, rid, p = _read_tlv(pdu_body, 0)
                if int.from_bytes(rid, "big") != req_id:
                    continue                            # stale reply, keep waiting
                _, err, p = _read_tlv(pdu_body, p)
                _, _, p = _read_tlv(pdu_body, p)        # error index
                if int.from_bytes(err, "big") != 0:
                    return oid, END
                _, vbs, _ = _read_tlv(pdu_body, p)
                _, vb, _ = _read_tlv(vbs, 0)
                _, oid_c, p = _read_tlv(vb, 0)
                vtag, vcontent, _ = _read_tlv(vb, p)
                return _dec_oid(oid_c), _dec_value(vtag, vcontent)
        except socket.timeout:
            continue
    raise last_err


def snmp_walk(sock, ip, community, base):
    out, oid = {}, base
    for _ in range(500):
        nxt, val = snmp_get_next(sock, ip, community, oid)
        if val is END or not nxt.startswith(base + ".") or nxt == oid:
            break
        out[nxt] = val
        oid = nxt
    return out


# --------------------------------------------------------------------------
# Printer-MIB logic
# --------------------------------------------------------------------------

SUPPLIES = "1.3.6.1.2.1.43.11.1.1"
COL_TYPE, COL_DESC, COL_MAX, COL_LEVEL = 5, 6, 8, 9
SUPPLY_TYPE_TONER, SUPPLY_TYPE_WASTE = 3, 4

COLOR_PATTERNS = [
    ("K", re.compile(r"black|\bbk\b|\bk\b", re.I)),
    ("C", re.compile(r"cyan|\bc\b", re.I)),
    ("M", re.compile(r"magenta|\bm\b", re.I)),
    ("Y", re.compile(r"yellow|\by\b", re.I)),
]


def level_to_pct(level, maximum):
    """Return (percent or None, display string)."""
    if level is None:
        return None, "?"
    if level == -3:
        return None, "OK"          # "some remaining", not measurable
    if level < 0:
        return None, "?"
    pct = round(level * 100 / maximum) if maximum and maximum > 0 else level
    return max(0, min(100, pct)), f"{max(0, min(100, pct))}%"


def fetch_copier(ip, community):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(SNMP_TIMEOUT)
    try:
        _, model = snmp_get_next(sock, ip, community, "1.3.6.1.2.1.1.1")   # sysDescr.0
        cols = {c: snmp_walk(sock, ip, community, f"{SUPPLIES}.{c}")
                for c in (COL_TYPE, COL_DESC, COL_MAX, COL_LEVEL)}
    finally:
        sock.close()

    supplies = []
    for oid, desc in cols[COL_DESC].items():
        idx = oid.rsplit(".", 2)[-2:]          # hrDeviceIndex.supplyIndex
        key = lambda col: f"{SUPPLIES}.{col}.{idx[0]}.{idx[1]}"
        stype = cols[COL_TYPE].get(key(COL_TYPE))
        pct, text = level_to_pct(cols[COL_LEVEL].get(key(COL_LEVEL)),
                                 cols[COL_MAX].get(key(COL_MAX)))
        is_waste = stype == SUPPLY_TYPE_WASTE or "waste" in desc.lower()
        is_toner = stype == SUPPLY_TYPE_TONER or "toner" in desc.lower()
        color = None
        if is_toner and not is_waste:
            for code, pat in COLOR_PATTERNS:
                if pat.search(desc):
                    color = code
                    break
        supplies.append({"desc": desc, "pct": pct, "text": text,
                         "waste": is_waste, "toner": is_toner, "color": color})
    if not supplies:
        raise RuntimeError("Device answered but reports no supplies")
    return {"model": model if isinstance(model, str) else "", "supplies": supplies,
            "time": time.strftime("%H:%M:%S")}


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------

class App(tk.Tk):
    COLUMNS = (("name", "Copier", 150), ("ip", "IP Address", 110),
               ("model", "Model", 190), ("K", "Black", 65), ("C", "Cyan", 65),
               ("M", "Magenta", 70), ("Y", "Yellow", 65), ("waste", "Waste", 65),
               ("status", "Status", 170))

    def __init__(self):
        super().__init__()
        self.title("Sharp Toner Monitor")
        self.geometry("1050x420")
        self.minsize(800, 300)

        self.copiers = self._load()
        self.results = {}
        self.q = queue.Queue()
        self.pool = ThreadPoolExecutor(max_workers=8)
        self.auto_var = tk.BooleanVar(value=False)
        self._auto_job = None

        self._build_ui()
        for c in self.copiers:
            self._insert_row(c)
        self.after(100, self._poll_queue)
        if self.copiers:
            self.refresh_all()

    # ---- persistence ----
    def _load(self):
        try:
            return json.loads(CONFIG_FILE.read_text())
        except Exception:
            return []

    def _save(self):
        try:
            CONFIG_FILE.write_text(json.dumps(self.copiers, indent=2))
        except OSError as e:
            messagebox.showwarning("Save failed", str(e))

    # ---- layout ----
    def _build_ui(self):
        add = ttk.LabelFrame(self, text="Add copier", padding=8)
        add.pack(fill="x", padx=10, pady=(10, 4))
        self.ip_var, self.name_var = tk.StringVar(), tk.StringVar()
        self.comm_var = tk.StringVar(value="public")

        ttk.Label(add, text="IP address").grid(row=0, column=0, sticky="w")
        ip_entry = ttk.Entry(add, textvariable=self.ip_var, width=18)
        ip_entry.grid(row=1, column=0, padx=(0, 8))
        ttk.Label(add, text="Name (optional)").grid(row=0, column=1, sticky="w")
        ttk.Entry(add, textvariable=self.name_var, width=24).grid(row=1, column=1, padx=(0, 8))
        ttk.Label(add, text="SNMP community").grid(row=0, column=2, sticky="w")
        ttk.Entry(add, textvariable=self.comm_var, width=16).grid(row=1, column=2, padx=(0, 8))
        ttk.Button(add, text="Add", command=self.add_copier).grid(row=1, column=3)
        ip_entry.bind("<Return>", lambda e: self.add_copier())
        ip_entry.focus_set()

        bar = ttk.Frame(self, padding=(10, 4))
        bar.pack(fill="x")
        ttk.Button(bar, text="Refresh all", command=self.refresh_all).pack(side="left")
        ttk.Button(bar, text="Remove selected", command=self.remove_selected).pack(side="left", padx=6)
        ttk.Checkbutton(bar, text="Auto-refresh every 5 min", variable=self.auto_var,
                        command=self._toggle_auto).pack(side="left", padx=10)
        ttk.Label(bar, text="Double-click a row for all supplies").pack(side="right")

        frame = ttk.Frame(self)
        frame.pack(fill="both", expand=True, padx=10, pady=(0, 6))
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in self.COLUMNS],
                                 show="headings", selectmode="browse")
        for key, title, width in self.COLUMNS:
            self.tree.heading(key, text=title)
            self.tree.column(key, width=width, anchor="center" if key in "KCMY" or key == "waste" else "w")
        sb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.tag_configure("low", background="#ffd6d6")
        self.tree.tag_configure("error", foreground="#888888")
        self.tree.bind("<Delete>", lambda e: self.remove_selected())
        self.tree.bind("<Double-1>", self.show_details)

        self.status = tk.StringVar(value="Ready")
        ttk.Label(self, textvariable=self.status, relief="sunken", anchor="w",
                  padding=(6, 2)).pack(fill="x", side="bottom")

    # ---- actions ----
    def add_copier(self):
        ip = self.ip_var.get().strip()
        try:
            ipaddress.ip_address(ip)
        except ValueError:
            messagebox.showerror("Invalid IP", f"'{ip}' is not a valid IP address.")
            return
        if any(c["ip"] == ip for c in self.copiers):
            messagebox.showinfo("Already added", f"{ip} is already in the list.")
            return
        copier = {"ip": ip, "name": self.name_var.get().strip() or ip,
                  "community": self.comm_var.get().strip() or "public"}
        self.copiers.append(copier)
        self._save()
        self._insert_row(copier)
        self.ip_var.set("")
        self.name_var.set("")
        self._refresh_one(copier)

    def remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        ip = sel[0]
        self.copiers = [c for c in self.copiers if c["ip"] != ip]
        self.results.pop(ip, None)
        self.tree.delete(ip)
        self._save()

    def refresh_all(self):
        for c in self.copiers:
            self._refresh_one(c)

    def _refresh_one(self, copier):
        self.tree.set(copier["ip"], "status", "Querying...")
        self.pool.submit(self._worker, copier["ip"], copier["community"])

    def _worker(self, ip, community):
        try:
            res = fetch_copier(ip, community)
        except Exception as e:  # network errors, parse errors, timeouts
            res = {"error": str(e) or e.__class__.__name__}
        self.q.put((ip, res))

    def _poll_queue(self):
        try:
            while True:
                ip, res = self.q.get_nowait()
                if self.tree.exists(ip):
                    self.results[ip] = res
                    self._update_row(ip)
        except queue.Empty:
            pass
        self.after(100, self._poll_queue)

    def _toggle_auto(self):
        if self._auto_job:
            self.after_cancel(self._auto_job)
            self._auto_job = None
        if self.auto_var.get():
            self._auto_tick()

    def _auto_tick(self):
        self.refresh_all()
        self._auto_job = self.after(AUTO_REFRESH_MS, self._auto_tick)

    # ---- table rendering ----
    def _insert_row(self, copier):
        self.tree.insert("", "end", iid=copier["ip"],
                         values=(copier["name"], copier["ip"], "", "", "", "", "", "", "Waiting..."))

    def _update_row(self, ip):
        res = self.results[ip]
        copier = next(c for c in self.copiers if c["ip"] == ip)
        if "error" in res:
            self.tree.item(ip, values=(copier["name"], ip, "", "-", "-", "-", "-", "-",
                                       f"Error: {res['error']}"), tags=("error",))
            self.status.set(f"{ip}: {res['error']}")
            return

        cells = {"K": "-", "C": "-", "M": "-", "Y": "-", "waste": "-"}
        low = False
        extra = []
        for s in res["supplies"]:
            if s["waste"]:
                cells["waste"] = s["text"]
            elif s["color"]:
                warn = s["pct"] is not None and s["pct"] <= LOW_THRESHOLD
                low = low or warn
                cells[s["color"]] = s["text"] + (" \u26a0" if warn else "")
            elif s["toner"]:
                warn = s["pct"] is not None and s["pct"] <= LOW_THRESHOLD
                low = low or warn
                extra.append(s)
        # Mono machines often report a single toner with an unrecognised name
        if extra and cells["K"] == "-":
            cells["K"] = extra[0]["text"] + (" \u26a0" if extra[0]["pct"] is not None
                                             and extra[0]["pct"] <= LOW_THRESHOLD else "")
        model = " ".join(res["model"].split())[:40]
        self.tree.item(ip, values=(copier["name"], ip, model, cells["K"], cells["C"],
                                   cells["M"], cells["Y"], cells["waste"],
                                   ("LOW TONER  " if low else "OK  ") + f"({res['time']})"),
                       tags=("low",) if low else ())
        self.status.set(f"Updated {ip} at {res['time']}")

    def show_details(self, _event):
        sel = self.tree.selection()
        if not sel or sel[0] not in self.results:
            return
        res = self.results[sel[0]]
        if "error" in res:
            messagebox.showerror(sel[0], res["error"])
            return
        lines = [f"{s['desc']}: {s['text']}" for s in res["supplies"]]
        messagebox.showinfo(f"{sel[0]} - supplies", "\n".join(lines))


if __name__ == "__main__":
    App().mainloop()
