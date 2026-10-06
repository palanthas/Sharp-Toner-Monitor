#!/usr/bin/env python3
"""
Sharp Copier Toner Monitor + Toner Inventory
--------------------------------------------
Native desktop UI (tkinter), no third-party packages needed.

Tab 1 "Copiers":   add copiers by IP, poll toner levels over SNMP, and assign
                   the toner / waste-collector part numbers each machine uses.
Tab 2 "Inventory": toner stock on hand per part number, with add/remove.
                   Every machine currently marked low counts against stock, so
                   you can see at a glance whether you have enough spares.

Requirements on the copier:
  * SNMP enabled (Sharp web UI: System Settings > Network Settings > Services
    > SNMP) with SNMP v1/v2c readable, usually community "public".
  * UDP port 161 reachable from this computer.
"""

import ipaddress
import json
import queue
import random
import re
import socket
import time
import tkinter as tk
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tkinter import messagebox, ttk

CONFIG_FILE = Path.home() / ".sharp_toner_monitor.json"
LOW_THRESHOLD = 10          # toner counts as low at/below this % remaining
WASTE_FULL_THRESHOLD = 190   # waste collector counts as full at/above this % full
DEFAULT_MIN_STOCK = 1       # minimum spares to keep for any part without its own
                            # minimum (set per part on the Inventory tab)
AUTO_REFRESH_MS = 5 * 60 * 1000
SNMP_TIMEOUT = 2.0
SNMP_RETRIES = 1

# Slots a copier can have a part number for: (key, column header)
SLOTS = (("K", "Black"), ("C", "Cyan"), ("M", "Magenta"), ("Y", "Yellow"),
         ("waste", "Waste collector"))


def slot_type_label(slot, header):
    return header if slot == "waste" else f"{header} toner"


def norm_part(text):
    return (text or "").strip().upper()


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
COL_CLASS, COL_TYPE, COL_DESC, COL_MAX, COL_LEVEL = 4, 5, 6, 8, 9
SUPPLY_TYPE_TONER, SUPPLY_TYPE_WASTE = 3, 4
SUPPLY_CLASS_CONSUMED = 3       # level = amount remaining
SUPPLY_CLASS_RECEPTACLE = 4     # level = amount filled (e.g. waste toner box)

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
    pct = max(0, min(100, pct))
    return pct, f"{pct}%"


def fetch_copier(ip, community):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(SNMP_TIMEOUT)
    try:
        _, model = snmp_get_next(sock, ip, community, "1.3.6.1.2.1.1.1")   # sysDescr.0
        cols = {c: snmp_walk(sock, ip, community, f"{SUPPLIES}.{c}")
                for c in (COL_CLASS, COL_TYPE, COL_DESC, COL_MAX, COL_LEVEL)}
    finally:
        sock.close()

    supplies = []
    for oid, desc in cols[COL_DESC].items():
        idx = oid.rsplit(".", 2)[-2:]          # hrDeviceIndex.supplyIndex

        def get(col):
            return cols[col].get(f"{SUPPLIES}.{col}.{idx[0]}.{idx[1]}")

        stype, klass = get(COL_TYPE), get(COL_CLASS)
        pct, text = level_to_pct(get(COL_LEVEL), get(COL_MAX))
        is_waste = stype == SUPPLY_TYPE_WASTE or "waste" in desc.lower()
        is_toner = stype == SUPPLY_TYPE_TONER or "toner" in desc.lower()

        # Waste collectors normally report how FULL they are (class 4).
        fills = is_waste and klass != SUPPLY_CLASS_CONSUMED
        if fills and pct is not None:
            text = f"{pct}% full"
        low = pct is not None and (pct >= WASTE_FULL_THRESHOLD if fills else pct <= LOW_THRESHOLD)

        slot = None
        if is_waste:
            slot = "waste"
        elif is_toner:
            for code, pat in COLOR_PATTERNS:
                if pat.search(desc):
                    slot = code
                    break
        supplies.append({"desc": desc, "pct": pct, "text": text, "low": low,
                         "waste": is_waste, "toner": is_toner, "fills": fills,
                         "slot": slot})

    # Mono machines often name their single toner something unrecognisable
    if not any(s["slot"] == "K" for s in supplies):
        for s in supplies:
            if s["toner"] and not s["waste"] and s["slot"] is None:
                s["slot"] = "K"
                break

    slots = {}
    for s in supplies:
        if s["slot"] and s["slot"] not in slots:
            slots[s["slot"]] = {"pct": s["pct"], "text": s["text"], "low": s["low"]}
    if not supplies:
        raise RuntimeError("Device answered but reports no supplies")
    return {"model": model if isinstance(model, str) else "", "supplies": supplies,
            "slots": slots, "time": time.strftime("%H:%M:%S")}


# --------------------------------------------------------------------------
# Inventory logic (pure functions, no GUI)
# --------------------------------------------------------------------------

def inventory_rows(copiers, results, stock, minimums=None):
    """
    Combine copier part assignments, latest readings, and stock on hand.
    Every machine whose toner/waste collector is currently low counts as one
    unit needed from stock. The result is compared with each part's minimum
    (from `minimums`, else DEFAULT_MIN_STOCK). Returns one dict per part number.
    """
    minimums = minimums or {}
    machines, low, types, low_by = Counter(), Counter(), {}, {}
    for c in copiers:
        res = results.get(c["ip"])
        for slot, header in SLOTS:
            part = norm_part((c.get("parts") or {}).get(slot))
            if not part:
                continue
            machines[part] += 1
            label = slot_type_label(slot, header)
            if label not in types.setdefault(part, []):
                types[part].append(label)
            if res and res.get("slots", {}).get(slot, {}).get("low"):
                low[part] += 1
                low_by.setdefault(part, []).append(f"{c['name']} ({header})")

    rows = []
    for part in sorted(set(stock) | set(machines) | set(minimums)):
        on_hand = stock.get(part, 0)
        need = low[part]
        net = on_hand - need
        minimum = minimums.get(part, DEFAULT_MIN_STOCK)
        if net < 0:
            status, tag = f"ORDER {minimum - net}", "short"
        elif net < minimum:
            status, tag = f"Reorder {minimum - net}", "warn"
        elif on_hand == 0 and machines[part]:
            status, tag = "Out of stock", "warn"
        elif net == 0 and need:
            status, tag = "Uses last spare", "warn"
        else:
            status, tag = "OK", ""
        rows.append({"part": part, "type": ", ".join(types.get(part, [])) or "(unassigned)",
                     "machines": machines[part], "low": need, "on_hand": on_hand,
                     "net": net, "minimum": minimum, "status": status, "tag": tag,
                     "low_machines": low_by.get(part, [])})
    return rows


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------

class PartsDialog(tk.Toplevel):
    """Assign part numbers to one copier."""

    def __init__(self, app, copier, on_save):
        super().__init__(app)
        self.title(f"Parts for {copier['name']}")
        self.transient(app)
        self.resizable(False, False)
        self.copier, self.on_save, self.app = copier, on_save, app

        known = sorted({r["part"] for r in app.current_inventory_rows()})
        body = ttk.Frame(self, padding=12)
        body.pack(fill="both", expand=True)

        others = [c for c in app.copiers if c is not copier and any((c.get("parts") or {}).values())]
        row = 0
        if others:
            ttk.Label(body, text="Copy from").grid(row=row, column=0, sticky="w", pady=(0, 8))
            self.copy_var = tk.StringVar()
            cb = ttk.Combobox(body, textvariable=self.copy_var, state="readonly", width=26,
                              values=[f"{c['name']} ({c['ip']})" for c in others])
            cb.grid(row=row, column=1, pady=(0, 8))
            cb.bind("<<ComboboxSelected>>", lambda e: self._copy_from(others))
            row += 1

        self.vars = {}
        parts = copier.get("parts") or {}
        for slot, header in SLOTS:
            ttk.Label(body, text=slot_type_label(slot, header)).grid(row=row, column=0, sticky="w", pady=2)
            var = tk.StringVar(value=parts.get(slot, ""))
            ttk.Combobox(body, textvariable=var, values=known, width=26).grid(row=row, column=1, pady=2)
            self.vars[slot] = var
            row += 1
        ttk.Label(body, text="Leave blank for colors this machine doesn't have.",
                  foreground="#666666").grid(row=row, column=0, columnspan=2, sticky="w", pady=(6, 0))
        btns = ttk.Frame(body)
        btns.grid(row=row + 1, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right", padx=(6, 0))
        ttk.Button(btns, text="Save", command=self._save).pack(side="right")
        self.bind("<Return>", lambda e: self._save())
        self.bind("<Escape>", lambda e: self.destroy())
        self.grab_set()

    def _copy_from(self, others):
        i = self.copy_var.get()
        for c in others:
            if f"{c['name']} ({c['ip']})" == i:
                for slot, _ in SLOTS:
                    self.vars[slot].set((c.get("parts") or {}).get(slot, ""))

    def _save(self):
        self.copier["parts"] = {slot: norm_part(v.get()) for slot, v in self.vars.items()}
        self.on_save()
        self.destroy()


class App(tk.Tk):
    COLUMNS = (("name", "Copier", 140), ("ip", "IP Address", 105),
               ("model", "Model", 170), ("K", "Black", 65), ("C", "Cyan", 65),
               ("M", "Magenta", 70), ("Y", "Yellow", 65), ("waste", "Waste", 85),
               ("parts", "Parts", 70), ("status", "Status", 170))
    CENTERED = {"K", "C", "M", "Y", "waste", "parts"}

    def __init__(self):
        super().__init__()
        self.title("Sharp Toner Monitor")
        self.geometry("1150x520")
        self.minsize(900, 360)

        self.copiers, self.stock, self.minimums = self._load()
        self.results = {}       # ip -> last good reading
        self.errors = {}        # ip -> last error message (cleared on success)
        self.q = queue.Queue()
        self.pool = ThreadPoolExecutor(max_workers=8)
        self.auto_var = tk.BooleanVar(value=False)
        self._auto_job = None

        self.status = tk.StringVar(value="Ready")
        ttk.Label(self, textvariable=self.status, relief="sunken", anchor="w",
                  padding=(6, 2)).pack(fill="x", side="bottom")

        nb = ttk.Notebook(self)
        nb.pack(fill="both", expand=True, padx=6, pady=6)
        self.copier_tab, self.inv_tab = ttk.Frame(nb), ttk.Frame(nb)
        nb.add(self.copier_tab, text="  Copiers  ")
        nb.add(self.inv_tab, text="  Toner Inventory  ")
        self._build_copier_tab(self.copier_tab)
        self._build_inventory_tab(self.inv_tab)

        for c in self.copiers:
            self._insert_row(c)
        self.refresh_inventory()
        self.after(100, self._poll_queue)
        if self.copiers:
            self.refresh_all()

    # ---- persistence ----
    def _load(self):
        try:
            data = json.loads(CONFIG_FILE.read_text())
        except Exception:
            return [], {}, {}
        if isinstance(data, list):                  # older file format
            data = {"copiers": data, "stock": {}}
        copiers = data.get("copiers", [])
        for c in copiers:
            c.setdefault("parts", {})
        stock = {norm_part(k): int(v) for k, v in data.get("stock", {}).items()}
        minimums = {norm_part(k): int(v) for k, v in data.get("minimums", {}).items()}
        return copiers, stock, minimums

    def _save(self):
        try:
            CONFIG_FILE.write_text(json.dumps({"copiers": self.copiers, "stock": self.stock,
                                                "minimums": self.minimums}, indent=2))
        except OSError as e:
            messagebox.showwarning("Save failed", str(e))

    # ======================================================================
    # Copiers tab
    # ======================================================================
    def _build_copier_tab(self, tab):
        add = ttk.LabelFrame(tab, text="Add copier", padding=8)
        add.pack(fill="x", padx=4, pady=(6, 4))
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

        bar = ttk.Frame(tab, padding=(4, 4))
        bar.pack(fill="x")
        ttk.Button(bar, text="Refresh all", command=self.refresh_all).pack(side="left")
        ttk.Button(bar, text="Assign parts...", command=self.assign_parts).pack(side="left", padx=6)
        ttk.Button(bar, text="Remove selected", command=self.remove_selected).pack(side="left")
        ttk.Checkbutton(bar, text="Auto-refresh every 5 min", variable=self.auto_var,
                        command=self._toggle_auto).pack(side="left", padx=10)
        ttk.Label(bar, text="Double-click a row for all supplies").pack(side="right")

        frame = ttk.Frame(tab)
        frame.pack(fill="both", expand=True, padx=4, pady=(0, 4))
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in self.COLUMNS],
                                 show="headings", selectmode="browse")
        for key, title, width in self.COLUMNS:
            self.tree.heading(key, text=title)
            self.tree.column(key, width=width, anchor="center" if key in self.CENTERED else "w")
        sb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.tag_configure("low", background="#ffd6d6")
        self.tree.tag_configure("error", foreground="#888888")
        self.tree.bind("<Delete>", lambda e: self.remove_selected())
        self.tree.bind("<Double-1>", self.show_details)

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
                  "community": self.comm_var.get().strip() or "public", "parts": {}}
        self.copiers.append(copier)
        self._save()
        self._insert_row(copier)
        self.ip_var.set("")
        self.name_var.set("")
        self._refresh_one(copier)
        self.refresh_inventory()
        self.status.set(f"Added {ip}. Use 'Assign parts...' so it counts toward inventory.")

    def remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        ip = sel[0]
        self.copiers = [c for c in self.copiers if c["ip"] != ip]
        self.results.pop(ip, None)
        self.errors.pop(ip, None)
        self.tree.delete(ip)
        self._save()
        self.refresh_inventory()

    def assign_parts(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Assign parts", "Select a copier first.")
            return
        copier = next(c for c in self.copiers if c["ip"] == sel[0])

        def saved():
            self._save()
            self._update_row(copier["ip"])
            self.refresh_inventory()

        PartsDialog(self, copier, saved)

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
        changed = False
        try:
            while True:
                ip, res = self.q.get_nowait()
                if not self.tree.exists(ip):
                    continue
                if "error" in res:
                    self.errors[ip] = res["error"]
                    self.status.set(f"{ip}: {res['error']}")
                else:
                    self.results[ip] = res
                    self.errors.pop(ip, None)
                    self.status.set(f"Updated {ip} at {res['time']}")
                self._update_row(ip)
                changed = True
        except queue.Empty:
            pass
        if changed:
            self.refresh_inventory()
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

    def _insert_row(self, copier):
        self.tree.insert("", "end", iid=copier["ip"],
                         values=(copier["name"], copier["ip"], "", "", "", "", "", "", "", "Waiting..."))
        self._update_row(copier["ip"], waiting=True)

    def _update_row(self, ip, waiting=False):
        copier = next(c for c in self.copiers if c["ip"] == ip)
        res, err = self.results.get(ip), self.errors.get(ip)
        has_parts = "Set" if any((copier.get("parts") or {}).values()) else "Not set"

        if res is None:
            status = "Waiting..." if waiting else f"Error: {err}"
            self.tree.item(ip, values=(copier["name"], ip, "", "-", "-", "-", "-", "-",
                                       has_parts, status),
                           tags=() if waiting else ("error",))
            return

        slots = res["slots"]
        cells = {}
        for slot, _ in SLOTS:
            s = slots.get(slot)
            cells[slot] = "-" if not s else s["text"] + (" \u26a0" if s["low"] else "")
        any_low = any(s["low"] for s in slots.values())
        model = " ".join(res["model"].split())[:40]
        if err:
            status, tags = f"OFFLINE - last read {res['time']}", ("error",)
        else:
            status = ("LOW  " if any_low else "OK  ") + f"({res['time']})"
            tags = ("low",) if any_low else ()
        self.tree.item(ip, values=(copier["name"], ip, model, cells["K"], cells["C"],
                                   cells["M"], cells["Y"], cells["waste"], has_parts, status),
                       tags=tags)

    def show_details(self, _event):
        sel = self.tree.selection()
        if not sel:
            return
        ip = sel[0]
        res = self.results.get(ip)
        if not res:
            messagebox.showerror(ip, self.errors.get(ip, "No data yet"))
            return
        lines = []
        for s in res["supplies"]:
            note = " (fills up)" if s["fills"] else ""
            flag = "  <-- LOW" if s["low"] and s["slot"] else ""
            lines.append(f"{s['desc']}: {s['text']}{note}{flag}")
        messagebox.showinfo(f"{ip} - supplies", "\n".join(lines))

    # ======================================================================
    # Inventory tab
    # ======================================================================
    INV_COLUMNS = (("part", "Part number", 140), ("type", "Type", 230),
                   ("machines", "Machines using", 100), ("low", "Low now", 70),
                   ("on_hand", "On hand", 70), ("net", "After replacing", 100),
                   ("minimum", "Minimum", 80), ("status", "Status", 160))

    def _build_inventory_tab(self, tab):
        form = ttk.LabelFrame(tab, text="Adjust stock", padding=8)
        form.pack(fill="x", padx=4, pady=(6, 4))
        self.part_var, self.qty_var = tk.StringVar(), tk.StringVar(value="1")
        self.min_var = tk.StringVar(value=str(DEFAULT_MIN_STOCK))

        ttk.Label(form, text="Part number").grid(row=0, column=0, sticky="w")
        self.part_combo = ttk.Combobox(form, textvariable=self.part_var, width=22)
        self.part_combo.grid(row=1, column=0, padx=(0, 8))
        ttk.Label(form, text="Quantity").grid(row=0, column=1, sticky="w")
        ttk.Spinbox(form, from_=1, to=999, textvariable=self.qty_var, width=6).grid(row=1, column=1, padx=(0, 8))
        ttk.Button(form, text="+ Add to stock", command=lambda: self.adjust_stock(+1)).grid(row=1, column=2, padx=2)
        ttk.Button(form, text="\u2212 Remove from stock", command=lambda: self.adjust_stock(-1)).grid(row=1, column=3, padx=2)
        ttk.Label(form, text="Minimum to keep").grid(row=0, column=5, sticky="w", padx=(16, 0))
        ttk.Spinbox(form, from_=0, to=999, textvariable=self.min_var, width=6).grid(row=1, column=5, padx=(16, 8))
        ttk.Button(form, text="Set minimum", command=self.set_minimum).grid(row=1, column=6, padx=2)
        ttk.Button(form, text="Delete part", command=self.delete_part).grid(row=1, column=7, padx=(16, 0))

        frame = ttk.Frame(tab)
        frame.pack(fill="both", expand=True, padx=4, pady=(0, 4))
        self.inv_tree = ttk.Treeview(frame, columns=[c[0] for c in self.INV_COLUMNS],
                                     show="headings", selectmode="browse")
        for key, title, width in self.INV_COLUMNS:
            self.inv_tree.heading(key, text=title)
            self.inv_tree.column(key, width=width, anchor="w" if key in ("part", "type", "status") else "center")
        sb = ttk.Scrollbar(frame, orient="vertical", command=self.inv_tree.yview)
        self.inv_tree.configure(yscrollcommand=sb.set)
        self.inv_tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.inv_tree.tag_configure("short", background="#ffd6d6")
        self.inv_tree.tag_configure("warn", background="#fff0c2")
        self.inv_tree.bind("<<TreeviewSelect>>", self._inv_selected)
        self.inv_tree.bind("<Double-1>", self._inv_details)

        self.inv_note = tk.StringVar()
        ttk.Label(tab, textvariable=self.inv_note, foreground="#555555",
                  wraplength=1000, justify="left").pack(fill="x", padx=6, pady=(0, 4))

    def current_inventory_rows(self):
        return inventory_rows(self.copiers, self.results, self.stock, self.minimums)

    def refresh_inventory(self):
        rows = self.current_inventory_rows()
        selected = self.inv_tree.selection()
        self.inv_tree.delete(*self.inv_tree.get_children())
        self._inv_low_machines = {}
        for r in rows:
            self._inv_low_machines[r["part"]] = r["low_machines"]
            self.inv_tree.insert("", "end", iid=r["part"], tags=(r["tag"],) if r["tag"] else (),
                                 values=(r["part"], r["type"], r["machines"], r["low"],
                                         r["on_hand"], r["net"], r["minimum"], r["status"]))
        if selected and self.inv_tree.exists(selected[0]):
            self.inv_tree.selection_set(selected[0])
        self.part_combo["values"] = [r["part"] for r in rows]

        unassigned = sum(1 for c in self.copiers if not any((c.get("parts") or {}).values()))
        unread = sum(1 for c in self.copiers if c["ip"] not in self.results)
        notes = ["'After replacing' = on hand minus machines currently low; "
                 "Status compares it with the part's minimum. "
                 "Refresh copiers before deducting a toner you just installed, "
                 "or it will be counted twice until the machine reads full."]
        if unassigned:
            notes.append(f"{unassigned} copier(s) have no parts assigned and aren't counted.")
        if unread:
            notes.append(f"{unread} copier(s) have no reading yet.")
        self.inv_note.set("  ".join(notes))

    def _inv_selected(self, _event):
        sel = self.inv_tree.selection()
        if sel:
            self.part_var.set(sel[0])
            self.min_var.set(str(self.minimums.get(sel[0], DEFAULT_MIN_STOCK)))

    def _inv_details(self, _event):
        sel = self.inv_tree.selection()
        if not sel:
            return
        machines = self._inv_low_machines.get(sel[0], [])
        body = "\n".join(machines) if machines else "No machines are currently low on this part."
        messagebox.showinfo(f"{sel[0]} - machines needing it", body)

    def adjust_stock(self, sign):
        part = norm_part(self.part_var.get())
        if not part:
            messagebox.showerror("Part number", "Enter or select a part number.")
            return
        try:
            qty = int(self.qty_var.get())
            if qty < 1:
                raise ValueError
        except ValueError:
            messagebox.showerror("Quantity", "Quantity must be a whole number of 1 or more.")
            return
        current = self.stock.get(part, 0)
        if sign < 0 and qty > current:
            messagebox.showerror("Not enough stock", f"Only {current} x {part} on hand.")
            return
        self.stock[part] = current + sign * qty
        self._save()
        self.refresh_inventory()
        self.status.set(f"{part}: {'added' if sign > 0 else 'removed'} {qty}, now {self.stock[part]} on hand")

    def set_minimum(self):
        part = norm_part(self.part_var.get())
        if not part:
            messagebox.showerror("Part number", "Enter or select a part number.")
            return
        try:
            minimum = int(self.min_var.get())
            if minimum < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Minimum", "Minimum must be a whole number, 0 or more.")
            return
        self.minimums[part] = minimum
        self.stock.setdefault(part, 0)
        self._save()
        self.refresh_inventory()
        self.status.set(f"{part}: minimum set to {minimum}")

    def delete_part(self):
        part = norm_part(self.part_var.get())
        if not part:
            return
        users = [c["name"] for c in self.copiers
                 if part in {norm_part(v) for v in (c.get("parts") or {}).values()}]
        if users:
            messagebox.showinfo("Part in use", f"{part} is still assigned to: {', '.join(users)}.\n"
                                "Unassign it from those copiers first.")
            return
        if part not in self.stock:
            return
        if self.stock[part] > 0 and not messagebox.askyesno(
                "Delete part", f"Delete {part}? {self.stock[part]} on hand will be forgotten."):
            return
        del self.stock[part]
        self.minimums.pop(part, None)
        self.part_var.set("")
        self._save()
        self.refresh_inventory()


if __name__ == "__main__":
    App().mainloop()
