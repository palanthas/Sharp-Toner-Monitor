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
import threading
import time
import tkinter as tk
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from tkinter import messagebox, simpledialog, ttk

CONFIG_FILE = Path.home() / ".sharp_toner_monitor.json"
LOW_THRESHOLD = 10          # toner counts as low at/below this % remaining
WASTE_FULL_THRESHOLD = 101  # waste collector counts as full at/above this % full
DEFAULT_MIN_STOCK = 0       # minimum spares to keep for any part without its own
                            # minimum (set per part on the Inventory tab)
AUTO_REFRESH_MS = 5 * 60 * 1000
SNMP_TIMEOUT = 2.0
SNMP_RETRIES = 1
SCAN_TIMEOUT = 1.0          # seconds to wait for each host during a scan
SCAN_WORKERS = 64           # hosts probed in parallel
MAX_SCAN_HOSTS = 1024       # refuse ranges bigger than this (e.g. a whole /16)

# Slots a copier can have a part number for: (key, column header)
SLOTS = (("K", "Black"), ("C", "Cyan"), ("M", "Magenta"), ("Y", "Yellow"),
         ("waste", "Waste collector"))


def slot_type_label(slot, header):
    return header if slot == "waste" else f"{header} toner"


def norm_part(text):
    return (text or "").strip().upper()


# Columns sorted as text; every other column is sorted numerically when it
# starts with a number ("45%", "95% full", "-2"), with text after the numbers
# and blank / "-" / "?" cells always last.
TEXT_COLUMNS = {"name", "model", "parts", "part", "type", "status"}
_NUM = re.compile(r"^\s*(-?\d+(?:\.\d+)?)")


def _natural(text):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", text)]


def sort_key(col, text):
    """Sort key for a table cell, or None for blank cells."""
    text = str(text).strip()
    if text in ("", "-", "?"):
        return None
    if col == "ip":
        try:
            return (0, int(ipaddress.ip_address(text)))
        except ValueError:
            pass
    if col not in TEXT_COLUMNS:
        m = _NUM.match(text)
        if m:
            return (0, float(m.group(1)))
    return (1, _natural(text))


# Model matching, used to put like machines first when copying parts.
MODEL_RE = re.compile(r"\b[A-Za-z]{1,4}-[A-Za-z]*\d+[A-Za-z0-9]*\b")   # e.g. MX-3071, BP-70C45
SIMILAR_MIN_PREFIX = 5      # models sharing this many leading characters are "similar"
SAME_MODEL = 10_000


def model_key(text):
    """Reduce a description like 'SHARP BP-70C45 ver 1.2' to 'BP-70C45'."""
    text = " ".join((text or "").split())
    m = MODEL_RE.search(text)
    return (m.group(0) if m else text).upper()


def model_similarity(a, b):
    """0 = unknown/unrelated, higher = more alike, SAME_MODEL = identical model."""
    ka, kb = model_key(a), model_key(b)
    if not ka or not kb:
        return 0
    if ka == kb:
        return SAME_MODEL
    n = 0
    for x, y in zip(ka, kb):
        if x != y:
            break
        n += 1
    return n if n >= SIMILAR_MIN_PREFIX else 0


def order_copy_sources(target_model, candidates):
    """
    candidates: [(name, model, item)]. Returns [(item, tag)] with the closest
    models first (tag is 'same model' / 'similar model'), then everything else
    alphabetically by name.
    """
    scored = [(model_similarity(target_model, model), name, item) for name, model, item in candidates]
    scored.sort(key=lambda t: (-t[0], _natural(t[1])))
    out = []
    for score, _name, item in scored:
        tag = "same model" if score >= SAME_MODEL else "similar model" if score else ""
        out.append((item, tag))
    return out


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


def snmp_get_next(sock, ip, community, oid, retries=SNMP_RETRIES):
    """Send one GETNEXT and return (next_oid, value)."""
    req_id = random.randint(1, 0x7FFFFFFF)
    varbind = _tlv(0x30, _enc_oid(oid) + b"\x05\x00")
    pdu = _tlv(0xA1, _enc_int(req_id) + _enc_int(0) + _enc_int(0) + _tlv(0x30, varbind))
    msg = _tlv(0x30, _enc_int(1) + _tlv(0x04, community.encode()) + pdu)

    last_err = socket.timeout("no response (check IP, SNMP enabled, community string)")
    for _ in range(retries + 1):
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
# Network scanning
# --------------------------------------------------------------------------

def parse_ip_range(text):
    """
    Turn user input into a list of IPv4 address strings. Accepts, comma-separated:
      192.168.0.50            a single address
      192.168.0.50-60         last-octet range
      192.168.0.50-192.168.1.9  full range
      192.168.0.0/24          CIDR network (network/broadcast addresses skipped)
    Raises ValueError with a readable message on bad input or oversized ranges.
    """
    def v4(t):
        try:
            ip = ipaddress.ip_address(t.strip())
        except ValueError:
            raise ValueError(f"'{t.strip()}' is not a valid IP address.")
        if ip.version != 4:
            raise ValueError("Only IPv4 addresses are supported.")
        return ip

    hosts = []
    parts = [p.strip() for p in re.split(r"[,;]", text) if p.strip()]
    if not parts:
        raise ValueError("Enter an IP range to scan.")
    for part in parts:
        if "/" in part:
            try:
                net = ipaddress.ip_network(part, strict=False)
            except ValueError:
                raise ValueError(f"'{part}' is not a valid network.")
            if net.version != 4:
                raise ValueError("Only IPv4 addresses are supported.")
            hosts.extend(str(h) for h in net.hosts())
        elif "-" in part:
            left, right = (t.strip() for t in part.split("-", 1))
            start = v4(left)
            end = v4(right if "." in right else left.rsplit(".", 1)[0] + "." + right)
            if int(end) < int(start):
                raise ValueError(f"Range '{part}' ends before it starts.")
            if int(end) - int(start) + 1 > MAX_SCAN_HOSTS:
                raise ValueError(f"Range '{part}' is too large (limit {MAX_SCAN_HOSTS} addresses).")
            hosts.extend(str(ipaddress.ip_address(i)) for i in range(int(start), int(end) + 1))
        else:
            hosts.append(str(v4(part)))
        if len(hosts) > MAX_SCAN_HOSTS:
            raise ValueError(f"That's more than {MAX_SCAN_HOSTS} addresses. Narrow the range.")
    return list(dict.fromkeys(hosts))     # de-duplicate, keep order


def probe_host(ip, community):
    """
    Ask one address for its SNMP identity. Returns a dict, or None if it doesn't
    answer. 'printer' is True when the Printer-MIB supplies table exists.
    """
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(SCAN_TIMEOUT)
    try:
        try:
            _, descr = snmp_get_next(sock, ip, community, "1.3.6.1.2.1.1.1", retries=1)
        except (socket.timeout, OSError):
            return None
        if descr is END or not isinstance(descr, str):
            return None
        name, printer = "", False
        try:
            oid, val = snmp_get_next(sock, ip, community, "1.3.6.1.2.1.1.4.0", retries=1)
            if oid == "1.3.6.1.2.1.1.5.0" and isinstance(val, str):
                name = val
            oid, val = snmp_get_next(sock, ip, community, f"{SUPPLIES}.{COL_DESC}", retries=1)
            printer = val is not END and oid.startswith(f"{SUPPLIES}.{COL_DESC}.")
        except (socket.timeout, OSError):
            pass
        descr = " ".join(descr.split())
        return {"ip": ip, "name": name.strip(), "descr": descr, "printer": printer,
                "sharp": "sharp" in (descr + " " + name).lower()}
    finally:
        sock.close()


def guess_scan_range():
    """Pre-fill the scan box with this computer's /24."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("192.0.2.1", 9))         # no packet is sent; just picks a route
        local = s.getsockname()[0]
        s.close()
        return local.rsplit(".", 1)[0] + ".1-254"
    except OSError:
        return "192.168.0.1-254"


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
    models, unknown, seen = {}, {}, {}      # per part: model counts / copiers w/o a known model
    for c in copiers:
        res = results.get(c["ip"])
        model = (res.get("model") if res else "") or c.get("model", "")
        for slot, header in SLOTS:
            part = norm_part((c.get("parts") or {}).get(slot))
            if not part:
                continue
            machines[part] += 1
            if c["ip"] not in seen.setdefault(part, set()):     # count each copier once per part
                seen[part].add(c["ip"])
                if model:
                    models.setdefault(part, Counter())[model_key(model)] += 1
                else:
                    unknown.setdefault(part, []).append(c["name"])
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
                     "low_machines": low_by.get(part, []),
                     "models": sorted(models.get(part, {}).items(), key=lambda kv: _natural(kv[0])),
                     "unknown": unknown.get(part, [])})
    return rows


def describe_part(row):
    """Text for the inventory detail popup: low machines, then models using the part."""
    lines = []
    if row["low_machines"]:
        lines.append(f"Low now ({len(row['low_machines'])}):")
        lines += [f"  {name}" for name in row["low_machines"]]
    else:
        lines.append("No machines are currently low on this part.")
    lines.append("")
    if row["models"] or row["unknown"]:
        lines.append("Models using this part:")
        for key, n in row["models"]:
            lines.append(f"  {key} ({n} machine{'s' if n != 1 else ''})")
        if row["unknown"]:
            lines.append(f"  Unknown model: {', '.join(row['unknown'])}")
    else:
        lines.append("No copiers are assigned this part.")
    return "\n".join(lines)


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
            ordered = order_copy_sources(
                app.model_of(copier), [(c["name"], app.model_of(c), c) for c in others])
            self.copy_map = {}
            for c, tag in ordered:      # closest model first, then alphabetical
                self.copy_map[f"{c['name']} ({c['ip']})" + (f" - {tag}" if tag else "")] = c
            cb = ttk.Combobox(body, textvariable=self.copy_var, state="readonly", width=40,
                              values=list(self.copy_map))
            cb.grid(row=row, column=1, pady=(0, 8))
            cb.bind("<<ComboboxSelected>>", lambda e: self._copy_from())
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

    def _copy_from(self):
        c = self.copy_map.get(self.copy_var.get())
        if c:
            for slot, _ in SLOTS:
                self.vars[slot].set((c.get("parts") or {}).get(slot, ""))

    def _save(self):
        self.copier["parts"] = {slot: norm_part(v.get()) for slot, v in self.vars.items()}
        self.on_save()
        self.destroy()


class CopierDialog(tk.Toplevel):
    """Edit a copier's name, IP address and SNMP community."""

    def __init__(self, app, copier):
        super().__init__(app)
        self.title(f"Edit {copier['name']}")
        self.transient(app)
        self.resizable(False, False)
        self.app, self.copier = app, copier
        body = ttk.Frame(self, padding=12)
        body.pack()
        self.vars = {}
        for r, (key, label) in enumerate((("ip", "IP address"), ("name", "Name"),
                                          ("community", "SNMP community"))):
            ttk.Label(body, text=label).grid(row=r, column=0, sticky="w", pady=3, padx=(0, 10))
            var = tk.StringVar(value=copier[key])
            ttk.Entry(body, textvariable=var, width=28).grid(row=r, column=1)
            self.vars[key] = var
        ttk.Label(body, text="Assigned parts stay with the copier, even if you change its IP.",
                  foreground="#666666").grid(row=3, column=0, columnspan=2, sticky="w", pady=(8, 0))
        btns = ttk.Frame(body)
        btns.grid(row=4, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right", padx=(6, 0))
        ttk.Button(btns, text="Save", command=self._save).pack(side="right")
        self.bind("<Return>", lambda e: self._save())
        self.bind("<Escape>", lambda e: self.destroy())
        self.grab_set()

    def _save(self):
        err = self.app.apply_copier_edit(self.copier, self.vars["ip"].get().strip(),
                                         self.vars["name"].get().strip(),
                                         self.vars["community"].get().strip())
        if err:
            messagebox.showerror("Edit copier", err, parent=self)
            return
        self.destroy()


class ScanDialog(tk.Toplevel):
    """Scan an IP range over SNMP and add the copiers it finds."""

    COLUMNS = (("ip", "IP Address", 120), ("name", "Name", 150),
               ("type", "Type", 130), ("descr", "Description", 380))

    def __init__(self, app):
        super().__init__(app)
        self.title("Scan for copiers")
        self.geometry("880x540")
        self.minsize(720, 420)
        self.transient(app)
        self.app = app
        self.found = {}                 # ip -> probe result
        self.running = False
        self.cancel = threading.Event()
        self.scan_q = queue.Queue()
        self.pool = None
        self.total = self.done = self.skipped = 0
        self.scanned_community = "public"

        box = ttk.LabelFrame(self, text="What to scan", padding=8)
        box.pack(fill="x", padx=10, pady=(10, 4))
        self.range_var = tk.StringVar(value=guess_scan_range())
        self.comm_var = tk.StringVar(value="public")
        ttk.Label(box, text="IP range").grid(row=0, column=0, sticky="w")
        entry = ttk.Entry(box, textvariable=self.range_var, width=46)
        entry.grid(row=1, column=0, padx=(0, 8))
        ttk.Label(box, text="SNMP community").grid(row=0, column=1, sticky="w")
        ttk.Entry(box, textvariable=self.comm_var, width=16).grid(row=1, column=1, padx=(0, 8))
        self.scan_btn = ttk.Button(box, text="Scan", command=self.start_scan)
        self.scan_btn.grid(row=1, column=2, padx=2)
        self.stop_btn = ttk.Button(box, text="Stop", command=self.stop_scan, state="disabled")
        self.stop_btn.grid(row=1, column=3, padx=2)
        ttk.Label(box, foreground="#666666",
                  text="Examples: 192.168.0.50-60   192.168.0.0/24   10.0.0.5-10.0.1.20   "
                       "(separate several with commas). Addresses already in your list are skipped."
                  ).grid(row=2, column=0, columnspan=4, sticky="w", pady=(6, 0))
        self.printers_only = tk.BooleanVar(value=True)
        self.sharp_only = tk.BooleanVar(value=False)
        ttk.Checkbutton(box, text="Only show printers/copiers", variable=self.printers_only,
                        command=self._render).grid(row=3, column=0, sticky="w", pady=(6, 0))
        ttk.Checkbutton(box, text="Only show Sharp", variable=self.sharp_only,
                        command=self._render).grid(row=3, column=1, columnspan=2, sticky="w", pady=(6, 0))

        prog = ttk.Frame(self)
        prog.pack(fill="x", padx=10, pady=4)
        self.bar = ttk.Progressbar(prog, mode="determinate")
        self.bar.pack(side="left", fill="x", expand=True)
        self.info = tk.StringVar(value="Enter a range and click Scan.")
        ttk.Label(prog, textvariable=self.info, width=48).pack(side="left", padx=(8, 0))

        frame = ttk.Frame(self)
        frame.pack(fill="both", expand=True, padx=10, pady=(0, 4))
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in self.COLUMNS],
                                 show="headings", selectmode="extended")
        for key, title, width in self.COLUMNS:
            self.tree.heading(key, text=title)
            self.tree.column(key, width=width, anchor="w")
        sb = ttk.Scrollbar(frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<Control-a>", lambda e: (self.select_all(), "break")[1])

        btns = ttk.Frame(self)
        btns.pack(fill="x", padx=10, pady=(4, 10))
        ttk.Button(btns, text="Close", command=self._close).pack(side="right")
        ttk.Button(btns, text="Add selected to monitor", command=self.add_selected).pack(side="right", padx=6)
        ttk.Button(btns, text="Select all", command=self.select_all).pack(side="left")
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.bind("<Escape>", lambda e: self._close())
        entry.focus_set()
        entry.bind("<Return>", lambda e: self.start_scan())

    # ---- scanning ----
    def start_scan(self):
        if self.running:
            return
        try:
            hosts = parse_ip_range(self.range_var.get())
        except ValueError as e:
            messagebox.showerror("IP range", str(e), parent=self)
            return
        existing = {c["ip"] for c in self.app.copiers}
        todo = [h for h in hosts if h not in existing]
        self.skipped = len(hosts) - len(todo)
        if not todo:
            self.info.set(f"Nothing to scan: all {self.skipped} address(es) are already added.")
            return
        self.scanned_community = self.comm_var.get().strip() or "public"
        self.found.clear()
        self._render()
        self.cancel = threading.Event()
        self.scan_q = queue.Queue()
        self.total, self.done = len(todo), 0
        self.bar.configure(maximum=self.total, value=0)
        self.running = True
        self.scan_btn.state(["disabled"])
        self.stop_btn.state(["!disabled"])
        self.pool = ThreadPoolExecutor(max_workers=SCAN_WORKERS)
        for ip in todo:
            self.pool.submit(self._probe, ip, self.scanned_community, self.cancel, self.scan_q)
        self._update_info()
        self.after(100, self._poll)

    @staticmethod
    def _probe(ip, community, cancel, out):
        result = None
        if not cancel.is_set():
            try:
                result = probe_host(ip, community)
            except Exception:
                result = None
        out.put((ip, result))

    def stop_scan(self):
        self.cancel.set()
        self.stop_btn.state(["disabled"])
        self.info.set("Stopping...")

    def _poll(self):
        if not self.running:
            return
        got = False
        try:
            while True:
                ip, res = self.scan_q.get_nowait()
                self.done += 1
                if res:
                    self.found[ip] = res
                    got = True
        except queue.Empty:
            pass
        self.bar["value"] = self.done
        if got:
            self._render()
        if self.done >= self.total:
            self._finish()
        else:
            self._update_info()
            self.after(100, self._poll)

    def _finish(self):
        self.running = False
        if self.pool:
            self.pool.shutdown(wait=False)
        self.scan_btn.state(["!disabled"])
        self.stop_btn.state(["disabled"])
        verb = "Stopped" if self.cancel.is_set() else "Done"
        self.info.set(f"{verb}. Scanned {self.done}/{self.total}, found {len(self._visible())}"
                      + (f" ({self.skipped} already added, skipped)" if self.skipped else ""))

    def _update_info(self):
        self.info.set(f"Scanned {self.done}/{self.total}, found {len(self._visible())}"
                      + (f" ({self.skipped} already added, skipped)" if self.skipped else ""))

    # ---- results ----
    def _visible(self):
        rows = [r for r in self.found.values()
                if (r["printer"] or not self.printers_only.get())
                and (r["sharp"] or not self.sharp_only.get())]
        rows.sort(key=lambda r: int(ipaddress.ip_address(r["ip"])))
        return rows

    def _render(self):
        selected = set(self.tree.selection())
        self.tree.delete(*self.tree.get_children())
        for r in self._visible():
            kind = ("Sharp printer" if r["sharp"] else "Printer") if r["printer"] else "Other SNMP device"
            self.tree.insert("", "end", iid=r["ip"],
                             values=(r["ip"], r["name"], kind, r["descr"][:80]))
        keep = [i for i in selected if self.tree.exists(i)]
        if keep:
            self.tree.selection_set(keep)
        if not self.running and self.total:
            self._update_info()

    def select_all(self):
        self.tree.selection_set(self.tree.get_children())

    def add_selected(self):
        sel = self.tree.selection()
        if not sel:
            self.info.set("Select one or more devices first.")
            return
        chosen = [self.found[ip] for ip in sel if ip in self.found]
        added = self.app.add_scanned(chosen, self.scanned_community)
        for ip in sel:
            self.found.pop(ip, None)
        self._render()
        self.info.set(f"Added {added} copier(s). Assign their parts on the Copiers tab.")

    def _close(self):
        self.cancel.set()
        self.running = False
        if self.pool:
            self.pool.shutdown(wait=False)
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
        self.sorts = {"copier": None, "inv": ("part", False)}   # name -> (column, descending)

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
        self._resort_copiers()
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
        ttk.Button(add, text="Scan network...", command=self.open_scan).grid(row=1, column=4, padx=(24, 0))
        ip_entry.bind("<Return>", lambda e: self.add_copier())
        ip_entry.focus_set()

        bar = ttk.Frame(tab, padding=(4, 4))
        bar.pack(fill="x")
        ttk.Button(bar, text="Refresh all", command=self.refresh_all).pack(side="left")
        ttk.Button(bar, text="Assign parts...", command=self.assign_parts).pack(side="left", padx=6)
        ttk.Button(bar, text="Edit copier...", command=self.edit_copier).pack(side="left")
        ttk.Button(bar, text="Remove selected", command=self.remove_selected).pack(side="left", padx=6)
        ttk.Checkbutton(bar, text="Auto-refresh every 5 min", variable=self.auto_var,
                        command=self._toggle_auto).pack(side="left", padx=10)
        ttk.Label(bar, text="Double-click a row for all supplies  |  click a header to sort").pack(side="right")

        frame = ttk.Frame(tab)
        frame.pack(fill="both", expand=True, padx=4, pady=(0, 4))
        self.tree = ttk.Treeview(frame, columns=[c[0] for c in self.COLUMNS],
                                 show="headings", selectmode="browse")
        for key, title, width in self.COLUMNS:
            self.tree.column(key, width=width, anchor="center" if key in self.CENTERED else "w")
        self._make_sortable(self.tree, "copier", self.COLUMNS)
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
        self._resort_copiers()
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
            self._resort_copiers()
            self.refresh_inventory()

        PartsDialog(self, copier, saved)

    def model_of(self, copier):
        """Best-known model description: latest reading, else the remembered one."""
        res = self.results.get(copier["ip"])
        return (res.get("model") if res else "") or copier.get("model", "")

    def open_scan(self):
        dlg = getattr(self, "_scan_dialog", None)
        if dlg is not None and dlg.winfo_exists():
            dlg.lift()
            return
        self._scan_dialog = ScanDialog(self)

    def add_scanned(self, found, community):
        """Add copiers discovered by a scan. Returns how many were new."""
        existing = {c["ip"] for c in self.copiers}
        added = 0
        for f in found:
            if f["ip"] in existing:
                continue
            copier = {"ip": f["ip"], "name": f["name"] or f["ip"],
                      "community": community, "parts": {}, "model": f.get("descr", "")}
            self.copiers.append(copier)
            existing.add(f["ip"])
            self._insert_row(copier)
            self._refresh_one(copier)
            added += 1
        if added:
            self._save()
            self._resort_copiers()
            self.refresh_inventory()
            self.status.set(f"Added {added} scanned copier(s). Use 'Assign parts...' on each.")
        return added

    def edit_copier(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Edit copier", "Select a copier first.")
            return
        CopierDialog(self, next(c for c in self.copiers if c["ip"] == sel[0]))

    def apply_copier_edit(self, copier, ip, name, community):
        """Apply edits from the dialog. Returns an error string, or None on success."""
        try:
            ipaddress.ip_address(ip)
        except ValueError:
            return f"'{ip}' is not a valid IP address."
        if any(c is not copier and c["ip"] == ip for c in self.copiers):
            return f"{ip} is already in the list."
        old_ip = copier["ip"]
        if name == old_ip and ip != old_ip:         # name was just the old IP
            name = ip
        copier["name"] = name or ip
        copier["community"] = community or "public"
        if ip != old_ip:
            index = self.tree.index(old_ip)
            self.tree.delete(old_ip)
            self.results.pop(old_ip, None)          # old readings belong to the old address
            self.errors.pop(old_ip, None)
            copier["ip"] = ip
            copier.pop("model", None)               # new address, maybe a different machine
            self._insert_row(copier, index)
        self._save()
        self._update_row(ip)
        self._refresh_one(copier)
        self._resort_copiers()
        self.refresh_inventory()
        return None

    # ---- column sorting (shared by both tables) ----
    def _make_sortable(self, tree, name, columns):
        for key, title, _width in columns:
            tree.heading(key, text=title,
                         command=lambda k=key: self._sort_by(tree, name, columns, k))

    def _sort_by(self, tree, name, columns, col):
        cur = self.sorts.get(name)
        descending = bool(cur and cur[0] == col and not cur[1])   # 2nd click flips
        self.sorts[name] = (col, descending)
        self._apply_sort(tree, name, columns)

    def _apply_sort(self, tree, name, columns):
        state = self.sorts.get(name)
        for key, title, _width in columns:
            arrow = ""
            if state and state[0] == key:
                arrow = "  \u25bc" if state[1] else "  \u25b2"
            tree.heading(key, text=title + arrow)
        if not state:
            return
        col, descending = state
        keyed, blanks = [], []
        for iid in tree.get_children(""):
            k = sort_key(col, tree.set(iid, col))
            (blanks if k is None else keyed).append((k, iid))
        keyed.sort(key=lambda t: t[0], reverse=descending)
        for pos, (_k, iid) in enumerate(keyed + blanks):    # blanks always last
            tree.move(iid, "", pos)

    def _resort_copiers(self):
        self._apply_sort(self.tree, "copier", self.COLUMNS)

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
        changed = model_changed = False
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
                    model = " ".join(res["model"].split())
                    c = next((c for c in self.copiers if c["ip"] == ip), None)
                    if c and model and c.get("model") != model:
                        c["model"] = model          # remembered for model matching
                        model_changed = True
                    self.status.set(f"Updated {ip} at {res['time']}")
                self._update_row(ip)
                changed = True
        except queue.Empty:
            pass
        if model_changed:
            self._save()
        if changed:
            self._resort_copiers()
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

    def _insert_row(self, copier, index="end"):
        self.tree.insert("", index, iid=copier["ip"],
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
        ttk.Spinbox(form, from_=0, to=999, textvariable=self.qty_var, width=6).grid(row=1, column=1, padx=(0, 8))
        ttk.Button(form, text="+ Add to stock", command=lambda: self.adjust_stock(+1)).grid(row=1, column=2, padx=2)
        ttk.Button(form, text="\u2212 Remove from stock", command=lambda: self.adjust_stock(-1)).grid(row=1, column=3, padx=2)
        ttk.Button(form, text="Set exact count", command=self.set_exact).grid(row=1, column=4, padx=2)
        ttk.Label(form, text="Minimum to keep").grid(row=0, column=5, sticky="w", padx=(16, 0))
        ttk.Spinbox(form, from_=0, to=999, textvariable=self.min_var, width=6).grid(row=1, column=5, padx=(16, 8))
        ttk.Button(form, text="Set minimum", command=self.set_minimum).grid(row=1, column=6, padx=2)
        mg = ttk.Frame(form)
        mg.grid(row=2, column=0, columnspan=8, sticky="w", pady=(8, 0))
        ttk.Button(mg, text="Rename part...", command=self.rename_part).pack(side="left")
        ttk.Button(mg, text="Delete part", command=self.delete_part).pack(side="left", padx=6)
        ttk.Label(mg, text="Click a column header to sort.", foreground="#666666").pack(side="left", padx=10)

        frame = ttk.Frame(tab)
        frame.pack(fill="both", expand=True, padx=4, pady=(0, 4))
        self.inv_tree = ttk.Treeview(frame, columns=[c[0] for c in self.INV_COLUMNS],
                                     show="headings", selectmode="browse")
        for key, title, width in self.INV_COLUMNS:
            self.inv_tree.column(key, width=width, anchor="w" if key in ("part", "type", "status") else "center")
        self._make_sortable(self.inv_tree, "inv", self.INV_COLUMNS)
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
        self._inv_rows = {}
        for r in rows:
            self._inv_rows[r["part"]] = r
            self.inv_tree.insert("", "end", iid=r["part"], tags=(r["tag"],) if r["tag"] else (),
                                 values=(r["part"], r["type"], r["machines"], r["low"],
                                         r["on_hand"], r["net"], r["minimum"], r["status"]))
        self._apply_sort(self.inv_tree, "inv", self.INV_COLUMNS)
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
        row = self._inv_rows.get(sel[0])
        if row:
            messagebox.showinfo(f"{sel[0]} - details", describe_part(row))

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

    def set_exact(self):
        part = norm_part(self.part_var.get())
        if not part:
            messagebox.showerror("Part number", "Enter or select a part number.")
            return
        try:
            qty = int(self.qty_var.get())
            if qty < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Quantity", "Quantity must be a whole number, 0 or more.")
            return
        self.stock[part] = qty
        self._save()
        self.refresh_inventory()
        self.status.set(f"{part}: on hand set to {qty}")

    def rename_part(self):
        """Rename a part everywhere: stock, minimum, and every copier assignment."""
        old = norm_part(self.part_var.get())
        known = {r["part"] for r in self.current_inventory_rows()}
        if old not in known:
            messagebox.showinfo("Rename part", "Select a part in the table first.")
            return
        new = norm_part(simpledialog.askstring("Rename part", f"New part number for {old}:",
                                               initialvalue=old, parent=self))
        if not new or new == old:
            return
        if new in known and not messagebox.askyesno(
                "Merge parts", f"{new} already exists.\n\nMerge {old} into it? Stock counts are "
                f"added together and copiers using {old} will switch to {new}."):
            return
        self.stock[new] = self.stock.get(new, 0) + self.stock.pop(old, 0)
        if old in self.minimums:
            self.minimums.setdefault(new, self.minimums.pop(old))
            self.minimums.pop(old, None)
        for c in self.copiers:
            parts = c.get("parts") or {}
            for slot, value in list(parts.items()):
                if norm_part(value) == old:
                    parts[slot] = new
        self._save()
        self.part_var.set(new)
        self.refresh_inventory()
        if self.inv_tree.exists(new):
            self.inv_tree.selection_set(new)
        self.status.set(f"Renamed {old} to {new} everywhere")

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
