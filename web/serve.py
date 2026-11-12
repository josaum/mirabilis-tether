#!/usr/bin/env python3
"""Read-only loopback server for the Tether-Optimize workbench.

Serves web/ statically and exposes /api/snapshot, assembled from the files the
daemon already writes (ui.snapshot, shaper.state, throttled.pids, the event log)
plus live sysctl reads. No writes, no root, no external dependencies.
"""

import argparse
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote, urlparse

CONTENT_TYPES = {
    ".html": "text/html; charset=utf-8",
    ".js": "text/javascript; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".json": "application/json; charset=utf-8",
    ".svg": "image/svg+xml",
    ".png": "image/png",
    ".ico": "image/x-icon",
}

# Fallback only: the engine writes the profile it applied to tcp-profile.env, and
# that file is authoritative. These mirror apply_tcp_profile() in bin/tether-optimize.
TCP_PROFILES = {
    "home": {
        "net.inet.tcp.delayed_ack": "3",
        "net.inet.tcp.sendspace": "262144",
        "net.inet.tcp.recvspace": "262144",
        "net.inet.tcp.autosndbufmax": "4194304",
        "net.inet.tcp.autorcvbufmax": "4194304",
        "net.inet.tcp.autosndbufinc": "32768",
        "net.inet.tcp.mssdflt": "1452",
        "net.inet.tcp.v6mssdflt": "1432",
        "net.inet.tcp.l4s": "1",
        "net.inet.tcp.bg_target_qdelay": "20",
        "net.inet.tcp.bg_tether_shift": "2",
        "net.inet.tcp.bg_allowed_increase": "4",
        "net.classq.fq_codel.enable_ecn": "1",
        "net.classq.fq_codel.enable_l4s": "1",
        "net.classq.fq_codel.enable_pacing": "1",
    },
    "hotspot": {
        "net.inet.tcp.delayed_ack": "3",
        "net.inet.tcp.sendspace": "65536",
        "net.inet.tcp.recvspace": "65536",
        "net.inet.tcp.autosndbufmax": "524288",
        "net.inet.tcp.autorcvbufmax": "1048576",
        "net.inet.tcp.autosndbufinc": "8192",
        "net.inet.tcp.mssdflt": "1380",
        "net.inet.tcp.v6mssdflt": "1380",
        "net.inet.tcp.l4s": "1",
        "net.inet.tcp.bg_target_qdelay": "15",
        "net.inet.tcp.bg_tether_shift": "3",
        "net.inet.tcp.bg_allowed_increase": "2",
        "net.classq.fq_codel.enable_ecn": "1",
        "net.classq.fq_codel.enable_l4s": "1",
        "net.classq.fq_codel.enable_pacing": "1",
    },
}

LOG_LINES = 40
AUDIT_PCAP = "/tmp/tether-optimize-audit.pcapng"
THEOREM_RE = re.compile(r"^theorem\s+([A-Za-z0-9_'.]+)")
SECTION_RE = re.compile(r"^/-!\s*##\s*(.+?)(?:\s*-/)?$")
_theorem_cache = {"mtime": None, "payload": None}
_theorem_lock = threading.Lock()


def read_kv(path):
    data = {}
    try:
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                key, sep, value = line.rstrip("\n").partition("=")
                if sep:
                    data[key.strip()] = value
    except OSError:
        pass
    return data


def tail_lines(path, limit):
    try:
        with open(path, "rb") as fh:
            fh.seek(0, os.SEEK_END)
            size = fh.tell()
            fh.seek(max(0, size - 65536))
            raw = fh.read()
    except OSError:
        return []
    lines = [ln.rstrip("\r") for ln in raw.decode("utf-8", "replace").splitlines()]
    return [ln for ln in lines if ln.strip()][-limit:]


def watchlist_addresses(config_dir):
    """Addresses from the site-local watchlist, so pf counts stay site-agnostic."""
    addresses = []
    try:
        with open(os.path.join(config_dir, "watchlist.conf"), "r", errors="replace") as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if line:
                    addresses.append(line.split()[0])
    except OSError:
        pass
    return addresses


def shaper_summary(path, watchlist=()):
    counts = {"scrub": 0, "dummynet": 0, "block": 0, "watchlist": 0, "pipes": 0}
    try:
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if line.startswith("scrub "):
                    counts["scrub"] += 1
                elif line.startswith("dummynet "):
                    counts["dummynet"] += 1
                elif line.startswith("block drop "):
                    counts["block"] += 1
                    if any(addr in line for addr in watchlist):
                        counts["watchlist"] += 1
                elif line.startswith("pipe "):
                    counts["pipes"] += 1
    except OSError:
        return None
    return counts


def applied_tcp_profile(state_dir, hotspot):
    """What the engine last applied; the file wins over the built-in table."""
    applied = read_kv(os.path.join(state_dir, "tcp-profile.env"))
    expected = {k: v for k, v in applied.items() if k.startswith(("net.", "kern."))}
    if expected:
        try:
            age = int(time.time() - os.path.getmtime(os.path.join(state_dir, "tcp-profile.env")))
        except OSError:
            age = None
        return expected, {
            "profile": applied.get("profile", "unknown"),
            "applied_ts": applied.get("applied_ts", ""),
            "age_sec": age,
            "source": "engine",
        }
    name = "hotspot" if hotspot else "home"
    return dict(TCP_PROFILES[name]), {
        "profile": name,
        "applied_ts": "",
        "age_sec": None,
        "source": "built-in fallback",
    }


def sysctl_values(state_dir, hotspot):
    expected, meta = applied_tcp_profile(state_dir, hotspot)
    names = list(expected)
    values = {}
    try:
        proc = subprocess.run(
            ["sysctl", "-n"] + names,
            capture_output=True, text=True, timeout=3,
        )
        if proc.returncode == 0:
            out = proc.stdout.split()
            if len(out) == len(names):
                values = dict(zip(names, out))
    except (OSError, subprocess.SubprocessError):
        pass
    if not values:
        for name in names:
            try:
                proc = subprocess.run(
                    ["sysctl", "-n", name],
                    capture_output=True, text=True, timeout=2,
                )
                if proc.returncode == 0:
                    values[name] = proc.stdout.strip()
            except (OSError, subprocess.SubprocessError):
                continue
    rows = [{"name": name, "value": values.get(name, ""), "expect": expect}
            for name, expect in expected.items()]
    return rows, meta


def computer_name():
    try:
        proc = subprocess.run(
            ["scutil", "--get", "ComputerName"],
            capture_output=True, text=True, timeout=2,
        )
        return proc.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return socket.gethostname()


def pcap_info():
    try:
        st = os.stat(AUDIT_PCAP)
    except OSError:
        return {"exists": False}
    return {
        "exists": True,
        "bytes": st.st_size,
        "age_sec": int(time.time() - st.st_mtime),
    }


def read_json_file(path):
    try:
        with open(path, "r", errors="replace") as fh:
            data = json.load(fh)
        data["file_age_sec"] = int(time.time() - os.path.getmtime(path))
        return data
    except (OSError, ValueError):
        return None


def read_state_file(path):
    try:
        with open(path, "r", errors="replace") as fh:
            kv = {}
            for line in fh:
                key, sep, value = line.strip().partition("=")
                if sep:
                    kv[key] = value
        kv["file_age_sec"] = int(time.time() - os.path.getmtime(path))
        return kv
    except OSError:
        return None


def theorem_catalog(spec_path):
    """Parse the Lean spec: named theorems, section headers, axiom declarations."""
    try:
        mtime = os.path.getmtime(spec_path)
    except OSError:
        return {"ok": False, "reason": "spec not found", "path": spec_path}
    if _theorem_cache["mtime"] == mtime and _theorem_cache["payload"] is not None:
        return _theorem_cache["payload"]

    with _theorem_lock:
        if _theorem_cache["mtime"] == mtime and _theorem_cache["payload"] is not None:
            return _theorem_cache["payload"]
        items, sections, axioms, section = [], [], 0, "preamble"
        try:
            with open(spec_path, "r", errors="replace") as fh:
                for lineno, line in enumerate(fh, 1):
                    sec = SECTION_RE.match(line.strip())
                    if sec:
                        section = sec.group(1)
                        continue
                    if line.lstrip().startswith("axiom "):
                        axioms += 1
                    t = THEOREM_RE.match(line)
                    if t:
                        name = t.group(1)
                        if section not in sections:
                            sections.append(section)
                        items.append({"name": name, "section": section, "line": lineno})
        except OSError:
            return {"ok": False, "reason": "spec unreadable", "path": spec_path}

        payload = {
            "ok": True,
            "path": spec_path,
            "count": len(items),
            "sections": sections,
            "axioms": axioms,
            "items": items,
        }
        _theorem_cache["mtime"] = mtime
        _theorem_cache["payload"] = payload
        return payload


def build_snapshot(state_dir, user_state_dir, config_dir):
    snap = read_kv(os.path.join(state_dir, "ui.snapshot"))
    if not snap:
        return {"ok": False, "reason": "ui.snapshot missing", "state_dir": state_dir,
                "host": computer_name(), "ts": int(time.time())}

    def num(key, default=0):
        try:
            return int(float(snap.get(key, default)))
        except (TypeError, ValueError):
            return default

    def flt(key, default=0.0):
        try:
            return float(snap.get(key, default))
        except (TypeError, ValueError):
            return default

    state_mtime = os.path.getmtime(os.path.join(state_dir, "ui.snapshot"))
    throttled = 0
    try:
        with open(os.path.join(state_dir, "throttled.pids"), "r") as fh:
            throttled = len([ln for ln in fh if ln.strip()])
    except OSError:
        throttle_entries = snap.get("THROTTLED_BG", "")
        throttled = int(throttle_entries) if throttle_entries.isdigit() else 0

    sysctl_rows, sysctl_meta = sysctl_values(state_dir, snap.get("IS_HOTSPOT", "0") == "1")

    return {
        "ok": True,
        "ts": int(time.time()),
        "host": computer_name(),
        "state_dir": state_dir,
        "snapshot_age_sec": int(time.time() - state_mtime),
        "mode": {
            "raw": snap.get("RAW_STATE", ""),
            "hotspot": snap.get("IS_HOTSPOT", "0") == "1",
            "paused": snap.get("IS_PAUSED", "0") == "1",
            "transport": snap.get("TRANSPORT", "unknown"),
            "device": snap.get("DEVICE", ""),
            "service": snap.get("SERVICE", ""),
            "ip": snap.get("IP", ""),
            "mtu": num("MTU"),
            "outer_mss": num("OUTER_MSS"),
            "overlay_mss": num("OVERLAY_MSS"),
            "delayed_ack": num("DELAYED_ACK"),
            "bg_qdelay": num("BG_QDELAY"),
            "awdl_up": snap.get("AWDL_UP", "0") == "1",
            "awdl_suppressed": num("AWDL_SUPPRESSED"),
            "throttled_bg": throttled,
            "wifi_off": snap.get("WIFI_OFF", "0") == "1",
        },
        "shaper": {
            "enabled": snap.get("SHAPE_ENABLED", "0") == "1",
            "down_mbps": num("DOWN_MBPS"),
            "up_mbps": num("UP_MBPS"),
            "eff_down_mbps": num("EFF_DOWN_MBPS"),
            "eff_up_mbps": num("EFF_UP_MBPS"),
            "autorate": {
                "delta_ms": num("AUTORATE_DELTA_MS"),
                "regime": snap.get("AUTORATE_REGIME", ""),
            },
            "taleb": {
                "alpha": flt("TAIL_ALPHA"),
                "n": num("INVGAMMA_N"),
                "shadow_mean_ms": flt("SHADOW_MEAN_MS"),
                "var99_ms": flt("TAIL_VAR99_MS"),
                "regime": snap.get("TAIL_REGIME", ""),
            },
            "costate": {"down_ms": num("COSTATE_DOWN_MS"), "up_ms": num("COSTATE_UP_MS")},
            "owd": {
                "down_ex_ms": num("OWD_DOWN_EX_MS"),
                "up_ex_ms": num("OWD_UP_EX_MS"),
                "mode": snap.get("OWD_MODE", ""),
            },
            "overlay_ifaces": snap.get("OVERLAY_IFACES", "").split(),
            "pf": shaper_summary(os.path.join(state_dir, "shaper.state"),
                                 watchlist_addresses(config_dir)),
        },
        "sysctl": sysctl_rows,
        "sysctl_profile": sysctl_meta,
        "pcap": pcap_info(),
        "audit": read_json_file(os.path.join(user_state_dir, "last-audit.json")),
        "verify": read_state_file(os.path.join(user_state_dir, "verify.state")),
        "log": tail_lines(os.path.join(state_dir, "tether-optimize.log"), LOG_LINES),
    }


def pf_rules(path, per_group_limit=1200):
    """Group the rules the engine actually loaded into the anchor."""
    groups = {"scrub": [], "dummynet": [], "block": [], "pipe": [], "other": []}
    try:
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                line = line.rstrip("\n")
                s = line.strip()
                if not s:
                    continue
                if s.startswith("scrub "):
                    key = "scrub"
                elif s.startswith("dummynet "):
                    key = "dummynet"
                elif s.startswith("block "):
                    key = "block"
                elif s.startswith("pipe "):
                    key = "pipe"
                else:
                    key = "other"
                groups[key].append(line)
    except OSError:
        return {"ok": False, "reason": "shaper.state unreadable"}
    groups["other"] = groups["other"][:40]
    truncated = {k: max(0, len(v) - per_group_limit) for k, v in groups.items()}
    return {
        "ok": True,
        "counts": {k: len(v) for k, v in groups.items()},
        "truncated": truncated,
        "groups": {k: v[:per_group_limit] for k, v in groups.items()},
    }


class Sampler:
    """Samples the daemon state on a fixed cadence so trends survive page reloads."""

    def __init__(self, state_dir, user_state_dir, config_dir, interval=2.0, capacity=450):
        self.state_dir = state_dir
        self.user_state_dir = user_state_dir
        self.config_dir = config_dir
        self.interval = interval
        self.lock = threading.Lock()
        self.latest = None
        self.series = deque(maxlen=capacity)
        self._stop = threading.Event()

    def _sample(self):
        try:
            snap = build_snapshot(self.state_dir, self.user_state_dir, self.config_dir)
        except Exception:
            return
        if not snap.get("ok"):
            # The daemon rewrites ui.snapshot several times a second; a single
            # failed read must not flip the dashboard to "offline".
            with self.lock:
                if self.latest is None:
                    self.latest = snap
            return
        sh = snap["shaper"]
        point = {
            "ts": snap["ts"],
            "u_down": sh["eff_down_mbps"],
            "u_up": sh["eff_up_mbps"],
            "cap_down": sh["down_mbps"],
            "cap_up": sh["up_mbps"],
            "lam_down": sh["costate"]["down_ms"],
            "lam_up": sh["costate"]["up_ms"],
            "owd_down": sh["owd"]["down_ex_ms"],
            "owd_up": sh["owd"]["up_ex_ms"],
            "alpha": sh["taleb"]["alpha"],
        }
        with self.lock:
            self.latest = snap
            self.series.append(point)

    def start(self):
        self._sample()

        def loop():
            while not self._stop.wait(self.interval):
                self._sample()

        threading.Thread(target=loop, daemon=True, name="tether-sampler").start()

    def snapshot(self):
        with self.lock:
            latest = self.latest
        if latest is None:
            return build_snapshot(self.state_dir, self.user_state_dir, self.config_dir)
        served = dict(latest)
        served["sampler_lag_sec"] = max(0, int(time.time() - latest["ts"]))
        return served

    def history(self):
        with self.lock:
            return list(self.series)


class Handler(BaseHTTPRequestHandler):
    server_version = "tether-workbench/1.1"
    sampler = None
    root = "."
    state_dir = "/usr/local/var/tether-optimize"
    user_state_dir = os.path.expanduser("~/.local/state/tether-optimize")
    config_dir = os.path.expanduser("~/.config/tether-optimize")
    spec_path = ""

    def log_message(self, fmt, *args):
        pass  # keep the terminal quiet; the daemon already logs to tether-optimize.log

    def _send(self, status, body, ctype="application/json; charset=utf-8"):
        payload = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(payload)

    def _json(self, payload, status=200):
        return self._send(status, json.dumps(payload))

    def _api_health(self):
        return self._json({"ok": True, "pid": os.getpid()})

    def _api_snapshot(self):
        try:
            snap = self.sampler.snapshot() if self.sampler else build_snapshot(self.state_dir, self.user_state_dir, self.config_dir)
        except Exception as exc:  # never take the server down over a read
            return self._json({"ok": False, "error": str(exc)}, 500)
        return self._json(snap)

    def _api_theorems(self):
        try:
            catalog = theorem_catalog(self.spec_path)
        except Exception as exc:
            catalog = {"ok": False, "error": str(exc)}
        return self._json(catalog)

    def _api_history(self):
        sampler = self.sampler
        return self._json({
            "ok": True,
            "interval_sec": sampler.interval if sampler else 2,
            "samples": sampler.history() if sampler else [],
        })

    def _api_rules(self):
        return self._json(pf_rules(os.path.join(self.state_dir, "shaper.state")))

    def routes(self):
        return {
            "/api/health": self._api_health,
            "/api/snapshot": self._api_snapshot,
            "/api/theorems": self._api_theorems,
            "/api/history": self._api_history,
            "/api/rules": self._api_rules,
        }

    def do_GET(self):
        path = urlparse(self.path).path
        route = self.routes().get(path)
        if route is not None:
            return route()
        return self._serve_static(unquote(path))

    def _serve_static(self, path):
        if path == "/":
            path = "/index.html"
        root = os.path.realpath(self.root)
        target = os.path.realpath(os.path.join(root, path.lstrip("/")))
        if not (target == root or target.startswith(root + os.sep)) or not os.path.isfile(target):
            return self._send(404, "Not found", "text/plain; charset=utf-8")
        ext = os.path.splitext(target)[1].lower()
        try:
            with open(target, "rb") as fh:
                body = fh.read()
        except OSError:
            return self._send(404, "Not readable", "text/plain; charset=utf-8")
        return self._send(200, body, CONTENT_TYPES.get(ext, "application/octet-stream"))


def main(argv):
    parser = argparse.ArgumentParser(description="Tether-Optimize live workbench server")
    parser.add_argument("--port", type=int, default=7180)
    parser.add_argument("--root", default=os.path.dirname(os.path.abspath(__file__)))
    parser.add_argument("--state-dir", default=os.environ.get("TETHER_STATE_DIR", "/usr/local/var/tether-optimize"))
    parser.add_argument("--user-state",
                        default=os.environ.get("TETHER_USER_STATE_DIR",
                                               os.path.expanduser("~/.local/state/tether-optimize")))
    parser.add_argument("--config-dir",
                        default=os.environ.get("TETHER_CONFIG_DIR",
                                               os.path.expanduser("~/.config/tether-optimize")))
    parser.add_argument("--spec", default="")
    args = parser.parse_args(argv)

    Handler.root = args.root
    Handler.state_dir = args.state_dir
    Handler.user_state_dir = args.user_state
    Handler.config_dir = args.config_dir
    if args.spec:
        Handler.spec_path = args.spec
    else:
        for candidate in (
            os.path.join(args.root, "..", "proofs", "TetherOptimizeSpec.lean"),
            os.path.join(args.root, "TetherOptimizeSpec.lean"),
        ):
            if os.path.isfile(candidate):
                Handler.spec_path = os.path.realpath(candidate)
                break
    if not os.path.isfile(os.path.join(args.root, "index.html")):
        print(f"error: no index.html under {args.root}", file=sys.stderr)
        return 2
    try:
        httpd = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    except OSError as exc:
        print(f"error: cannot bind 127.0.0.1:{args.port}: {exc}", file=sys.stderr)
        return 98
    print(f"tether workbench → http://127.0.0.1:{args.port}/  (state: {args.state_dir})", flush=True)
    Handler.sampler = Sampler(args.state_dir, args.user_state, args.config_dir)
    Handler.sampler.start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
