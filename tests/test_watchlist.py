"""Tests for the site-local peer watchlist and the no-personal-data guard.

The guard test is the regression test for the 2026-11-12 finding that the public
engine and Wireshark plugin shipped a real household's addresses, hostnames and
hardware addresses as firewall policy.
"""

import os
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(ROOT, "bin", "tether-optimize")

# Anything resembling a real home/lab network must stay out of shipped files.
PERSONAL_PATTERNS = [
    r"192\.168\.3\.",
    r"192\.168\.15\.",
    r"100\.104\.150\.111",
    r"\bfd04:907d:",
    r"b4:e9:b8:fb:7c:1d",
    r"7c:4b:26:40:1c:1f",
    r"68:d7:9a:2f:7b:8e",
    r"04:bf:d5:50:40:a4",
    r"ea:d7:10:a0:14:d2",
    r"(?i)demetrios",
    r"(?i)lili-ursa",
    r"(?i)imac-de-lilian",
    r"(?i)sounio-language-macbook",
    r"(?i)mycelia-waha",
    r"(?i)waha-iap",
    r"(?i)jquant",
    r"(?i)litellm",
    r"(?i)leio-embed",
    r"(?i)central-tether",
    r"(?i)ts-webhook",
    r"/Users/josaum",
    r"/home/josaum",
]

SHIPPED_FILES = [
    "bin/tether-optimize",
    "web/serve.py",
    "web/index.html",
    "web/static/app.js",
    "web/static/app.css",
    "wireshark/tether_optimize.lua",
    "config/watchlist.conf",
    "config/peers.example.lua",
    "scripts/install.sh",
    "src/tether-menubar.swift",
    "src/tether-events.swift",
    "proofs/TetherOptimizeSpec.lean",
]


def run_emit(watchlist_path):
    env = dict(os.environ, TETHER_WATCHLIST=watchlist_path)
    proc = subprocess.run([ENGINE, "__emit_rules", "1380"], capture_output=True, text=True, env=env)
    if proc.returncode != 0:
        raise AssertionError(f"__emit_rules failed: {proc.stderr}")
    return proc.stdout


class ShippedFilesGuardTest(unittest.TestCase):
    def test_no_personal_network_data_in_shipped_files(self):
        offenders = []
        for rel in SHIPPED_FILES:
            path = os.path.join(ROOT, rel)
            with open(path, encoding="utf-8", errors="replace") as fh:
                for lineno, line in enumerate(fh, 1):
                    for pattern in PERSONAL_PATTERNS:
                        if re.search(pattern, line):
                            offenders.append(f"{rel}:{lineno}: {line.strip()[:90]}")
        self.assertEqual(offenders, [], "personal network data in shipped files:\n" + "\n".join(offenders))

    def test_local_overrides_are_gitignored(self):
        with open(os.path.join(ROOT, ".gitignore"), encoding="utf-8") as fh:
            ignore = fh.read()
        self.assertIn("config/*.local.conf", ignore)
        self.assertIn("config/*.local.lua", ignore)


class WatchlistRulesTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write_watchlist(self, body):
        path = os.path.join(self.tmp, "watchlist.conf")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(body)
        return path

    def test_empty_watchlist_emits_no_peer_rules(self):
        out = run_emit(os.path.join(ROOT, "config", "watchlist.conf"))
        self.assertNotIn("block drop in quick inet from {", out)
        self.assertIn("port { 3000, 7100, 8787, 11434 }", out)

    def test_both_direction_addresses_are_grouped_per_family(self):
        path = self.write_watchlist("192.0.2.10\n192.0.2.11\n2001:db8::1\n")
        out = run_emit(path)
        self.assertIn("block drop in quick inet from { 192.0.2.10, 192.0.2.11 } to any", out)
        self.assertIn("block drop out quick inet from any to { 192.0.2.10, 192.0.2.11 }", out)
        self.assertIn("block drop in quick inet6 from { 2001:db8::1 } to any", out)

    def test_direction_and_protocol_modifiers(self):
        path = self.write_watchlist(
            "198.51.100.5 in udp\n"
            "203.0.113.7 in tcp syn\n"
            "203.0.113.8 out tcp\n"
            "203.0.113.9 in icmp\n"
        )
        out = run_emit(path)
        self.assertIn("block drop in quick inet proto udp from 198.51.100.5 to any", out)
        self.assertIn("block drop in quick inet proto tcp from 203.0.113.7 to any flags S/SA", out)
        self.assertIn("block drop out quick inet proto tcp from any to 203.0.113.8", out)
        self.assertIn("block drop in quick inet proto icmp from 203.0.113.9 to any icmp-type echoreq", out)

    def test_both_with_protocol_expands_to_in_and_out(self):
        path = self.write_watchlist("198.51.100.5 both udp\n203.0.113.7 both tcp syn\n")
        out = run_emit(path)
        self.assertIn("block drop in quick inet proto udp from 198.51.100.5 to any", out)
        self.assertIn("block drop out quick inet proto udp from any to 198.51.100.5", out)
        self.assertIn("block drop in quick inet proto tcp from 203.0.113.7 to any flags S/SA", out)
        self.assertIn("block drop out quick inet proto tcp from any to 203.0.113.7 flags S/SA", out)
        self.assertNotIn("block drop both ", out)

    def test_comments_and_blank_lines_are_ignored(self):
        path = self.write_watchlist("# comment\n\n192.0.2.20  # trailing note\n")
        out = run_emit(path)
        self.assertIn("192.0.2.20", out)
        self.assertNotIn("comment", out)

    def test_watchlist_command_reports_entries(self):
        path = self.write_watchlist("192.0.2.30 in udp\n")
        env = dict(os.environ, TETHER_WATCHLIST=path)
        proc = subprocess.run([ENGINE, "watchlist"], capture_output=True, text=True, env=env)
        self.assertEqual(proc.returncode, 0)
        self.assertIn("1 entry", proc.stdout)
        self.assertIn("192.0.2.30", proc.stdout)
        self.assertIn("proto udp", proc.stdout)


if __name__ == "__main__":
    unittest.main()
