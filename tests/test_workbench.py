"""Unit tests for the workbench server's parsers and state assembly."""

import importlib.util
import os
import tempfile
import time
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, "web", "serve.py")

spec = importlib.util.spec_from_file_location("tether_serve", SPEC)
serve = importlib.util.module_from_spec(spec)
spec.loader.exec_module(serve)


class TheoremCatalogTest(unittest.TestCase):
    def test_parses_counts_sections_and_axioms(self):
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
            fh.write(
                "/-! ## 1. First section -/\n"
                "theorem alpha : True := trivial\n"
                "theorem beta_one : True := trivial\n"
                "/-! ## 2. Second section (0 Axioms):\n"
                "-/\n"
                "axiom bogus : False\n"
                "theorem gamma : True := trivial\n"
            )
            path = fh.name
        try:
            catalog = serve.theorem_catalog(path)
            self.assertTrue(catalog["ok"])
            self.assertEqual(catalog["count"], 3)
            self.assertEqual(catalog["axioms"], 1)
            self.assertEqual(catalog["sections"][0], "1. First section")
            self.assertEqual(catalog["sections"][1], "2. Second section (0 Axioms):")
            self.assertEqual(catalog["items"][0]["name"], "alpha")
            self.assertEqual(catalog["items"][0]["line"], 2)
        finally:
            os.unlink(path)

    def test_missing_spec_is_reported_not_raised(self):
        catalog = serve.theorem_catalog("/nonexistent/spec.lean")
        self.assertFalse(catalog["ok"])


class PfRulesTest(unittest.TestCase):
    def test_groups_rules_from_the_anchor_dump(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as fh:
            fh.write(
                "scrub on en0 inet all max-mss 1380 fragment reassemble\n"
                "dummynet out on en0 all pipe 10\n"
                "block drop in quick on ! lo0 proto tcp from any to any port = 3000\n"
                "pipe 10 bandwidth 10Mbit/s queue 96\n"
                "some header line\n"
            )
            path = fh.name
        try:
            rules = serve.pf_rules(path)
            self.assertTrue(rules["ok"])
            self.assertEqual(rules["counts"]["scrub"], 1)
            self.assertEqual(rules["counts"]["dummynet"], 1)
            self.assertEqual(rules["counts"]["block"], 1)
            self.assertEqual(rules["counts"]["pipe"], 1)
            self.assertIn("other", rules["groups"])
        finally:
            os.unlink(path)

    def test_unreadable_state_is_reported(self):
        self.assertFalse(serve.pf_rules("/nonexistent/shaper.state")["ok"])


class TcpProfileTest(unittest.TestCase):
    def test_engine_file_wins_over_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, "tcp-profile.env"), "w") as fh:
                fh.write(
                    "profile=hotspot\n"
                    f"applied_ts={int(time.time())}\n"
                    "net.inet.tcp.sendspace=65536\n"
                    "net.inet.tcp.bg_target_qdelay=15\n"
                )
            expected, meta = serve.applied_tcp_profile(tmp, hotspot=False)
            self.assertEqual(meta["source"], "engine")
            self.assertEqual(meta["profile"], "hotspot")
            self.assertEqual(expected["net.inet.tcp.sendspace"], "65536")
            self.assertIsNotNone(meta["age_sec"])

    def test_fallback_tracks_detected_mode(self):
        with tempfile.TemporaryDirectory() as tmp:
            home_expected, home_meta = serve.applied_tcp_profile(tmp, hotspot=False)
            hot_expected, hot_meta = serve.applied_tcp_profile(tmp, hotspot=True)
            self.assertEqual(home_meta["profile"], "home")
            self.assertEqual(hot_meta["profile"], "hotspot")
            self.assertEqual(home_expected["net.inet.tcp.mssdflt"], "1452")
            self.assertEqual(hot_expected["net.inet.tcp.mssdflt"], "1380")
            self.assertEqual(home_expected["net.inet.tcp.bg_target_qdelay"], "20")
            self.assertEqual(hot_expected["net.inet.tcp.bg_target_qdelay"], "15")


class StateFileTest(unittest.TestCase):
    def test_verify_state_parses_line_per_pair(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as fh:
            fh.write("ok=1\npassed=110\ntotal=110\nts=1762500000\nspec=TetherOptimizeSpec.lean\nlean=lean\n")
            path = fh.name
        try:
            state = serve.read_state_file(path)
            self.assertEqual(state["ok"], "1")
            self.assertEqual(state["passed"], "110")
            self.assertEqual(state["lean"], "lean")
        finally:
            os.unlink(path)

    def test_missing_state_file_returns_none(self):
        self.assertIsNone(serve.read_state_file("/nonexistent/verify.state"))

    def test_log_tail_keeps_last_lines(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as fh:
            fh.write("\n".join(f"line {i}" for i in range(60)) + "\n\n")
            path = fh.name
        try:
            lines = serve.tail_lines(path, 5)
            self.assertEqual(lines[-1], "line 59")
            self.assertEqual(len(lines), 5)
        finally:
            os.unlink(path)


class SnapshotTest(unittest.TestCase):
    def test_missing_ui_snapshot_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            snap = serve.build_snapshot(tmp, tmp, tmp)
            self.assertFalse(snap["ok"])
            self.assertIn("reason", snap)

    def test_snapshot_carries_audit_verify_and_profile_meta(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, "ui.snapshot"), "w") as fh:
                fh.write(
                    "RAW_STATE=down:en0|Wi-Fi|192.0.2.9\n"
                    "IS_HOTSPOT=1\nIS_PAUSED=0\nTRANSPORT=wifi\nDEVICE=en0\nSERVICE=Wi-Fi\n"
                    "IP=172.20.10.2\nMTU=1420\nOUTER_MSS=1380\nOVERLAY_MSS=1220\n"
                    "DOWN_MBPS=100\nUP_MBPS=30\nEFF_DOWN_MBPS=42\nEFF_UP_MBPS=9\n"
                    "SHAPE_ENABLED=1\nAUTORATE_DELTA_MS=6\nAUTORATE_REGIME=drained\n"
                    "TAIL_ALPHA=0.56\nINVGAMMA_N=16\nSHADOW_MEAN_MS=55.8\nTAIL_VAR99_MS=78171.5\n"
                    "TAIL_REGIME=inf_mean\nCOSTATE_DOWN_MS=20\nCOSTATE_UP_MS=57\n"
                    "OWD_DOWN_EX_MS=6\nOWD_UP_EX_MS=6\nOWD_MODE=rtt\nOVERLAY_IFACES=utun4 feth110\n"
                )
            with open(os.path.join(tmp, "last-audit.json"), "w") as fh:
                fh.write('{"ts": 1, "packets": 10, "max_l3": 1420, "mtu_ceiling": 1420}')
            with open(os.path.join(tmp, "verify.state"), "w") as fh:
                fh.write("ok=1\npassed=110\ntotal=110\nts=1762500000\n")

            snap = serve.build_snapshot(tmp, tmp, tmp)
            self.assertTrue(snap["ok"])
            self.assertEqual(snap["mode"]["device"], "en0")
            self.assertTrue(snap["mode"]["hotspot"])
            self.assertEqual(snap["shaper"]["eff_down_mbps"], 42)
            self.assertEqual(len(snap["shaper"]["overlay_ifaces"]), 2)
            self.assertEqual(snap["audit"]["packets"], 10)
            self.assertEqual(snap["verify"]["passed"], "110")
            self.assertEqual(snap["sysctl_profile"]["profile"], "hotspot")
            self.assertTrue(all("expect" in row for row in snap["sysctl"]))


if __name__ == "__main__":
    unittest.main()
