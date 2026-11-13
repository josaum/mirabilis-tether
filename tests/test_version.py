"""The version is hand-stamped in nine files; this test fails when any one drifts.

Same class of bug as the assertion count (72/85) that drifted before it was
guarded — the release version must be identical everywhere a user or the build
system can read it.
"""

import os
import re
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def engine_version():
    with open(os.path.join(ROOT, "bin", "tether-optimize"), encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r'^VERSION="(.+)"$', line.strip())
            if m:
                return m.group(1)
    raise AssertionError("VERSION= not found in bin/tether-optimize")


class VersionConsistencyTest(unittest.TestCase):
    def test_version_is_stamped_consistently(self):
        version = engine_version()
        self.assertRegex(version, r"^\d+\.\d+\.\d+$", "unexpected version shape")

        # Every other stamped site must mention the exact same version string.
        sites = {
            "Makefile": ["Makefile"],
            "CITATION.cff": ["CITATION.cff"],
            ".zenodo.json": [".zenodo.json"],
            "README.md": ["README.md"],
            "scripts/install.sh": ["scripts/install.sh"],
            "scripts/uninstall.sh": ["scripts/uninstall.sh"],
            "scripts/build-release.sh": ["scripts/build-release.sh"],
            "web/index.html": ["web/index.html"],
        }
        missing = []
        for name, rel in sites.items():
            path = os.path.join(ROOT, rel[0])
            with open(path, encoding="utf-8", errors="replace") as fh:
                content = fh.read()
            if version not in content:
                missing.append(name)
        self.assertEqual(missing, [], f"version {version} not found in: {missing}")

    def test_dist_artifacts_match_version(self):
        version = engine_version()
        dist = os.path.join(ROOT, "dist")
        expected = [
            f"TetherOptimize-{version}-macos-arm64.pkg",
            f"TetherOptimize-{version}-macos-arm64.tar.gz",
        ]
        for name in expected:
            self.assertTrue(
                os.path.isfile(os.path.join(dist, name)),
                f"missing release artifact {name}",
            )
        # Superseded artifacts must not linger alongside the current release.
        stale = [
            f
            for f in os.listdir(dist)
            if f.startswith("TetherOptimize-") and f.endswith((".pkg", ".tar.gz"))
            and not f.startswith(f"TetherOptimize-{version}-")
        ]
        self.assertEqual(stale, [], f"stale dist artifacts present: {stale}")


if __name__ == "__main__":
    unittest.main()
