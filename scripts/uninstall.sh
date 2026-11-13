#!/usr/bin/env bash
# uninstall.sh — Clean uninstaller for Tether-Optimize v1.1.3
set -euo pipefail

TARGET_USER="${SUDO_USER:-$(stat -f%Su /dev/console 2>/dev/null || id -un)}"
[[ "$TARGET_USER" == "root" || "$TARGET_USER" == "loginwindow" ]] && TARGET_USER="$(id -un)"
USER_HOME="${TETHER_HOME:-/Users/${TARGET_USER}}"
BIN_DIR="${TETHER_BIN_DIR:-${USER_HOME}/bin}"
USER_UID=$(id -u "${TARGET_USER}")

echo "=== Uninstalling Tether-Optimize ==="
if [[ -x "${BIN_DIR}/tether-optimize" ]]; then
  "${BIN_DIR}/tether-optimize" menubar-stop || true
  "${BIN_DIR}/tether-optimize" restore || true
fi
launchctl bootout "gui/${USER_UID}/com.josaum.tether-menubar" 2>/dev/null || true
echo "✓ Tether-Optimize topbar stopped and Standard Home network profile restored."
