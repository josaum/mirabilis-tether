#!/usr/bin/env bash
# install.sh — Zero-dependency macOS installer for Tether-Optimize v1.1.3
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TARGET_USER="${SUDO_USER:-$(stat -f%Su /dev/console 2>/dev/null || id -un)}"
[[ "$TARGET_USER" == "root" || "$TARGET_USER" == "loginwindow" ]] && TARGET_USER="$(id -un)"
USER_HOME="${TETHER_HOME:-/Users/${TARGET_USER}}"
BIN_DIR="${TETHER_BIN_DIR:-${USER_HOME}/bin}"
APP_DIR="${USER_HOME}/Applications/TetherMenubar.app"
WIRESHARK_PLUGIN_DIR="${USER_HOME}/.local/lib/wireshark/plugins"
LAUNCH_AGENT_DIR="${USER_HOME}/Library/LaunchAgents"

echo "=== Installing Tether-Optimize v1.1.3 ==="
echo "  Target User : ${TARGET_USER} (${USER_HOME})"
echo "  Binary Dir  : ${BIN_DIR}"
echo "  Menubar App : ${APP_DIR}"

mkdir -p "${BIN_DIR}" "${APP_DIR}/Contents/MacOS" "${APP_DIR}/Contents/Resources" "${WIRESHARK_PLUGIN_DIR}" "${LAUNCH_AGENT_DIR}"

# 1. Stage source & formal specification atomically via /tmp (works even when target files are root-locked 644)
cp -f "${REPO_ROOT}/src/tether-events.swift" "/tmp/tether-events.swift.$$"
chmod 644 "/tmp/tether-events.swift.$$"
mv -f "/tmp/tether-events.swift.$$" "${BIN_DIR}/tether-events.swift"

cp -f "${REPO_ROOT}/src/tether-menubar.swift" "/tmp/tether-menubar.swift.$$"
chmod 644 "/tmp/tether-menubar.swift.$$"
mv -f "/tmp/tether-menubar.swift.$$" "${BIN_DIR}/tether-menubar.swift"

cp -f "${REPO_ROOT}/proofs/TetherOptimizeSpec.lean" "/tmp/TetherOptimizeSpec.lean.$$"
chmod 644 "/tmp/TetherOptimizeSpec.lean.$$"
mv -f "/tmp/TetherOptimizeSpec.lean.$$" "${BIN_DIR}/TetherOptimizeSpec.lean"

cp -f "${REPO_ROOT}/wireshark/tether_optimize.lua" "${WIRESHARK_PLUGIN_DIR}/tether_optimize.lua"

# 1b. Web workbench: page, static assets and loopback telemetry server in the product tree
stage_asset() {  # stage in /tmp first so a root-owned previous copy can be replaced
  local src="$1" dest="$2" tmp
  tmp="/tmp/tether-web-$(basename "$dest").$$"
  cp -f "$src" "$tmp"
  chmod 644 "$tmp"
  mv -f "$tmp" "$dest"
}

WEB_TARGET_DIR="${USER_HOME}/tether-optimize/web"
mkdir -p "${WEB_TARGET_DIR}/static"
stage_asset "${REPO_ROOT}/web/index.html"      "${WEB_TARGET_DIR}/index.html"
stage_asset "${REPO_ROOT}/web/serve.py"        "${WEB_TARGET_DIR}/serve.py"
stage_asset "${REPO_ROOT}/web/static/app.css"  "${WEB_TARGET_DIR}/static/app.css"
stage_asset "${REPO_ROOT}/web/static/app.js"   "${WEB_TARGET_DIR}/static/app.js"
chmod 755 "${WEB_TARGET_DIR}/serve.py"

# 1c. Site-local peer data: ship the empty watchlist template once, then respect
#     the operator's own file; local peer labels go next to the Lua plugin.
CONFIG_TARGET_DIR="${USER_HOME}/.config/tether-optimize"
mkdir -p "${CONFIG_TARGET_DIR}"
if [[ ! -f "${CONFIG_TARGET_DIR}/watchlist.conf" ]]; then
  stage_asset "${REPO_ROOT}/config/watchlist.conf" "${CONFIG_TARGET_DIR}/watchlist.conf"
fi
if [[ -f "${REPO_ROOT}/config/watchlist.local.conf" ]]; then
  stage_asset "${REPO_ROOT}/config/watchlist.local.conf" "${CONFIG_TARGET_DIR}/watchlist.conf"
fi
if [[ -f "${REPO_ROOT}/config/peers.local.lua" ]]; then
  stage_asset "${REPO_ROOT}/config/peers.local.lua" "${WIRESHARK_PLUGIN_DIR}/tether_peers.lua"
fi

# 2. Compile native ARM64/x86_64 binaries via Apple Command Line Tools swiftc
echo "  Compiling tether-events (XNU kqueue + PF_ROUTE + BSD IPPROTO_ICMP OWD reactor)…"
swiftc -O -o "/tmp/tether-events.$$" "${REPO_ROOT}/src/tether-events.swift"
chmod 755 "/tmp/tether-events.$$"
mv -f "/tmp/tether-events.$$" "${BIN_DIR}/tether-events"

echo "  Compiling TetherMenubar.app (Native Cocoa Menu Bar Widget)…"
cat > "${APP_DIR}/Contents/Info.plist" <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleExecutable</key>
  <string>tether-menubar</string>
  <key>CFBundleIdentifier</key>
  <string>com.josaum.tether-menubar</string>
  <key>CFBundleName</key>
  <string>TetherMenubar</string>
  <key>CFBundlePackageType</key>
  <string>APPL</string>
  <key>CFBundleShortVersionString</key>
  <string>1.1.3</string>
  <key>CFBundleVersion</key>
  <string>100</string>
  <key>LSUIElement</key>
  <true/>
  <key>NSHighResolutionCapable</key>
  <true/>
</dict>
</plist>
EOF
swiftc -O -o "${APP_DIR}/Contents/MacOS/tether-menubar.new" "${REPO_ROOT}/src/tether-menubar.swift" -framework Cocoa
chmod 755 "${APP_DIR}/Contents/MacOS/tether-menubar.new"
mv -f "${APP_DIR}/Contents/MacOS/tether-menubar.new" "${APP_DIR}/Contents/MacOS/tether-menubar"
ln -sf "${APP_DIR}/Contents/MacOS/tether-menubar" "${BIN_DIR}/tether-menubar"

# 3. Install LaunchAgent for TetherMenubar.app
sed -e "s|__USER_HOME__|${USER_HOME}|g" -e "s|__BIN_DIR__|${BIN_DIR}|g" \
  "${REPO_ROOT}/launchd/com.josaum.tether-menubar.plist.in" > "${LAUNCH_AGENT_DIR}/com.josaum.tether-menubar.plist"

# 4. Atomically stage tether-optimize (triggers hot-reload if LaunchDaemon is already active)
cp -f "${REPO_ROOT}/bin/tether-optimize" "/tmp/tether-optimize.$$"
chmod 755 "/tmp/tether-optimize.$$"
mv -f "/tmp/tether-optimize.$$" "${BIN_DIR}/tether-optimize"

# 5. Restart TetherMenubar LaunchAgent
USER_UID=$(id -u "${TARGET_USER}")
launchctl bootout "gui/${USER_UID}/com.josaum.tether-menubar" 2>/dev/null || true
launchctl bootstrap "gui/${USER_UID}" "${LAUNCH_AGENT_DIR}/com.josaum.tether-menubar.plist" 2>/dev/null || true
launchctl kickstart -k "gui/${USER_UID}/com.josaum.tether-menubar" 2>/dev/null || true

echo "✓ Tether-Optimize v1.1.3 installed."
echo "  Run '${BIN_DIR}/tether-optimize doctor' or '${BIN_DIR}/tether-optimize verify' to verify."
