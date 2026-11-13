#!/usr/bin/env bash
# build-release.sh — Builds standalone macOS .pkg installer and portable release tarball in dist/
set -euo pipefail
export COPYFILE_DISABLE=1

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VERSION="1.1.5"
DIST_DIR="${REPO_ROOT}/dist"
STAGE_DIR="/tmp/tether-optimize-pkg-stage.$$"
PKG_ROOT="${STAGE_DIR}/root"
PKG_SCRIPTS="${STAGE_DIR}/scripts"

# Never ship local caches or site-local peer data
find "${REPO_ROOT}" -name __pycache__ -type d -prune -exec rm -rf {} + 2>/dev/null || true

rm -rf "${STAGE_DIR}"
mkdir -p "${DIST_DIR}" "${PKG_ROOT}/usr/local/share/tether-optimize" "${PKG_SCRIPTS}"

echo "=== Building Tether-Optimize v${VERSION} Release Artifacts ==="

# 1. Compile universal/native release binaries into staging tree
mkdir -p "${PKG_ROOT}/usr/local/share/tether-optimize/"{bin,src,proofs,wireshark,launchd,scripts,web,config,paper}
cp -R "${REPO_ROOT}/bin/"* "${PKG_ROOT}/usr/local/share/tether-optimize/bin/"
cp -R "${REPO_ROOT}/src/"* "${PKG_ROOT}/usr/local/share/tether-optimize/src/"
cp -R "${REPO_ROOT}/proofs/"* "${PKG_ROOT}/usr/local/share/tether-optimize/proofs/"
cp -R "${REPO_ROOT}/wireshark/"* "${PKG_ROOT}/usr/local/share/tether-optimize/wireshark/"
cp -R "${REPO_ROOT}/launchd/"* "${PKG_ROOT}/usr/local/share/tether-optimize/launchd/"
cp -R "${REPO_ROOT}/scripts/"* "${PKG_ROOT}/usr/local/share/tether-optimize/scripts/"
cp -R "${REPO_ROOT}/web/"* "${PKG_ROOT}/usr/local/share/tether-optimize/web/"
cp -R "${REPO_ROOT}/config/watchlist.conf" "${PKG_ROOT}/usr/local/share/tether-optimize/config/"
cp -R "${REPO_ROOT}/config/peers.example.lua" "${PKG_ROOT}/usr/local/share/tether-optimize/config/"
[[ -d "${REPO_ROOT}/paper" ]] && cp -R "${REPO_ROOT}/paper/"* "${PKG_ROOT}/usr/local/share/tether-optimize/paper/"
[[ -f "${REPO_ROOT}/README.md" ]] && cp "${REPO_ROOT}/README.md" "${PKG_ROOT}/usr/local/share/tether-optimize/README.md"
[[ -f "${REPO_ROOT}/Makefile" ]] && cp "${REPO_ROOT}/Makefile" "${PKG_ROOT}/usr/local/share/tether-optimize/Makefile"

swiftc -O -o "${PKG_ROOT}/usr/local/share/tether-optimize/bin/tether-events" "${REPO_ROOT}/src/tether-events.swift"
chmod 755 "${PKG_ROOT}/usr/local/share/tether-optimize/bin/tether-events" \
          "${PKG_ROOT}/usr/local/share/tether-optimize/bin/tether-optimize" \
          "${PKG_ROOT}/usr/local/share/tether-optimize/scripts/"*.sh
xattr -cr "${STAGE_DIR}" 2>/dev/null || true
find "${STAGE_DIR}" -name '._*' -delete 2>/dev/null || true

# 2. Create postinstall script for macOS Installer.app / installer(8)
cat > "${PKG_SCRIPTS}/postinstall" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ -x /usr/local/share/tether-optimize/scripts/install.sh ]]; then
  /usr/local/share/tether-optimize/scripts/install.sh
fi
EOF
chmod 755 "${PKG_SCRIPTS}/postinstall"

# 3. Build macOS .pkg via native pkgbuild
PKG_FILE="${DIST_DIR}/TetherOptimize-${VERSION}-macos-arm64.pkg"
pkgbuild \
  --root "${PKG_ROOT}" \
  --scripts "${PKG_SCRIPTS}" \
  --identifier "com.josaum.tether-optimize.pkg" \
  --version "${VERSION}" \
  --install-location "/" \
  "${PKG_FILE}" >/dev/null

# 4. Build portable .tar.gz archive
TAR_FILE="${DIST_DIR}/TetherOptimize-${VERSION}-macos-arm64.tar.gz"
tar -C "${PKG_ROOT}/usr/local/share" -czf "${TAR_FILE}" tether-optimize

# 5. Generate SHA-256 checksum manifest
(cd "${DIST_DIR}" && shasum -a 256 "TetherOptimize-${VERSION}-macos-arm64.pkg" "TetherOptimize-${VERSION}-macos-arm64.tar.gz" > SHA256SUMS.txt)

rm -rf "${STAGE_DIR}"
echo "✓ Built macOS Installer Package : ${PKG_FILE}"
echo "✓ Built Portable Release Archive: ${TAR_FILE}"
echo "✓ SHA-256 Manifest              : ${DIST_DIR}/SHA256SUMS.txt"
cat "${DIST_DIR}/SHA256SUMS.txt"
