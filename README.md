# Mirabilis-Tether (`tether-optimize` v1.0.0)
### *Mirabilis Abbreviatio* — Formally Verified macOS Personal Hotspot & WAN Optimizer

[![Lean 4 Kernel Verified](https://img.shields.io/badge/Lean_4-110_Theorems_(0_Axioms)-3fb950)](proofs/TetherOptimizeSpec.lean)
[![Live Assertions](https://img.shields.io/badge/Live_Assertions-72%2F72_Passing-58a6ff)](bin/tether-optimize)
[![macOS Platform](https://img.shields.io/badge/macOS-Apple_Silicon_%26_XNU-bc8cff)](https://github.com/josaum/mirabilis-tether)

**Mirabilis-Tether** (`tether-optimize`) is an event-driven macOS kernel optimization product and native Menu Bar suite that eliminates cellular baseband bufferbloat, Wi-Fi `awdl0` channel-hopping stutters, GTP-U/CLAT46 packet fragmentation, and background sync saturation when tethered to an iPhone, iPad, or Android Personal Hotspot (over Wi-Fi `en0` or USB `en7`/`en17`), while automatically restoring unshaped PPPoE-safe Gigabit Home Wi-Fi/LAN settings on disconnect.

Every control law, state transition, packet-size bound, and statistical estimator is machine-verified in **110 zero-axiom constructive Lean 4 theorems** ([`proofs/TetherOptimizeSpec.lean`](proofs/TetherOptimizeSpec.lean)) and continuously validated by **72 live system & unit assertions** (`tether-optimize test`).

---

## 1. Architecture & Mathematical Stack

| Layer | Component | Mechanism & Formal Guarantee |
| :--- | :--- | :--- |
| **1. Event-Driven XNU Reactor** | [`src/tether-events.swift`](src/tether-events.swift) | `AF_ROUTE` raw kernel socket + `kqueue` (`EVFILT_VNODE`, `EVFILT_TIMER`, `EVFILT_PROC`) + zero-fork 64-bit `NET_RT_IFLIST2` byte counters. `0` radio probes in idle (`<16 KB/s`, `3000 ms` sleep); `500 ms` fast control under load (**Theorem 110**). |
| **2. Clock-Offset-Cancelled OWD Quorum** | [`src/tether-events.swift`](src/tether-events.swift) | Parallel BSD `SOCK_DGRAM` `IPPROTO_ICMP` 3-reflector quorum (`9.9.9.9` & `149.112.112.112` RFC 792 Type 13/14 Timestamp + `1.1.1.1` Type 8/0 Echo). Cancels arbitrary host-reflector clock offset $\theta \in \mathbb{Z}$ (**Theorem 106**) and rejects single-reflector glitches via Birkhoff distributive `median3` (**Theorem 107**). |
| **3. Taleb Fat-Tail Estimation** | [`bin/tether-optimize`](bin/tether-optimize) | Models Pareto/Lomax tail index $\widehat{\alpha}_{\text{MLE}} \sim \text{InvGamma}(n, n\alpha)$, applies exact $\frac{n-1}{n}$ small-sample debiasing $\widehat{\alpha}_0 = \frac{n-1}{S_n}$, and computes the Cirillo–Taleb Shadow Mean across $\alpha \le 1$ (**Theorems 96–100**). |
| **4. Pontryagin Hamiltonian Control** | [`bin/tether-optimize`](bin/tether-optimize) | Maximizes the discrete Kelly–Pontryagin Hamiltonian $\mathcal{H}(q, u, -\lambda) = U_W(u) + \lambda(u_{\max} - u)$ via Galois floor-division duality $u^\star(\lambda) = \operatorname{clamp}_{[u_{\min}, u_{\max}]}(\lfloor W/\lambda \rfloor)$ (**Theorems 101–105**) with 1-step revealed-capacity fade capture $\lambda_{\text{cap}}(W, \hat{r}) = \lfloor W/(\hat{r}+1)\rfloor + 1$ (**Theorem 108**). |
| **5. Dual PF Scrub & BDP-Isochronous GRED** | [`bin/tether-optimize`](bin/tether-optimize) | Enforces outer MSS (`1380 B` Hotspot / `1452 B` Home IPv4 / `1432 B` Home IPv6), inner VPN `utun*` MSS (`1220 B` Hotspot / `1332 B` Home), and rate-adaptive CoDel/GRED dummynet queues (**Theorems 13–28, 93, 109**). |
| **6. Native macOS Menu Bar App** | [`src/tether-menubar.swift`](src/tether-menubar.swift) | `TetherMenubar.app` (`LSUIElement` Cocoa app) watching `/usr/local/var/tether-optimize/ui.snapshot` via `EVFILT_VNODE` with zero main-thread blocking. |
| **7. Wireshark Lua Post-Dissector** | [`wireshark/tether_optimize.lua`](wireshark/tether_optimize.lua) | Registers `tether.l3_len`, `tether.syn_mss`, `tether.syn_ecn`, `tether.fast_lane`, `tether.ecn`, and `tether.icmp_owd` for 1-command header-only wire audits (`tether-optimize pcap`). |

---

## 2. Repository Layout

```text
tether-optimize/
├── Makefile                                  # Build, verify, test, and .pkg release targets
├── README.md                                 # Product architecture & operational runbook
├── bin/
│   └── tether-optimize                       # Portable CLI & root daemon engine (v1.0.0)
├── src/
│   ├── tether-events.swift                   # XNU kqueue + PF_ROUTE + RFC 792 OWD reactor
│   └── tether-menubar.swift                  # Native macOS Cocoa Menu Bar application
├── proofs/
│   └── TetherOptimizeSpec.lean               # 110 zero-axiom constructive Lean 4 theorems
├── wireshark/
│   └── tether_optimize.lua                   # Wireshark Lua post-dissector (incl. RFC 792 OWD)
├── launchd/
│   ├── com.josaum.tether-optimize.plist.in   # Root LaunchDaemon template
│   └── com.josaum.tether-menubar.plist.in    # User LaunchAgent template
├── scripts/
│   ├── install.sh                            # Zero-dependency macOS installer
│   ├── uninstall.sh                          # Clean uninstaller & profile restorer
│   └── build-release.sh                      # Builds macOS .pkg + .tar.gz + SHA256SUMS.txt
├── web/
│   └── index.html                            # Interactive Product Landing Page & Hamiltonian Workbench
└── dist/
    ├── TetherOptimize-1.0.0-macos-arm64.pkg
    ├── TetherOptimize-1.0.0-macos-arm64.tar.gz
    └── SHA256SUMS.txt
```

---

## 3. Quick Start & CLI Reference

### Install or Upgrade

```bash
git clone https://github.com/josaum/mirabilis-tether.git ~/tether-optimize
cd ~/tether-optimize
./scripts/install.sh
```

### Everyday Commands

```bash
tether-optimize status          # Concise status (link, Pontryagin u*(λ), OWD, Taleb α̂₀, TCP, VPNs)
tether-optimize doctor          # Full environment & component readiness diagnostic
tether-optimize version         # Show product version & paths
tether-optimize web             # Open interactive Product Landing Page & Hamiltonian Workbench
tether-optimize owd-probe       # Run live 3-reflector RFC 792 One-Way Delay quorum probe
tether-optimize tail-mle        # Run Taleb InvGamma(n, nα) MLE & Pontryagin control diagnostic
tether-optimize pcap 4          # Run 4s header-only Wireshark (dumpcap/tshark/Lua) wire audit
tether-optimize cap 40 12       # Live-update hotspot ceiling to 40 Mbps down / 12 Mbps up
tether-optimize unshape         # Disable dummynet bandwidth cap (keep TCP/MSS/AWDL/QoS)
tether-optimize shape           # Re-enable dummynet bandwidth cap
tether-optimize restore         # Force Standard Home Wi-Fi / LAN profile
tether-optimize verify          # Run all 110 Lean 4 proofs + 72 live system assertions
```

---

## 4. Verification & Reproducibility

To independently verify the entire mathematical specification and live kernel invariants without consulting the author:

1. **Formal Proof Check (`0` axioms, `0` external imports)**:
   ```bash
   tether-optimize verify-lean
   ```
   Expected output: `All 110 tether-optimize formal specification theorems verified (0 axioms).`

2. **Live System & Unit Invariant Suite**:
   ```bash
   tether-optimize test
   ```
   Expected output: `✓ 72/72 live system & unit assertions passed (0 failed)`

3. **Distributable Package Build**:
   ```bash
   make pkg
   ```
   Produces `dist/TetherOptimize-1.0.0-macos-arm64.pkg`, `dist/TetherOptimize-1.0.0-macos-arm64.tar.gz`, and `dist/SHA256SUMS.txt`.

---

## 5. Exception Handling & Recovery Boundaries

- **Unplugged or Flapping USB Cable**: Debounced across `1.5s` transient USB resets (`watch_loop`) and guarded by `iface_exists` before touching `networksetup` or `ifconfig`.
- **ICMP Timestamp Filtered by Carrier**: If a cellular carrier strips RFC 792 Type 13/14 messages or returns non-conserving timestamps (`|(d̃_↑ + d̃_↓) - RTT| > 25 ms`), `tether-events` automatically falls back to `mode=rtt` using the `median3` Echo quorum and directional byte-activity guards.
- **Hot-Reload Without `sudo`**: When the root `com.josaum.tether-optimize` LaunchDaemon is running, atomic replacement (`mv -f`) of `~/bin/tether-optimize` triggers `EVFILT_VNODE`, causing the daemon to re-lock ownership to `root:wheel` and `exec` the new script automatically.
