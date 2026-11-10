# Mirabilis-Tether (`tether-optimize` v1.0.0)
### *Mirabilis Abbreviatio* — Formally Verified macOS Personal Hotspot & WAN Optimizer

[![Lean 4 Kernel Verified](https://img.shields.io/badge/Lean_4-110_Theorems_(0_Axioms)-3fb950)](proofs/TetherOptimizeSpec.lean)
[![Live Assertions](https://img.shields.io/badge/Live_Assertions-72%2F72_Passing-58a6ff)](bin/tether-optimize)
[![macOS Platform](https://img.shields.io/badge/macOS-Apple_Silicon_%26_XNU-bc8cff)](https://github.com/josaum/mirabilis-tether)
[![Research Paper](https://img.shields.io/badge/Paper-PDF_%26_LaTeX-f0883e)](paper/mirabilis_tether.pdf)

**Mirabilis-Tether** (`tether-optimize`) is an event-driven macOS kernel optimization product and native Menu Bar suite that eliminates cellular baseband bufferbloat, Wi-Fi `awdl0` channel-hopping stutters, GTP-U/CLAT46 packet fragmentation, and background sync saturation when tethered to an iPhone, iPad, or Android Personal Hotspot (over Wi-Fi `en0` or USB `en7`/`en17`), while automatically restoring unshaped PPPoE-safe Gigabit Home Wi-Fi/LAN settings on disconnect.

Every control law, state transition, packet-size bound, and statistical estimator is machine-verified in **110 zero-axiom constructive Lean 4 theorems** ([`proofs/TetherOptimizeSpec.lean`](proofs/TetherOptimizeSpec.lean)), documented in the accompanying research paper ([**PDF**](paper/mirabilis_tether.pdf) | [**Markdown**](paper/MIRABILIS_TETHER_PAPER.md) | [**LaTeX**](paper/mirabilis_tether.tex)), and continuously validated by **72 live system & unit assertions** (`tether-optimize test`).

---

## 1. Core Benefits: Why Stock macOS Tethering Stalls & How Mirabilis-Tether Fixes It

When a Mac tethers to an iPhone, iPad, or Android phone, six compounding OS and radio pathologies degrade interactive performance:

1. **Baseband Queue Bufferbloat (`16 MB` Socket Buffers $\to$ `>1,000 ms` Stalls)**:
   - *Pathology*: Stock macOS allows TCP send/receive buffers to balloon up to `16 MB` (`net.inet.tcp.sendspace` / `autorcvbufmax`), dumping megabytes of bulk frames into the phone's cellular baseband FIFO and causing `450–1,200+ ms` latency spikes (proven worst-case `>13 s` at 8 Mbps in **Theorem 8**).
   - *Fix*: Clamps socket buffers, enables L4S + FQ-CoDel ECN (`net.inet.tcp.l4s=1`), reserves an 80% proportional Fast-Lane (`dnctl` Pipes `#10`/`#11`) for interactive traffic (`ICMP`, `DNS`, `SSH`, `NTP`, `DoT`, `WireGuard`), and shapes bulk queues (`Pipes #12`/`#13`) via **Pontryagin's Maximum Principle** around target queue delay $\tau_0 = 20\text{ ms}$ (**Theorems 9, 101–105**).
2. **Self-Inflicted Download Throttling During Heavy Uploads (Symmetric Ping Blindness)**:
   - *Pathology*: Standard autorate controllers measure symmetric Echo RTT (`Type 8/0`). When a cloud backup or `git push` saturates the 5G/LTE uplink, symmetric RTT rises and the controller mistakenly slashes the *download* pipe by 50–80%.
   - *Fix*: Uses parallel BSD `SOCK_DGRAM` `IPPROTO_ICMP` **RFC 792 Type 13/14 Timestamp probes** across a 3-reflector quorum (`9.9.9.9`, `149.112.112.112`, `1.1.1.1`) to cancel arbitrary host-reflector clock offset $\theta \in \mathbb{Z}$ and isolate directional queueing delays $(\Delta q_\uparrow, \Delta q_\downarrow)$ (**Theorems 106 & 107**).
3. **Multi-Second Lag on Abrupt Cellular Fades (`5,500 ms` AIMD Decay vs `500 ms` 1-Step Capture)**:
   - *Pathology*: When stepping into an elevator or cellular shadow (e.g., capacity drops from `100 Mbps` to `12 Mbps`), multiplicative decrease (`×0.8` per step) takes **11 control cycles (`5.5 seconds`)** to catch up, causing massive packet loss.
   - *Fix*: Computes the **Revealed-Capacity Costate** $\lambda_{\text{cap}}(W, \hat{r}) = \lfloor W/(\hat{r}+1)\rfloor + 1$ from zero-fork 64-bit `NET_RT_IFLIST2` kernel byte counters, snapping $u^\star(\lambda)$ to the true bottleneck $\hat{r} = 12\text{ Mbps}$ in **a single `500 ms` step** (**Theorem 108**).
4. **Heavy-Tailed Cellular Jitter Underestimation (Gaussian/Plug-in Fallacy)**:
   - *Pathology*: 5G/LTE scheduling spikes follow power-law Pareto/Lomax tails where finite-sample Maximum Likelihood Estimation ($\widehat{\alpha}_{\text{MLE}}$) overestimates $\alpha$ by $\frac{n}{n-1}$, systematically understating tail risk.
   - *Fix*: Applies exact `InvGamma(n, nα)` small-sample debiasing $\widehat{\alpha}_0 = \frac{n-1}{S_n}$, computes the **Cirillo–Taleb Shadow Mean** (which remains finite even when $\alpha \le 1$), and drives the Pontryagin adjoint forcing $\Psi$ accordingly (**Theorems 96–100, 104**).
5. **AirDrop (`awdl0`) Channel-Hopping Radio Stutters (`120 ms` Periodic Spikes)**:
   - *Pathology*: While tethered over Wi-Fi (`en0`), macOS periodically switches the Wi-Fi radio off the hotspot channel to scan Apple Wireless Direct Link (`awdl0`) social channels.
   - *Fix*: Automatically holds `awdl0` `DOWN` while tethered over Wi-Fi hotspot (`en0`), and automatically restores `awdl0` `UP` when tethered via USB cable (`en7`/`en17`) or on Home Wi-Fi/LAN (**Theorems 33–38**).
6. **GTP-U / CLAT46 & Overlay VPN (`utun*`) Fragmentation Blackholes**:
   - *Pathology*: Cellular carriers encapsulate packets in GTP-U and RFC 7335 CLAT46 (`464XLAT`), reducing effective MTU below `1500 B`. Inner WireGuard/Tailscale tunnels (`utun*`) add another `80 B` of overhead, causing silent PMTU blackholes.
   - *Fix*: Enforces a dual PF MSS scrub Galois adjunction: `MTU 1420 B` + outer `max-mss 1380 B` + inner `utun*` `max-mss 1220 B` on Hotspot (and PPPoE-safe `MTU 1492 B` + outer `1452/1432 B` + inner `1332 B` on Home networks) (**Theorems 13–28, 93**).

---

## 2. Empirical Measurements & Verified Benchmarks

All measurements below were executed live on an **Apple M1 Mac** (`macOS 26.5.2`, XNU kernel, Lean `4.35.0`, Wireshark `tshark`/`dumpcap` with `tether_optimize.lua`). We strictly distinguish **live empirical measurements** from **machine-checked mathematical bounds**.

### 2.1 Live System & Kernel Microbenchmarks (Measured on Apple M1)

| Subsystem / Operation | Legacy / Baseline Approach | Mirabilis-Tether (`v1.0.0`) | Measured Result / Speedup | Reproducibility Command |
| :--- | :--- | :--- | :--- | :--- |
| **64-bit Interface Byte Sensing** | Forking `/usr/sbin/netstat -ibn` (`5.41 ms` / call) | In-process `sysctl(NET_RT_IFLIST2)` (`if_msghdr2`) | **`7.8 µs` / call (`697×` faster, `0` forks)** | `tether-events --probe en0` |
| **Idle Daemon CPU & Memory** | Polling shell loops (`0.4%` CPU, `20` pings/min) | `kqueue` + `AF_ROUTE` (`tether-events`) | **`0.0%` CPU, `2.64 MB` RSS (`2,704 KB`), `0` idle pings** | `ps -o pid,%cpu,rss,comm -p $(pgrep -x tether-events)` |
| **Native Menu Bar App Footprint** | Electron / WebView tray apps (`150–400 MB` RSS) | Native Cocoa `TetherMenubar.app` (`EVFILT_VNODE`) | **`0.0%` CPU, `13.0 MB` RSS (`13,360 KB`)** | `ps -o pid,%cpu,rss,comm -p $(pgrep -x tether-menubar)` |
| **RFC 792 One-Way Delay $\theta$-Cancellation** | Unusable raw timestamps ($\tilde{d}_\uparrow = +1567\text{ ms}$, $\tilde{d}_\downarrow = -1557\text{ ms}$) | Clock-offset-cancelled conservation sum $\tilde{d}_\uparrow + \tilde{d}_\downarrow$ | **`1567 + (-1557) = 10 ms` (vs `11 ms` `median3` RTT; $\theta \approx 1.56\text{ s}$ cancelled)** | `tether-optimize owd-probe` |
| **Live 4s Wire-Level Packet Audit** | Uninspected L3/L4 framing (`791` frames, `82.6 KB`) | `dumpcap -s 128` + `tshark` + `tether_optimize.lua` | **Max L3 `1480 B` ($\le 1492\text{ B}$), `frag=0`, `retrans=0`, `dup_ack=0`, `zero_win=0`** | `tether-optimize pcap 4` |
| **Live ACK RTT Fat-Tail Analysis** | Naive plug-in sample mean & quantile (`n = 19` ACK spikes $\ge 3.82\text{ ms}$) | Debiased $\widehat{\alpha}_0 \sim \text{InvGamma}(19, 19\alpha)$ + Predictive Lomax | **$\widehat{\alpha}_0 = 1.22 \pm 0.30$ (raw MLE `1.28`), Shadow Mean `21.4 ms` (vs `18.6 ms` sample), $\text{VaR}_{99}^\star = 220.8\text{ ms}$ (vs `137.8 ms` naive — captures `+60.2%` hidden tail risk)** | `tether-optimize pcap 4` |
| **Dead Proxy & USB Guard Sweep** | Unconditional `networksetup` calls (stalls on shadow USB ports) | Attached-only `iface_exists` + `SCPreferences` guard | **`<= 1.0 s` across all attached & unplugged USB ports** | `tether-optimize test` (`PASS 33`) |
| **Lean 4 Formal Proof Check** | Unverified shell heuristics (`0` proofs) | `TetherOptimizeSpec.lean` (`4,099` lines, `0` imports) | **`110 / 110` theorems kernel-verified in `17.5 s` (`0` axioms)** | `tether-optimize verify-lean` |

### 2.2 Machine-Checked Mathematical Guarantees (Lean 4 Kernel Verified)

| Control / Network Scenario | Unoptimized / Classical Behavior | Mirabilis-Tether Formal Bound | Verified Lean 4 Theorem |
| :--- | :--- | :--- | :--- |
| **Worst-Case Uplink Bufferbloat (`16 MB` buf @ `8 Mbps`)** | $16,777,216\text{ B} / 1,000\text{ B/ms} = \mathbf{16,777\text{ ms}}$ (`> 13 s`) stall | Clamped buffer + pipe drain **$< 22\text{ ms}$** ($\tau_0 = 20\text{ ms}$) | [`unthrottled_causes_13s_bufferbloat`](proofs/TetherOptimizeSpec.lean) & [`hotspot_pipe_drain_under_22ms`](proofs/TetherOptimizeSpec.lean) (Thms 8–9) |
| **Abrupt Cellular Fade (`100 Mbps` $\to$ `12 Mbps` Elevator Drop)** | `11` AIMD ticks (`×0.8`/step) = **`5,500 ms`** overshoot | $\lambda_{\text{cap}}(2000, 12) = 154\text{ ms} \implies u^\star(154) = 12\text{ Mbps}$ in **`1` tick (`500 ms`, `11×` faster)** | [`revealed_capacity_costate_single_step_capture`](proofs/TetherOptimizeSpec.lean#L3699-L3740) (Thm 108) |
| **Byzantine Single-Reflector Spike (`350 ms` Rate-Limit Glitch)** | Single-host ping triggers false `×0.8` rate cut | Birkhoff distributive `median3(6, 8, 350) = 8 ms` (**`0%` false throttle across all $3!$ permutations**) | [`multi_reflector_median3_byzantine_resilience`](proofs/TetherOptimizeSpec.lean#L3641-L3671) (Thm 107) |
| **Small-Sample Hill-Taleb Tail Bias ($n = 4$)** | Raw MLE $\widehat{\alpha}_{\text{MLE}}$ overestimates $\alpha$ by $+33.3\%$ ($\frac{4}{3}\alpha$) | Exact `InvGamma(n, nα)` MVUE correction $\widehat{\alpha}_0 = \frac{n-1}{n}\widehat{\alpha}_{\text{MLE}}$ (**`0` first-moment bias**) | [`inv_gamma_mle_small_sample_bias_identity`](proofs/TetherOptimizeSpec.lean#L2700-L2735) (Thm 96) |
| **BDP-Isochronous CoDel/GRED Scaling ($r \in [2, 100]\text{ Mbps}$)** | Static `4/14` packet thresholds starve 5G or bloat LTE | Strict invariant $2 \le \text{min\_th}(r) < \text{max\_th}(r) < \text{slots}(r) \le 90$ (`2/6/10` at 2M $\to$ `24/64/90` at 100M) | [`bdp_isochronous_gred_invariants_and_monotonicity`](proofs/TetherOptimizeSpec.lean#L3767-L3882) (Thm 109) |

---

## 3. Architecture & Mathematical Stack

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

## 4. Repository Layout

```text
tether-optimize/
├── Makefile                                  # Build, verify, test, and .pkg release targets
├── README.md                                 # Product architecture, benchmarks & runbook
├── paper/
│   ├── mirabilis_tether.pdf                  # Typeset research paper (PDF)
│   ├── mirabilis_tether.tex                  # LaTeX source of the research paper
│   └── MIRABILIS_TETHER_PAPER.md             # GitHub-rendered Markdown edition of the paper
├── bin/
│   ├── tether-optimize                       # Portable CLI & root daemon engine (v1.0.0)
│   └── tether-events                         # Compiled XNU kqueue + RFC 792 OWD reactor
├── src/
│   ├── tether-events.swift                   # XNU kqueue + PF_ROUTE + RFC 792 OWD reactor source
│   └── tether-menubar.swift                  # Native macOS Cocoa Menu Bar application source
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

## 5. Quick Start & CLI Reference

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

## 6. Verification & Reproducibility

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

## 7. Exception Handling & Recovery Boundaries

- **Unplugged or Flapping USB Cable**: Debounced across `1.5s` transient USB resets (`watch_loop`) and guarded by `iface_exists` before touching `networksetup` or `ifconfig`.
- **ICMP Timestamp Filtered by Carrier**: If a cellular carrier strips RFC 792 Type 13/14 messages or returns non-conserving timestamps (`|(d̃_↑ + d̃_↓) - RTT| > 25 ms`), `tether-events` automatically falls back to `mode=rtt` using the `median3` Echo quorum and directional byte-activity guards.
- **Hot-Reload Without `sudo`**: When the root `com.josaum.tether-optimize` LaunchDaemon is running, atomic replacement (`mv -f`) of `~/bin/tether-optimize` triggers `EVFILT_VNODE`, causing the daemon to re-lock ownership to `root:wheel` and `exec` the new script automatically.
