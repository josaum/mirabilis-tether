# Mirabilis-Tether: Formally Verified Cellular Hotspot Control via Pontryagin's Maximum Principle, Inverse-Gamma Fat-Tail Debiasing, and Clock-Offset-Cancelled One-Way Delay

**Author:** Dionisio Chiuratto Agourakis (`dionisio.ca@gmail.com` · ORCID: [`0009-0000-4863-9143`](https://orcid.org/0009-0000-4863-9143)) · **DOI:** [`10.5281/zenodo.24100456`](https://doi.org/10.5281/zenodo.24100456) · **Repository:** [`github.com/josaum/mirabilis-tether`](https://github.com/josaum/mirabilis-tether) · **PDF Edition:** [`paper/mirabilis_tether.pdf`](mirabilis_tether.pdf) · **Version:** 1.0.0 (November 2026)

---

## Abstract

When a desktop or laptop operating system tethers to a smartphone Personal Hotspot (5G/LTE over Wi-Fi or USB), six interacting systems pathologies degrade interactive latency: (1) multi-megabyte host TCP socket buffers saturate un-managed smartphone baseband queues, inducing `450–1,200+ ms` bufferbloat stalls; (2) symmetric ICMP Echo RTT controllers conflate uplink and downlink congestion, falsely throttling download capacity during heavy uploads; (3) fixed-step multiplicative-decrease (AIMD) controllers require `5–6 seconds` to track abrupt cellular fades; (4) naive Gaussian or plug-in Pareto estimators underestimate heavy-tailed 5G/LTE scheduling spikes due to finite-sample Maximum Likelihood bias; (5) periodic Apple Wireless Direct Link (`awdl0`) social-channel scans induce `120 ms` Wi-Fi radio stutters; and (6) cascading GTP-U, RFC 7335 CLAT46 (`464XLAT`), and overlay VPN (`utun*`) headers trigger silent Path MTU blackholes.

We present **Mirabilis-Tether** (`tether-optimize`), a zero-dependency macOS/XNU kernel optimization engine and native menu bar suite whose entire mathematical and state-transition specification is machine-checked in **110 zero-axiom constructive Lean 4 theorems** ([`proofs/TetherOptimizeSpec.lean`](../proofs/TetherOptimizeSpec.lean), `4,099` lines, zero external imports) and validated at runtime by **72 live system assertions**. Our mathematical framework unifies: (i) *Mirabilis Abbreviatio*, an exact small-sample debiasing of the Hill–Taleb Pareto tail estimator $\widehat{\alpha}_{\text{MLE}} \sim \text{InvGamma}(n, n\alpha)$ paired with the Cirillo–Taleb compact-support Shadow Mean; (ii) a discrete formulation of **Pontryagin's Maximum Principle** over logarithmic Kelly utility solved in $O(1)$ integer arithmetic via the floor-division Galois connection; (iii) a **Revealed-Capacity Costate Dual** driven by 64-bit `NET_RT_IFLIST2` kernel counters that captures abrupt $100 \to 12\text{ Mbps}$ cellular fades in a single `500 ms` step (`11×` faster than AIMD); and (iv) a parallel 3-reflector BSD `IPPROTO_ICMP` **RFC 792 Type 13/14 One-Way Delay quorum** that algebraically cancels arbitrary host-reflector clock offsets $\theta \in \mathbb{Z}$ while rejecting single-reflector spikes via Birkhoff's distributive median. Live evaluation on Apple Silicon (M1) demonstrates a **`697×` counter-sensing speedup** (`7.8 µs` vs. `5.41 ms`), **`0.0%` standby CPU overhead**, exact wire-level $\theta$-cancellation, and zero packet fragmentation or retransmissions.

---

## 1. Introduction & The Six Pathologies of Mobile Tethering

Modern cellular networks (5G NR and LTE-Advanced) exhibit extreme non-stationarity: air-interface capacity fluctuates by an order of magnitude within hundreds of milliseconds due to carrier aggregation switches, beam handovers, RLC retransmissions, and physical shadowing. When a macOS host tethers to an iPhone, iPad, or Android device via Wi-Fi (`en0`) or USB (`en7`/`en17`), six structural mismatches arise:

1. **Baseband Bufferbloat**: Stock macOS permits TCP socket buffers to auto-scale up to `16 MiB`. On an `8 Mbps` (`1,000 B/ms`) cellular uplink, a single bulk flow can enqueue `16,777,216 B` into the smartphone's baseband FIFO, creating up to `16.7 s` of queueing delay (**Theorem 8**) behind which interactive DNS, SSH, and WebRTC packets stall.
2. **Symmetric RTT Blindness**: Standard autorate loops probe the link with symmetric ICMP Echo (`Type 8/0`) requests. Because $\text{RTT} = d_\uparrow + d_\downarrow$, pure upload saturation inflates RTT and causes symmetric controllers to slash the *download* shaper pipe by `50–80%`, starving downlink throughput even when the cellular downlink is completely idle.
3. **Multi-Second Lag on Abrupt Fades**: Classical AIMD autorate loops decay the shaper ceiling multiplicatively ($r_{k+1} = \lfloor 0.8 r_k \rfloor$). If a user enters an elevator and cellular capacity drops from `100 Mbps` to `12 Mbps`, multiplicative decay requires `11` consecutive bloated ticks (`5.5 s` at `500 ms`/tick) to converge.
4. **Fat-Tailed Scheduling Spikes & Small-Sample MLE Bias**: Cellular MAC scheduling delays follow power-law Pareto/Lomax distributions $P(X > x) = (x/L)^{-\alpha}$. In small rolling windows ($n \in [4, 20]$), the Maximum Likelihood (Hill) estimator $\widehat{\alpha}_{\text{MLE}} = n / \sum_{i=1}^n \ln(X_i / L)$ is Inverse-Gamma distributed with expectation $\mathbb{E}[\widehat{\alpha}_{\text{MLE}}] = \frac{n}{n-1}\alpha > \alpha$, systematically overestimating tail thinness.
5. **AWDL Social-Channel Radio Stutters**: On macOS, the Apple Wireless Direct Link (`awdl0`) interface periodically hops off the active Wi-Fi AP channel to scan social channels (AirDrop/Handoff), introducing periodic `80–150 ms` latency spikes on Wi-Fi hotspots.
6. **Cascading Encapsulation Blackholes**: Carrier GTP-U tunnels and RFC 7335 CLAT46 (`464XLAT`) translation reduce effective path MTU to `1420–1450 B`. Combined with overlay VPNs (Tailscale/WireGuard `utun*` adding `80 B`), un-scrubbed TCP segments suffer silent PMTU drops.

---

## 2. Algebraic & Lattice Foundations of Network State Control

All proofs in [`proofs/TetherOptimizeSpec.lean`](../proofs/TetherOptimizeSpec.lean) are constructed from first principles over inductive Peano naturals and integers so that every theorem reduces purely in the Lean 4 kernel with **0 external imports and 0 axioms**.

### 2.1 Bounded Join-Semilattice Catamorphism (Theorem 91)

Let $(L, \sqcup, \bot, \top)$ be a bounded join-semilattice of network operating modes (ordered from passive Home LAN/Wi-Fi $\bot$ through constrained Wi-Fi hotspot to active USB Personal Hotspot $\top$). For any observation map $f : A \to L$, the fold catamorphism $\Phi_f([a_1, \dots, a_k]) = f(a_1) \sqcup \dots \sqcup f(a_k) \sqcup \bot$ is a monoid homomorphism under list concatenation ($\Phi_f(xs \mathbin{+\!+} ys) = \Phi_f(xs) \sqcup \Phi_f(ys)$), is idempotent on duplicate observations, and short-circuits upon encountering $\top$.

### 2.2 Encapsulation Galois Adjunction & Dual PF Scrubbing (Theorems 93–94)

For payload size $p \in \mathbb{N}$, header overhead $H \in \mathbb{N}$, and link MTU $M \in \mathbb{N}$, the pair $\text{encap}_H(p) = p + H$ and $\text{decap}_H(M) = M \ominus H = \max(0, M - H)$ forms a monotone Galois connection $\text{encap}_H \dashv \text{decap}_H$:
$$\text{encap}_H(p) \le M \iff p \le \text{decap}_H(M).$$
By adjoint composition, compound encapsulation (inner TCP/IPv6 $H_1 = 60\text{ B}$ inside WireGuard/Tailscale `utun*` $H_2 = 80\text{ B}$ over cellular MTU $M = 1420\text{ B}$) satisfies $\text{decap}_{H_1}(\text{decap}_{H_2}(M)) = M \ominus (H_1 + H_2) = 1280\text{ B}$. Clamping $\text{MSS}_{\text{outer}} = 1380\text{ B}$ and $\text{MSS}_{\text{overlay}} = 1220\text{ B}$ via idempotent PF `max-mss` scrubbing ($\min(p, c_1, c_2) = \min(p, \min(c_1, c_2))$) strictly prevents L3 fragmentation across all IPv4, IPv6, GTP-U, and CLAT46 paths.

### 2.3 Jacobson–Karels Adaptive Deadband Invariant (Theorem 95)

For RFC 6298 EWMA mean deviation $v = \text{RTTVAR} \in \mathbb{N}$, the adaptive hysteresis thresholds $\Theta_{\text{high}}(v) = 30 + \min(60, 2v)$ and $\Theta_{\text{low}}(v) = 12 + \min(20, \lfloor v/2 \rfloor)$ satisfy $\Theta_{\text{high}}(v) - \Theta_{\text{low}}(v) \ge 18\text{ ms}$ for all $v \ge 0$.

---

## 3. *Mirabilis Abbreviatio*: Inverse-Gamma Fat-Tail Estimation & Shadow Means

Given $n$ exceedance observations $X_1, \dots, X_n \ge L$ from a Pareto Type I tail $P(X > x) = (x/L)^{-\alpha}$, the log-exceedance sum $S_n = \sum_{i=1}^n \ln(X_i / L)$ follows $\text{Gamma}(n, \alpha)$.

### 3.1 Exact Small-Sample Bias of the Hill MLE & MVUE Debiasing (Theorems 96–97)

The Maximum Likelihood (Hill) estimator $\widehat{\alpha}_{\text{MLE}} = \frac{n}{S_n}$ follows an Inverse-Gamma distribution:
$$\widehat{\alpha}_{\text{MLE}} = \frac{n}{S_n} \sim \text{InvGamma}(\text{shape}=n,\, \text{scale}=n\alpha), \qquad \mathbb{E}[\widehat{\alpha}_{\text{MLE}}] = \frac{n}{n-1}\alpha > \alpha.$$
Multiplying by $\frac{n-1}{n}$ yields the exact Minimum Variance Unbiased Estimator (MVUE):
$$\widehat{\alpha}_0 = \frac{n-1}{S_n} = \frac{n-1}{n}\widehat{\alpha}_{\text{MLE}}, \qquad \mathbb{E}[\widehat{\alpha}_0] = \alpha \quad (\forall n \ge 2).$$

### 3.2 Posterior Predictive Lomax & Cirillo–Taleb Shadow Mean (Theorems 98–100)

Integrating out $\alpha$ against the $\text{Gamma}(n, S_n)$ likelihood yields the Lomax predictive survival function $P(X_{\text{new}} > x \mid S_n, n) = \left(1 + \frac{\ln(x/L)}{S_n}\right)^{-n}$ with exact predictive quantile $\text{VaR}_p^\star = L \exp\!\left(S_n((1-p)^{-1/n} - 1)\right)$. On compact physical timeout support $[L, H]$ ($H = 350\text{ ms}$), the **Cirillo–Taleb Shadow Mean**:
$$\mu_{\text{shadow}}(\alpha, L, H) = \frac{\alpha L}{\alpha - 1}\,\frac{1 - (L/H)^{\alpha - 1}}{1 - (L/H)^\alpha} \quad (\alpha \ne 1), \qquad \mu_{\text{shadow}}(1, L, H) = \frac{L \ln(H/L)}{1 - L/H}$$
remains strictly finite and well-ordered even when $\widehat{\alpha}_0 \le 1$.

---

## 4. Pontryagin's Maximum Principle & Galois Control Duality

### 4.1 Global Maximization of the Discrete Kelly–Pontryagin Hamiltonian (Theorem 101)

With target BDP scale $W = u_{\max}\tau_0$, discrete Kelly logarithmic utility $U_W(u) = \sum_{j=1}^u \lfloor W / j \rfloor$, and shadow price (costate) $\lambda \ge 1$, the discrete Pontryagin Hamiltonian is:
$$\mathcal{H}(q, u, -\lambda) = U_W(u) + \lambda (u_{\max} - u).$$
By the floor-division Galois connection ($q \cdot d \le W \iff q \le \lfloor W / d \rfloor$), the marginal utility satisfies $\Delta U_W(u) = \lfloor W / u \rfloor \ge \lambda \iff u \le \lfloor W / \lambda \rfloor$. Consequently,
$$u^\star(\lambda) = \operatorname{clamp}_{[u_{\min}, u_{\max}]}\!\left(\left\lfloor \frac{u_{\max}\tau_0}{\lambda} \right\rfloor\right)$$
globally maximizes $\mathcal{H}(q, u, -\lambda)$ over all $u \in [u_{\min}, u_{\max}]$ in $O(1)$ integer arithmetic (**Theorems 101–105**).

---

## 5. Closing the Real-World Gap: OWD Quorum & Revealed-Capacity Duality

### 5.1 RFC 792 One-Way Delay Clock-Offset Cancellation (Theorem 106)

For any host-reflector clock offset $\theta \in \mathbb{Z}$, RFC 792 Type 13/14 apparent one-way delays $\tilde{d}_\uparrow = b_\uparrow + \Delta q_\uparrow + \theta$ and $\tilde{d}_\downarrow = b_\downarrow + \Delta q_\downarrow - \theta$ satisfy:
$$\tilde{d}_\uparrow - \tilde{b}_\uparrow = \Delta q_\uparrow, \qquad \tilde{d}_\downarrow - \tilde{b}_\downarrow = \Delta q_\downarrow, \qquad \tilde{d}_\uparrow + \tilde{d}_\downarrow = \text{RTT}.$$

### 5.2 Byzantine 2-of-3 Multi-Reflector Quorum (Theorem 107)

Probing `9.9.9.9` (Type 13), `149.112.112.112` (Type 13), and `1.1.1.1` (Type 8) in parallel and aggregating via Birkhoff's distributive $\text{median3}(a,b,c) = \max(\min(a,b), \min(\max(a,b), c))$ rejects any single reflector spike $B \ge H$ across all $3! = 6$ permutations.

### 5.3 Revealed-Capacity Costate Dual: 1-Step Cellular Fade Capture (Theorem 108)

Define the **Revealed-Capacity Costate Dual** from 64-bit `NET_RT_IFLIST2` achieved goodput $\hat{r}$:
$$\lambda_{\text{cap}}(W, \hat{r}) = \left\lfloor \frac{W}{\hat{r} + 1} \right\rfloor + 1.$$
By Galois duality, $\lfloor W / \lambda_{\text{cap}}(W, \hat{r}) \rfloor \le \hat{r}$ holds for all $W, \hat{r} \in \mathbb{N}$. For an elevator fade from $u_{\max} = 100\text{ Mbps}$ ($W = 2000$) to $\hat{r} = 12\text{ Mbps}$, $\lambda_{\text{cap}}(2000, 12) = 154\text{ ms}$ sets $u^\star(154) = \lfloor 2000/154 \rfloor = 12\text{ Mbps}$ in **1 tick (`500 ms`, `11×` faster than AIMD)**.

---

## 6. Empirical Evaluation on Apple Silicon (M1)

| Subsystem / Metric | Legacy / Baseline | Mirabilis-Tether (`v1.0.0`) | Measured Result / Verification |
| :--- | :--- | :--- | :--- |
| **64-bit Byte Counter Read** | `netstat -ibn` (`5.41 ms`) | `sysctl(NET_RT_IFLIST2)` (`memcpy`) | **`7.8 µs` (`697×` speedup, `0` forks)** |
| **Reactor Idle CPU & RSS** | Shell loop (`0.4%` CPU) | `tether-events` (`kqueue`) | **`0.0%` CPU, `2.64 MB` RSS (`2,704 KB`), `0` idle pings** |
| **Menu Bar App Footprint** | Electron tray (`>150 MB`) | `TetherMenubar.app` (Cocoa) | **`0.0%` CPU, `13.0 MB` RSS (`13,360 KB`)** |
| **RFC 792 OWD $\theta$-Cancel** | Raw $\tilde{d}_\uparrow = +1567\text{ ms}$ | $\tilde{d}_\uparrow + \tilde{d}_\downarrow = 1567 + (-1557)$ | **`10 ms` ($\theta \approx +1.56\text{ s}$ cancelled; `median3` RTT `11 ms`)** |
| **4s Wire Audit (`791` pkts)** | Uninspected framing | `dumpcap -s 128` + `tether_optimize.lua` | **Max L3 `1480 B` ($\le 1492\text{ B}$), `frag=0`, `retrans=0`** |
| **ACK Tail Risk (`n = 19`)** | Naive $\text{VaR}_{99} = 137.8\text{ ms}$ | Debiased $\widehat{\alpha}_0 = 1.22 \pm 0.30$ | **Shadow Mean `21.4 ms`, $\text{VaR}_{99}^\star = 220.8\text{ ms}$ (`+60.2%`)** |
| **Formal Spec Verification** | `0` proofs | `TetherOptimizeSpec.lean` (`4,099` LOC) | **`110 / 110` theorems in `17.5 s` (`0` axioms)** |
| **Live System Self-Tests** | Manual checks | `tether-optimize test` | **`72 / 72` assertions passed (`0` failed)** |
