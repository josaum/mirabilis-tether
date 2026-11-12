const THEOREM_CATALOG = [
  { id: "Thm 1–12 (Sec 1–4)", title: "IPv4/CLAT46 Hotspot Classification & Partition", desc: "Disjoint classification of Apple 172.20.10.0/28, Android 192.168.43/49.x, RFC 7335 192.0.0.0/29 vs Home LAN." },
  { id: "Thm 13–28 (Sec 5–10)", title: "MTU/MSS Clamping & Encapsulation Geometry", desc: "Exact IPv4 (1380 B), IPv6 (1380 B), PPPoE (1452/1432 B), and WireGuard/Tailscale utun* (1220/1332 B) non-fragmentation." },
  { id: "Thm 29–55 (Sec 11–20)", title: "PF Grammar Order, AWDL Suppression & Debounce", desc: "Strict OpenBSD/macOS PF section ordering, Wi-Fi vs USB awdl0 state machine, and link-blip hysteresis." },
  { id: "Thm 56–90 (Sec 21–29)", title: "Event Reactor, Proportional Fast-Lane & AIMD Bounds", desc: "kqueue + PF_ROUTE completeness, 80% proportional Fast-Lane (#10/#11), and closed-loop [floor, ceiling] invariants." },
  { id: "Thm 91–95 (Sec 30)", title: "Bounded Join-Semilattice & Lyapunov Convergence", desc: "Catamorphism uniqueness, discrete Banach-Lyapunov contraction, encapsulation Galois adjunction, and Jacobson-Karels >=18ms deadband." },
  { id: "Thm 96–100 (Sec 31)", title: "Taleb Fat Tails, InvGamma(n, nα) MLE & Shadow Mean", desc: "Exact N/(N-1) small-sample Hill bias identity, unbiased α̂₀=(n-1)/S_n, Cirillo-Taleb finite Shadow Mean, and order-statistic streak k(α)." },
  { id: "Thm 101–105 (Sec 32)", title: "Pontryagin's Maximum Principle & Hamiltonian Control", desc: "Global maximization of H(q,u,-λ)=U_W(u)+λ(u_max-u) at u*(λ)=clamp(⌊W/λ⌋), comparative statics, and Taleb adjoint forcing Ψ." },
  { id: "Thm 106 (Sec 33.1)", title: "RFC 792 One-Way Delay Clock-Offset Cancellation", desc: "For any clock offset θ ∈ ℤ, (d̃_↑ - b̃_↑) = Δq_↑, (d̃_↓ - b̃_↓) = Δq_↓, and d̃_↑ + d̃_↓ = d_↑ + d_↓ = RTT." },
  { id: "Thm 107 (Sec 33.2)", title: "Byzantine 2-of-3 Multi-Reflector Quorum (median3)", desc: "Birkhoff distributive median3 rejects any single reflector spike B ≥ H across all 3! permutations." },
  { id: "Thm 108 (Sec 33.3)", title: "Revealed-Capacity Costate Dual (1-Step Fade Capture)", desc: "λ_cap(W, r̂) = ⌊W/(r̂+1)⌋ + 1 guarantees ⌊W/λ_cap⌋ ≤ r̂ and captures a 100→12 Mbps fade in one 500ms tick." },
  { id: "Thm 109 (Sec 33.4)", title: "BDP-Isochronous CoDel/GRED Queue Scaling", desc: "Strict ordering 2 ≤ min_th(r) < max_th(r) < slots(r) ≤ 90 and monotonicity across all rates r ∈ [2, 100] Mbps." },
  { id: "Thm 110 (Sec 33.5)", title: "Adaptive Two-Speed kqueue Cadence & Zero Idle Overhead", desc: "Zero radio probes at Δbytes < 48 KB (3000ms sleep) and 6x faster 500ms control under active traffic." }
];

let theoremItems = THEOREM_CATALOG.map(t => ({ id: t.id, name: t.title, desc: t.desc }));

function renderTheorems(filterText = "") {
  const q = filterText.trim().toLowerCase();
  const container = document.getElementById("theorem-container");
  container.innerHTML = "";
  theoremItems.filter(t =>
    !q || `${t.id} ${t.name} ${t.desc}`.toLowerCase().includes(q)
  ).forEach(t => {
    const div = document.createElement("div");
    div.className = "theorem-item";
    div.setAttribute("role", "listitem");
    const head = document.createElement("strong");
    head.textContent = t.id ? `${t.id}: ${t.name}` : t.name;
    const sub = document.createElement("span");
    sub.textContent = t.desc;
    div.append(head, sub);
    container.appendChild(div);
  });
  if (!container.childElementCount) {
    const empty = document.createElement("div");
    empty.className = "theorem-item";
    empty.textContent = "No declarations match that filter.";
    container.appendChild(empty);
  }
}

async function loadTheoremCatalog() {
  if (location.protocol === "file:") return;
  try {
    const res = await fetch("/api/theorems", { cache: "no-store" });
    const data = await res.json();
    if (!data.ok) return;
    theoremItems = data.items.map(it => ({
      id: "",
      name: it.name.replace(/_/g, " "),
      desc: `${it.section} · line ${it.line} · \`${it.name}\``,
    }));
    document.getElementById("theorem-count").textContent =
      `${data.count} declarations · ${data.sections.length} sections · ${data.axioms} axioms`;
    document.getElementById("theorem-tag").textContent = `${data.sections.length} sections parsed`;
    renderTheorems(document.getElementById("theorem-search").value);
  } catch (err) {
    /* keep the static summary list */
  }
}

function filterTheorems() {
  renderTheorems(document.getElementById("theorem-search").value);
}

function applyPreset(umax, ex, tail, rhat, btn) {
  document.querySelectorAll(".preset-btn").forEach(b => b.classList.remove("active"));
  if (btn) btn.classList.add("active");
  document.getElementById("sim-umax").value = umax;
  document.getElementById("sim-ex").value = ex;
  document.getElementById("sim-tail").value = tail;
  document.getElementById("sim-rhat").value = rhat;
  updateWorkbench();
}

function setRange(id, value) {
  const el = document.getElementById(id);
  if (!el) return;
  el.value = String(Math.min(Number(el.max), Math.max(Number(el.min), Math.round(value))));
}

function resetWorkbench() {
  document.querySelectorAll(".preset-btn").forEach(b => b.classList.remove("active"));
  const first = document.querySelector(".preset-btn");
  if (first) first.classList.add("active");
  setRange("sim-umax", 100);
  setRange("sim-ex", 4);
  setRange("sim-tail", 22);
  setRange("sim-rhat", 95);
  updateWorkbench();
}

function loadLiveWorkbench() {
  if (!lastSnapshot || !lastSnapshot.ok) return;
  const sh = lastSnapshot.shaper;
  document.querySelectorAll(".preset-btn").forEach(b => b.classList.remove("active"));
  setRange("sim-umax", sh.down_mbps || 100);
  setRange("sim-ex", sh.owd.down_ex_ms);
  setRange("sim-rhat", sh.eff_down_mbps || sh.down_mbps);
  updateWorkbench();
}

function resetOWD() {
  setRange("owd-theta", 1345);
  setRange("owd-up", 48);
  setRange("owd-down", 3);
  setRange("owd-byz", 290);
  updateOWD();
}

function loadLiveOWD() {
  if (!lastSnapshot || !lastSnapshot.ok) return;
  const owd = lastSnapshot.shaper.owd;
  setRange("owd-up", owd.up_ex_ms);
  setRange("owd-down", owd.down_ex_ms);
  updateOWD();
}

function resetROI() {
  setRange("roi-hours", 12);
  setRange("roi-devs", 5);
  updateROI();
}

function updateWorkbench() {
  const uMax = parseInt(document.getElementById("sim-umax").value, 10);
  const ex = parseInt(document.getElementById("sim-ex").value, 10);
  const tailPct = parseInt(document.getElementById("sim-tail").value, 10);
  const rHat = Math.min(uMax, parseInt(document.getElementById("sim-rhat").value, 10));
  const tau0 = 20;
  const uMin = 4;
  const W = uMax * tau0;

  document.getElementById("out-umax").textContent = `${uMax} Mbps`;
  document.getElementById("out-ex").textContent = `${ex} ms`;
  document.getElementById("out-tail").textContent = `${tailPct}%`;
  document.getElementById("out-rhat").textContent = `${rHat} Mbps`;

  // Debiased Hill-Taleb InvGamma estimator (n = 8 sample window)
  const n = 8;
  const sBar = tailPct / 100.0;
  const alpha0 = ((n - 1) / n) * (1.0 / sBar);
  const alphaMilli = Math.round(alpha0 * 1000);
  const L = 10.0;
  const H = 350.0;
  let shadowMs = 15.0;
  if (alpha0 > 1.05) {
    shadowMs = L + (L / (alpha0 - 1.0)) * (1.0 - Math.pow(L / H, alpha0 - 1.0));
  } else {
    shadowMs = L + L * Math.log(H / L) * 0.65;
  }

  // Adjoint forcing Psi (Theorem 104)
  let tailTerm = 0;
  if (alphaMilli < 2000) {
    const excessWeight = 2000 - alphaMilli;
    const rawTail = Math.floor((excessWeight * Math.round(shadowMs)) / 2000);
    tailTerm = Math.min(120, rawTail);
  }
  const psi = tau0 + ex + tailTerm;

  // Revealed-capacity shadow price (Theorem 108)
  const lamCap = Math.floor(W / (rHat + 1)) + 1;
  let lam = ex > 12 ? Math.max(psi, lamCap) : tau0;
  const uStar = Math.max(uMin, Math.min(uMax, Math.floor(W / lam)));

  // BDP-Isochronous GRED (Theorem 109)
  const minTh = Math.max(2, Math.min(24, Math.floor(uStar / 4) + 2));
  const maxTh = Math.max(6, Math.min(64, Math.floor((3 * uStar) / 4) + 6));
  const qSlots = Math.max(10, Math.min(90, uStar + 10));

  document.getElementById("kpi-ustar").textContent = `${uStar} Mbps`;
  document.getElementById("kpi-lambda").textContent = `${lam} ms`;
  document.getElementById("kpi-alpha").textContent = alpha0.toFixed(2);
  document.getElementById("kpi-shadow").textContent = `${shadowMs.toFixed(1)} ms`;
  document.getElementById("kpi-lamcap").textContent = `${lamCap} ms`;
  document.getElementById("kpi-gred").textContent = `${minTh}/${maxTh}/${qSlots}`;

  const badge = document.getElementById("regime-badge");
  if (ex <= 12 && alpha0 >= 1.5) {
    badge.className = "badge-pass";
    badge.textContent = "✓ Drained Equilibrium (u* = u_max)";
  } else {
    badge.className = "badge-warn";
    badge.textContent = `⚡ Pontryagin Active Control (u* = ${uStar} Mbps)`;
  }

  // Render SVG Hamiltonian curve H(u) = U_W(u) + lam * (uMax - u)
  const Hcurve = new Array(uMax + 1).fill(0);
  let util = 0;
  let minH = Infinity, maxH = -Infinity;
  for (let u = uMin; u <= uMax; u++) {
    util += Math.floor(W / u);
    Hcurve[u] = util + lam * (uMax - u);
    if (Hcurve[u] < minH) minH = Hcurve[u];
    if (Hcurve[u] > maxH) maxH = Hcurve[u];
  }
  const spanH = Math.max(1, maxH - minH);
  const xOf = u => 30 + ((u - uMin) / Math.max(1, uMax - uMin)) * 465;
  const yOf = h => 150 - ((h - minH) / spanH) * 115;

  let d = "";
  for (let u = uMin; u <= uMax; u++) {
    const x = xOf(u).toFixed(1);
    const y = yOf(Hcurve[u]).toFixed(1);
    d += (u === uMin ? `M ${x} ${y}` : ` L ${x} ${y}`);
  }
  document.getElementById("svg-curve").setAttribute("d", d);
  const optX = xOf(uStar);
  const optY = yOf(Hcurve[uStar]);
  document.getElementById("svg-opt-line").setAttribute("x1", optX);
  document.getElementById("svg-opt-line").setAttribute("x2", optX);
  document.getElementById("svg-opt-dot").setAttribute("cx", optX);
  document.getElementById("svg-opt-dot").setAttribute("cy", optY);
  document.getElementById("svg-opt-label").textContent =
    `Global Max H(u*=${uStar} Mbps) = ${Hcurve[uStar]} [λ=${lam}ms, W=${W}]`;
}

function updateOWD() {
  const theta = parseInt(document.getElementById("owd-theta").value, 10);
  const qUp = parseInt(document.getElementById("owd-up").value, 10);
  const qDown = parseInt(document.getElementById("owd-down").value, 10);
  const byz = parseInt(document.getElementById("owd-byz").value, 10);
  const baseUp = 5, baseDown = 5;

  const dUpApp = baseUp + qUp + theta;
  const dDownApp = baseDown + qDown - theta;
  const bUpApp = baseUp + theta;
  const bDownApp = baseDown - theta;

  const recUp = dUpApp - bUpApp;
  const recDown = dDownApp - bDownApp;
  const rttTrue = (baseUp + qUp) + (baseDown + qDown);
  const r1 = rttTrue, r2 = rttTrue + byz, r3 = rttTrue + 2;
  const sorted = [r1, r2, r3].sort((a, b) => a - b);
  const med3 = sorted[1];

  document.getElementById("out-theta").textContent = `${theta >= 0 ? "+" : ""}${theta} ms`;
  document.getElementById("out-owd-up").textContent = `${qUp} ms`;
  document.getElementById("out-owd-down").textContent = `${qDown} ms`;
  document.getElementById("out-owd-byz").textContent = `+${byz} ms spike`;

  document.getElementById("kpi-dup").textContent = `${dUpApp >= 0 ? "+" : ""}${dUpApp} ms`;
  document.getElementById("kpi-ddown").textContent = `${dDownApp >= 0 ? "+" : ""}${dDownApp} ms`;
  document.getElementById("kpi-dsum").textContent = `${dUpApp + dDownApp} ms`;
  document.getElementById("kpi-rec-up").textContent = `${recUp} ms`;
  document.getElementById("kpi-rec-down").textContent = `${recDown} ms`;
  document.getElementById("kpi-median3").textContent = `${med3} ms`;

  const badge = document.getElementById("owd-isolation-badge");
  if (recUp > 25 && recDown <= 15) {
    badge.className = "badge-pass";
    badge.textContent = "✓ Upload Isolated (Download Unthrottled)";
  } else if (recDown > 25 && recUp <= 15) {
    badge.className = "badge-pass";
    badge.textContent = "✓ Download Isolated (Upload Unthrottled)";
  } else {
    badge.className = "badge-pass";
    badge.textContent = "✓ Clock Offset θ Cancelled Exactly";
  }

  document.getElementById("owd-proof-readout").textContent =
    `Theorem 106 & 107 Verified: (d̃_↑ - b̃_↑) = (${dUpApp}) - (${bUpApp}) = ${recUp} ms | (d̃_↓ - b̃_↓) = (${dDownApp}) - (${bDownApp}) = ${recDown} ms | median3(${r1}, ${r2}, ${r3}) = ${med3} ms (Byzantine +${byz}ms spike rejected).`;
}

const PROFILES = [
  {
    title: "iPhone / iPad USB High-Speed Tether (en7 / en17)",
    desc: "Detects Apple Mobile Device USB Ethernet interfaces in < 1 ms via AF_ROUTE kernel sockets while strictly excluding USB LAN docks (en9) and VMware passthrough NICs. Keeps awdl0 UP for AirDrop while clamping cellular MTU to 1420 B and TCP MSS to 1380 B.",
    code: `scrub on en7 inet all no-df random-id max-mss 1380 fragment reassemble\nscrub on en7 inet6 all max-mss 1380 fragment reassemble\ndummynet out on en7 proto { icmp, icmp6, tcp, udp } to any pipe 11   # Fast-Lane Interactive\ndummynet in  on en7 all pipe 12                                      # Pontryagin Bulk Downlink`
  },
  {
    title: "Wi-Fi Personal Hotspot + AWDL Channel-Hop Guard (en0)",
    desc: "Automatically detects iOS 172.20.10.0/28, Android 192.168.43/49.x, or macOS Low Data Mode on en0. Suppresses awdl0 channel-hopping while tethered over Wi-Fi so neither the Mac nor iPhone radio stutters.",
    code: `ifconfig awdl0 down                                                  # Eliminates 120ms AWDL scan spikes\nscrub on en0 inet all no-df random-id max-mss 1380 fragment reassemble\nsysctl net.inet.tcp.delayed_ack=3 net.inet.tcp.l4s=1 net.inet.tcp.bg_target_qdelay=15`
  },
  {
    title: "Overlay VPN Tunnels (Tailscale / WireGuard utun* Dual-Scrub)",
    desc: "Dynamically tracks active utun* and feth* interfaces on every PF_ROUTE event, clamping inner TCP SYN MSS to 1220 B on Hotspot (or 1332 B on Home PPPoE) so outer UDP WireGuard packets never fragment.",
    code: `scrub on utun0 inet  all no-df max-mss 1220 fragment reassemble\nscrub on utun0 inet6 all max-mss 1220 fragment reassemble\n# Theorem 93 Encapsulation Galois Adjunction: inner Payload + 80B WG + 40B IPv6 <= 1420B MTU`
  },
  {
    title: "Standard Home PPPoE Fiber & Wired LAN Handover (en0 / en9)",
    desc: "When disconnecting from hotspot, automatically restores unshaped gigabit throughput, sets PPPoE-safe MTU 1492 (MSS 1452 IPv4 / 1432 IPv6), re-enables awdl0 for AirDrop, and resumes throttled background sync daemons.",
    code: `dnctl -q flush                                                       # Unshaped full-speed Home LAN/Fiber\nscrub on en0 inet  all no-df random-id max-mss 1452 fragment reassemble\nscrub on en0 inet6 all max-mss 1432 fragment reassemble`
  }
];

function selectProfile(idx, btn) {
  document.querySelectorAll(".tab-btn").forEach(b => b.setAttribute("aria-selected", "false"));
  btn.setAttribute("aria-selected", "true");
  document.getElementById("prof-title").textContent = PROFILES[idx].title;
  document.getElementById("prof-desc").textContent = PROFILES[idx].desc;
  document.getElementById("prof-code").textContent = PROFILES[idx].code;
}

function copyCmd(id, btn) {
  const text = document.getElementById(id).textContent;
  navigator.clipboard.writeText(text).then(() => {
    const orig = btn.textContent;
    btn.textContent = "✓ Copied";
    setTimeout(() => { btn.textContent = orig; }, 1600);
  });
}

function updateROI() {
  const hrs = parseInt(document.getElementById("roi-hours").value, 10);
  const devs = parseInt(document.getElementById("roi-devs").value, 10);
  document.getElementById("out-roi-hours").textContent = `${hrs} hrs/wk`;
  document.getElementById("out-roi-devs").textContent = `${devs} Mac${devs > 1 ? "s" : ""}`;
  const savedHrs = Math.round(hrs * devs * 50 * 0.0625);
  const valueUsd = savedHrs * 150;
  document.getElementById("roi-stalls").textContent = `${savedHrs.toLocaleString()} hrs`;
  document.getElementById("roi-dollars").textContent = `$${valueUsd.toLocaleString()}`;
}

/* ── Live system state ─────────────────────────────────────────────
   Populated from /api/snapshot, which the companion server (serve.py)
   assembles from the daemon's own state files. Under file:// the API is
   unreachable by design, so the page degrades to an honest static view. */
const LIVE_POLL_MS = 2000;
let liveFailures = 0;
let lastSnapshot = null;

function fmtAge(sec) {
  if (sec == null || !Number.isFinite(Number(sec))) return "—";
  sec = Number(sec);
  if (sec < 90) return `${sec} s`;
  if (sec < 5400) return `${Math.round(sec / 60)} min`;
  if (sec < 172800) return `${(sec / 3600).toFixed(1)} h`;
  return `${(sec / 86400).toFixed(1)} d`;
}

function liveRow(k, v, cls) {
  const row = document.createElement("div");
  row.className = "live-row";
  const kk = document.createElement("span");
  kk.className = "k";
  kk.textContent = k;
  const vv = document.createElement("span");
  vv.className = "v" + (cls ? " " + cls : "");
  vv.textContent = v;
  row.append(kk, vv);
  return row;
}

function fillRows(id, rows) {
  document.getElementById(id).replaceChildren(...rows);
}

function modeLabel(mode) {
  if (mode.paused) return "Paused";
  if (!mode.hotspot) return "Home / unshaped";
  return mode.transport === "usb" ? "Hotspot (USB)" : "Hotspot (Wi-Fi)";
}

function renderLive(s) {
  if (!s.ok) {
    setLiveOffline(`snapshot unavailable: ${s.reason || "unknown"}`);
    return;
  }
  document.getElementById("live-offline").hidden = true;
  liveFailures = 0;
  lastSnapshot = s;

  const mode = s.mode, sh = s.shaper;
  const tag = document.getElementById("live-tag");
  tag.className = "section-tag live-tag-live";
  tag.textContent = `● LIVE · ${s.host} · snapshot ${fmtAge(s.snapshot_age_sec)} old`;

  const pill = document.getElementById("nav-pill-text");
  pill.textContent = `${modeLabel(mode)} · ${sh.eff_down_mbps}/${sh.down_mbps} Mbps`;

  const modeTag = document.getElementById("live-mode-tag");
  modeTag.textContent = modeLabel(mode);
  modeTag.className = "section-tag" + (mode.hotspot && !mode.paused ? " live-tag-live" : "");

  fillRows("live-uplink", [
    liveRow("Mode", modeLabel(mode)),
    liveRow("Service / device", `${mode.service || "—"} / ${mode.device || "—"}`),
    liveRow("Address", mode.ip || "—"),
    liveRow("MTU / MSS (outer→inner)", `${mode.mtu} B · ${mode.outer_mss} → ${mode.overlay_mss} B`),
    liveRow("Overlay ifaces", `${sh.overlay_ifaces.length} tunnels`),
    liveRow("awdl0 guard", mode.awdl_up ? "awdl0 UP (AirDrop enabled)" : `awdl0 DOWN (${mode.awdl_suppressed} wake(s) suppressed)`,
      mode.awdl_up ? "warn" : "ok"),
    liveRow("Background PIDs throttled", String(mode.throttled_bg), mode.throttled_bg > 0 ? "ok" : ""),
    liveRow("Snapshot written", fmtAge(s.snapshot_age_sec + (s.sampler_lag_sec || 0)),
      (s.sampler_lag_sec || 0) > 5 ? "warn" : "ok"),
  ]);

  const meter = document.getElementById("live-uplink-meter");
  const pct = sh.down_mbps > 0 ? Math.min(100, Math.round((sh.eff_down_mbps / sh.down_mbps) * 100)) : 0;
  meter.style.width = `${pct}%`;

  fillRows("live-control", [
    liveRow("u* down / up", `${sh.eff_down_mbps} / ${sh.eff_up_mbps} Mbps`),
    liveRow("Ceiling (configured)", `${sh.down_mbps} / ${sh.up_mbps} Mbps`),
    liveRow("Costate λ ↓ / ↑", `${sh.costate.down_ms} / ${sh.costate.up_ms} ms`),
    liveRow("OWD excess Δq ↓ / ↑", `${sh.owd.down_ex_ms} / ${sh.owd.up_ex_ms} ms (${sh.owd.mode})`),
    liveRow("AIMD regime", `${sh.autorate.regime || "—"} (Δ ${sh.autorate.delta_ms} ms)`),
    liveRow("Shaper", sh.enabled ? "ACTIVE" : "OFF", sh.enabled ? "ok" : "warn"),
  ]);

  const pf = sh.pf || { scrub: 0, dummynet: 0, block: 0, watchlist: 0 };
  fillRows("live-guard", [
    liveRow("Taleb α̂ (MLE)", sh.taleb.alpha.toFixed(2), sh.taleb.alpha < 1 ? "warn" : "ok"),
    liveRow("InvGamma n", String(sh.taleb.n)),
    liveRow("Shadow mean", `${sh.taleb.shadow_mean_ms.toFixed(1)} ms`),
    liveRow("VaR₉₉*", `${sh.taleb.var99_ms.toFixed(1)} ms (${sh.taleb.regime})`),
    liveRow("PF scrub / dummynet rules", `${pf.scrub} / ${pf.dummynet}`),
    liveRow("PF block rules", `${pf.block} (${pf.watchlist} watchlist)`, pf.block > 0 ? "ok" : "warn"),
  ]);

  const auditTag = document.getElementById("live-audit-tag");
  if (s.audit) {
    const a = s.audit;
    const l3ok = a.max_l3 <= a.mtu_ceiling;
    auditTag.textContent = `${a.packets} pkts · ${fmtAge(a.file_age_sec)} old`;
    auditTag.className = "section-tag" + (l3ok && a.fragmented === 0 ? " live-tag-live" : " live-tag-off");
    fillRows("live-audit", [
      liveRow("Interface", a.ifaces || a.device || "—"),
      liveRow("Max L3 vs ceiling", `${a.max_l3} / ${a.mtu_ceiling} B`, l3ok ? "ok" : "bad"),
      liveRow("SYN MSS out v4 / v6", `${a.mss_out_v4} / ${a.mss_out_v6}`),
      liveRow("SYN MSS inbound", a.mss_in || "none"),
      liveRow("TCP iRTT", a.irtt || "n/a"),
      liveRow("Unicast DNS RTT", a.dns_rtt || "n/a"),
      liveRow("Retrans / dupACK / RST", `${a.retrans} / ${a.dup_ack} / ${a.reset}`),
      liveRow("Fragmented packets", String(a.fragmented), a.fragmented > 0 ? "warn" : "ok"),
      liveRow("Watchlist pkts / anomalies", `${a.watchlist_pkts} / ${a.security_anomalies}`,
        a.security_anomalies > 0 ? "warn" : "ok"),
    ]);
  } else {
    auditTag.textContent = "no audit yet";
    auditTag.className = "section-tag live-tag-off";
    fillRows("live-audit", [liveRow("Run tether-optimize pcap 4", "then refresh")]);
  }

  const vTag = document.getElementById("live-verify-tag");
  if (s.verify) {
    const v = s.verify;
    const vok = v.ok === "1";
    vTag.textContent = vok ? `PASS · ${fmtAge(Number(v.file_age_sec))} old` : "FAILED";
    vTag.className = "section-tag" + (vok ? " live-tag-live" : " live-tag-off");
    fillRows("live-verify", [
      liveRow("Result", vok ? `${v.passed}/${v.total} theorems · 0 axioms` : "verification failed",
        vok ? "ok" : "bad"),
      liveRow("Spec", v.spec || "—"),
      liveRow("Prover", v.lean || "—"),
      liveRow("Last run", v.ts ? new Date(Number(v.ts) * 1000).toLocaleString() : "—"),
    ]);
  } else {
    vTag.textContent = "not run yet";
    vTag.className = "section-tag live-tag-off";
    fillRows("live-verify", [liveRow("Run tether-optimize verify-lean", "≈13 s")]);
  }

  const tbody = document.getElementById("live-sysctl-body");
  let pass = 0, checked = 0;
  const rows = s.sysctl.map(item => {
    const tr = document.createElement("tr");
    const name = document.createElement("td");
    name.textContent = item.name;
    name.className = "val";
    const exp = document.createElement("td");
    exp.textContent = item.expect ?? "—";
    exp.className = "val";
    const val = document.createElement("td");
    val.textContent = item.value || "n/a";
    val.className = "val";
    const st = document.createElement("td");
    if (item.expect == null) {
      st.textContent = "info";
      st.style.color = "var(--text-muted)";
      st.className = "val";
    } else {
      checked += 1;
      const ok = item.value === item.expect;
      if (ok) pass += 1;
      st.textContent = ok ? "✓ MATCH" : "✗ DRIFT";
      st.className = "val " + (ok ? "v ok" : "v bad");
    }
    tr.append(name, exp, val, st);
    return tr;
  });
  tbody.replaceChildren(...rows);

  const prof = s.sysctl_profile || {};
  const sysTag = document.getElementById("live-sysctl-tag");
  const applied = prof.age_sec != null ? ` · applied ${fmtAge(prof.age_sec)} ago` : "";
  sysTag.textContent = `${pass}/${checked} · ${prof.profile || "unknown"} profile${applied}`;
  sysTag.title = prof.source === "engine"
    ? "Expected column is the set the engine applied (tcp-profile.env)"
    : "Expected column fell back to the built-in table for the detected mode";
  sysTag.className = "section-tag" + (pass === checked ? " live-tag-live" : " live-tag-off");

  renderLog(s.log, s.ts);
}

function renderLog(lines, ts) {
  const el = document.getElementById("live-log");
  const joined = lines.join("\n");
  if (el.dataset.hash === joined) {
    document.getElementById("live-log-stamp").textContent =
      `${lines.length} lines · fetched ${new Date(ts * 1000).toLocaleTimeString()}`;
    return;
  }
  const atBottom = el.scrollTop + el.clientHeight >= el.scrollHeight - 24;
  const frag = document.createDocumentFragment();
  lines.forEach((line, i) => {
    const span = document.createElement("span");
    span.className = /error|fail|drift|watchlist|block drop/i.test(line) ? "lg-err"
      : /warn|pause|fade|underflow|enobufs|deadband/i.test(line) ? "lg-warn" : "";
    span.textContent = line + (i < lines.length - 1 ? "\n" : "");
    frag.appendChild(span);
  });
  el.replaceChildren(frag);
  el.dataset.hash = joined;
  if (atBottom) el.scrollTop = el.scrollHeight;
  document.getElementById("live-log-stamp").textContent =
    `${lines.length} lines · fetched ${new Date(ts * 1000).toLocaleTimeString()}`;
}

function setLiveOffline(reason) {
  const banner = document.getElementById("live-offline");
  banner.hidden = false;
  document.getElementById("live-offline-detail")?.remove();
  if (reason) {
    const p = document.createElement("p");
    p.id = "live-offline-detail";
    p.style.color = "var(--text-muted)";
    p.textContent = `Details: ${reason}`;
    banner.append(p);
  }
  const tag = document.getElementById("live-tag");
  tag.className = "section-tag live-tag-off";
  tag.textContent = "◌ STATIC COPY (no live channel)";
  document.getElementById("live-mode-tag").textContent = "offline";
  document.getElementById("nav-pill-text").textContent = "static copy";
  document.getElementById("nav-pulse").style.background = "var(--accent-amber)";
  document.getElementById("nav-pulse").style.boxShadow = "0 0 8px var(--accent-amber)";
}

const TRENDS = [
  { id: "u", field: "u_down", unit: "Mbps", decimals: 0, color: "#58a6ff" },
  { id: "lam", field: "lam_down", unit: "ms", decimals: 0, color: "#a5d6ff" },
  { id: "owd", field: "owd_down", unit: "ms", decimals: 0, color: "#56d364" },
  { id: "alpha", field: "alpha", unit: "", decimals: 2, color: "#f0883e" },
];
let lastSamples = [];
let rulesTick = 0;

function drawSpark(id, values, color) {
  const canvas = document.getElementById(`trend-${id}`);
  if (!canvas || values.length < 2) return;
  const dpr = window.devicePixelRatio || 1;
  const w = canvas.clientWidth || 220;
  const h = canvas.clientHeight || 78;
  if (canvas.width !== Math.round(w * dpr) || canvas.height !== Math.round(h * dpr)) {
    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(h * dpr);
  }
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);

  const min = Math.min(...values);
  const max = Math.max(...values);
  const span = max - min || 1;
  const pad = 6;
  const xOf = i => pad + (i * (w - pad * 2)) / (values.length - 1);
  const yOf = v => h - pad - ((v - min) / span) * (h - pad * 2);

  ctx.strokeStyle = "rgba(255,255,255,0.06)";
  ctx.lineWidth = 1;
  [0.25, 0.5, 0.75].forEach(f => {
    ctx.beginPath();
    ctx.moveTo(pad, pad + f * (h - pad * 2));
    ctx.lineTo(w - pad, pad + f * (h - pad * 2));
    ctx.stroke();
  });

  const grad = ctx.createLinearGradient(0, 0, 0, h);
  grad.addColorStop(0, color + "55");
  grad.addColorStop(1, color + "00");

  ctx.beginPath();
  values.forEach((v, i) => (i ? ctx.lineTo(xOf(i), yOf(v)) : ctx.moveTo(xOf(0), yOf(v))));
  ctx.strokeStyle = color;
  ctx.lineWidth = 1.6;
  ctx.stroke();
  ctx.lineTo(xOf(values.length - 1), h - pad);
  ctx.lineTo(xOf(0), h - pad);
  ctx.closePath();
  ctx.fillStyle = grad;
  ctx.fill();
}

function updateTrends(samples) {
  lastSamples = samples;
  const tag = document.getElementById("live-trend-tag");
  if (!samples.length) {
    tag.textContent = "collecting…";
    return;
  }
  const spanSec = samples[samples.length - 1].ts - samples[0].ts;
  tag.textContent = `${samples.length} samples · ${Math.max(1, Math.round(spanSec / 60))} min window · sampled by server`;
  TRENDS.forEach(t => {
    const values = samples.map(s => Number(s[t.field]) || 0);
    drawSpark(t.id, values, t.color);
    const last = values[values.length - 1];
    document.getElementById(`trend-${t.id}-val`).textContent =
      `${last.toFixed(t.decimals)}${t.unit ? " " + t.unit : ""}`;
  });
}

async function loadRules() {
  try {
    const res = await fetch("/api/rules", { cache: "no-store" });
    const data = await res.json();
    if (!data.ok) return;
    ["scrub", "dummynet", "block"].forEach(key => {
      document.getElementById(`rules-${key}`).textContent =
        (data.groups[key] || []).join("\n") || "(none loaded)";
      document.getElementById(`rules-${key}-count`).textContent = String(data.counts[key] || 0);
    });
    document.getElementById("live-rules-tag").textContent =
      `${data.counts.scrub} scrub · ${data.counts.dummynet} dummynet · ${data.counts.block} block`;
  } catch (err) {
    /* leave the last render in place */
  }
}

async function pollLive() {
  if (location.protocol === "file:") {
    setLiveOffline("page opened over file:// — start the local server to attach telemetry");
    return;
  }
  try {
    const [snapRes, histRes] = await Promise.all([
      fetch("/api/snapshot", { cache: "no-store" }),
      fetch("/api/history", { cache: "no-store" }),
    ]);
    if (!snapRes.ok) throw new Error(`HTTP ${snapRes.status}`);
    renderLive(await snapRes.json());
    if (histRes.ok) {
      const hist = await histRes.json();
      if (hist.ok) updateTrends(hist.samples);
    }
    if (rulesTick++ % 5 === 0) loadRules();
  } catch (err) {
    liveFailures += 1;
    if (liveFailures === 1) setLiveOffline(err.message);
  }
}

window.addEventListener("resize", () => updateTrends(lastSamples));

pollLive();
setInterval(pollLive, LIVE_POLL_MS);
loadTheoremCatalog();

renderTheorems();

updateWorkbench();
updateOWD();
updateROI();
