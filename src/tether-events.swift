// tether-events.swift — Zero-Polling XNU Kernel Event Reactor & SOTA Multi-Reflector OWD Engine
//
// Capabilities:
//   1. AF_ROUTE raw socket (`RTM_IFINFO`, `RTM_IFINFO2`, `RTM_NEWADDR`, `RTM_DELADDR`, `RTM_ADD`,
//      `RTM_DELETE`, `RTM_CHANGE`) detects USB/Wi-Fi/LAN attach, detach, DHCP/IPv6 assignment,
//      utun* creation, and default-route switches in < 1 ms (filtering ARP/ND6 neighbor churn).
//   2. kqueue EVFILT_VNODE watches both `tether-optimize` (hot-reload) and `.tether-optimize.prefs`
//      (zero-password CLI & TetherMenubar IPC), plus parent directories for atomic `mv -f`.
//   3. Zero-fork 64-bit `NET_RT_IFLIST2` (`if_msghdr2`) interface byte-rate sensing + adaptive
//      two-speed `EVFILT_TIMER` (`500 ms` active load / `3000 ms` idle with `0` radio probes).
//   4. Parallel BSD `SOCK_DGRAM` `IPPROTO_ICMP` 3-reflector quorum (`9.9.9.9` RFC 792 Type 13/14 OWD,
//      `149.112.112.112` RFC 792 Type 13/14 OWD, `1.1.1.1` Type 8/0 Echo) with:
//        • Clock-offset-cancelled one-way queueing delays `(Δq_↑, Δq_↓)` (Paxson / RFC 6817 LEDBAT),
//        • Physical conservation validation `|(upRaw + downRaw) - rttMs| ≤ 25`,
//        • Empty-queue (`RTT ≤ baseRTT + 4 ms`) quartz clock-skew drift re-anchoring, and
//        • Birkhoff distributive `median3` Byzantine single-reflector glitch immunity.
//   5. Standalone `--probe [iface] [timeout_ms]` CLI mode for instant diagnostics & live self-tests.
//
// Build:
//   swiftc -O -o bin/tether-events src/tether-events.swift

import Darwin
import Foundation

enum IdentTag: UInt {
    case timer     = 1
    case parentPid = 2
}

struct ReflectorSample {
    let ip: String
    let responded: Bool
    let rttMs: Int
    let owdValid: Bool
    let upRawMs: Int
    let downRawMs: Int
}

struct ReflectorBaseline {
    let ip: String
    let icmpType: UInt8
    var baseRttMs: Int? = nil
    var baseUpRaw: Int? = nil
    var baseDownRaw: Int? = nil
    var nearBaseCount: Int = 0

    mutating func reset() {
        baseRttMs = nil
        baseUpRaw = nil
        baseDownRaw = nil
        nearBaseCount = 0
    }

    mutating func updateAndExcess(_ s: ReflectorSample) -> (rttEx: Int, downEx: Int?, upEx: Int?)? {
        guard s.responded else { return nil }
        if let b = baseRttMs {
            if s.rttMs <= b {
                baseRttMs = s.rttMs
                nearBaseCount = 0
            } else if s.rttMs <= b + 20 {
                nearBaseCount += 1
                if nearBaseCount >= 24 {
                    baseRttMs = b + 1
                    nearBaseCount = 0
                }
            }
        } else {
            baseRttMs = s.rttMs
        }

        let effBaseRtt = baseRttMs ?? s.rttMs
        let rttEx = max(0, s.rttMs - effBaseRtt)

        guard s.owdValid else {
            return (rttEx, nil, nil)
        }

        if baseUpRaw == nil || baseDownRaw == nil {
            baseUpRaw = s.upRawMs
            baseDownRaw = s.downRawMs
        } else {
            if s.upRawMs < baseUpRaw! { baseUpRaw = s.upRawMs }
            if s.downRawMs < baseDownRaw! { baseDownRaw = s.downRawMs }
            // Quartz oscillator skew re-anchoring: when round-trip queue is near-empty (`rttEx ≤ 4 ms`),
            // both one-way queues are physically near zero, so gently track slow clock offset drift ±1 ms.
            if rttEx <= 4 {
                if s.upRawMs > baseUpRaw! { baseUpRaw! += 1 }
                if s.downRawMs > baseDownRaw! { baseDownRaw! += 1 }
            }
        }

        let upEx = max(0, s.upRawMs - (baseUpRaw ?? s.upRawMs))
        let downEx = max(0, s.downRawMs - (baseDownRaw ?? s.downRawMs))
        return (rttEx, downEx, upEx)
    }
}

enum TelemetryMath {
    static func median3(_ a: Int, _ b: Int, _ c: Int) -> Int {
        return max(min(a, b), min(max(a, b), c))
    }

    static func icmpChecksum(_ bytes: [UInt8]) -> UInt16 {
        var sum: UInt32 = 0
        var i = 0
        while i + 1 < bytes.count {
            let word = (UInt32(bytes[i]) << 8) | UInt32(bytes[i + 1])
            sum += word
            i += 2
        }
        if i < bytes.count {
            sum += UInt32(bytes[i]) << 8
        }
        while (sum >> 16) != 0 {
            sum = (sum & 0xffff) + (sum >> 16)
        }
        return ~UInt16(sum & 0xffff)
    }

    static func utcMidnightMs() -> Int64 {
        var tv = timeval()
        gettimeofday(&tv, nil)
        let secInDay = Int64(tv.tv_sec) % 86400
        return secInDay * 1000 + Int64(tv.tv_usec) / 1000
    }

    static func unwrapDayMs(_ delta: Int64) -> Int {
        let dayMs: Int64 = 86_400_000
        var d = delta
        if d < -(dayMs / 2) { d += dayMs }
        if d > (dayMs / 2)  { d -= dayMs }
        return Int(d)
    }

    static func readInterfaceBytes64(_ targetName: String) -> (ibytes: UInt64, obytes: UInt64) {
        let targetIdx = if_nametoindex(targetName)
        guard targetIdx != 0 else { return (0, 0) }
        var mib: [Int32] = [CTL_NET, PF_ROUTE, 0, 0, NET_RT_IFLIST2, Int32(targetIdx)]
        var len: Int = 0
        guard sysctl(&mib, 6, nil, &len, nil, 0) == 0 && len > 0 else { return (0, 0) }
        var buf = [UInt8](repeating: 0, count: len + 256)
        len = buf.count
        guard sysctl(&mib, 6, &buf, &len, nil, 0) == 0 else { return (0, 0) }

        var off = 0
        while off + MemoryLayout<if_msghdr2>.size <= len {
            let msglen = Int(buf[off]) | (Int(buf[off + 1]) << 8)
            if msglen <= 0 { break }
            let rtmType = Int32(buf[off + 3])
            if rtmType == RTM_IFINFO2 {
                var hdr = if_msghdr2()
                _ = buf.withUnsafeBytes { raw in
                    memcpy(&hdr, raw.baseAddress!.advanced(by: off), MemoryLayout<if_msghdr2>.size)
                }
                if UInt32(hdr.ifm_index) == targetIdx {
                    return (hdr.ifm_data.ifi_ibytes, hdr.ifm_data.ifi_obytes)
                }
            }
            off += msglen
        }
        return (0, 0)
    }

    static func detectActiveHotspotDev() -> String? {
        var ifap: UnsafeMutablePointer<ifaddrs>? = nil
        guard getifaddrs(&ifap) == 0, let first = ifap else { return nil }
        defer { freeifaddrs(first) }

        var en7Up = false
        var en17Up = false
        var en0Hotspot = false

        var cur: UnsafeMutablePointer<ifaddrs>? = first
        while let p = cur {
            let flags = Int32(p.pointee.ifa_flags)
            if (flags & IFF_UP) != 0, let addr = p.pointee.ifa_addr {
                let name = String(cString: p.pointee.ifa_name)
                let fam = Int32(addr.pointee.sa_family)
                if fam == AF_INET {
                    let sin = addr.withMemoryRebound(to: sockaddr_in.self, capacity: 1) { $0.pointee }
                    let ipHost = UInt32(bigEndian: sin.sin_addr.s_addr)
                    let b0 = (ipHost >> 24) & 0xff
                    let b1 = (ipHost >> 16) & 0xff
                    let b2 = (ipHost >> 8) & 0xff
                    let isLinkLocal = (b0 == 169 && b1 == 254)
                    if !isLinkLocal && ipHost != 0 {
                        if name == "en7" { en7Up = true }
                        else if name == "en17" { en17Up = true }
                        else if name == "en0" {
                            if (b0 == 172 && b1 == 20 && b2 == 10) ||
                               (b0 == 192 && b1 == 0 && b2 == 0) ||
                               (b0 == 192 && b1 == 168 && b2 == 43) {
                                en0Hotspot = true
                            }
                        }
                    }
                } else if fam == AF_INET6 && (name == "en7" || name == "en17") {
                    let sin6 = addr.withMemoryRebound(to: sockaddr_in6.self, capacity: 1) { $0.pointee }
                    let b0 = sin6.sin6_addr.__u6_addr.__u6_addr8.0
                    let b1 = sin6.sin6_addr.__u6_addr.__u6_addr8.1
                    let isLinkLocal6 = (b0 == 0xfe && (b1 & 0xc0) == 0x80)
                    if !isLinkLocal6 && b0 != 0 {
                        if name == "en7" { en7Up = true }
                        else if name == "en17" { en17Up = true }
                    }
                }
            }
            cur = p.pointee.ifa_next
        }
        if en7Up { return "en7" }
        if en17Up { return "en17" }
        if en0Hotspot { return "en0" }
        return nil
    }

    static func probeMultiReflector(specs: [(ip: String, icmpType: UInt8)], timeoutMs: Int, seqSeed: UInt16) -> [ReflectorSample] {
        let count = specs.count
        var fds = [Int32](repeating: -1, count: count)
        var targetAddrs = [sockaddr_in](repeating: sockaddr_in(), count: count)
        var sendMonoNs = [UInt64](repeating: 0, count: count)
        var origDayMs = [Int64](repeating: 0, count: count)
        var seqs = [UInt16](repeating: 0, count: count)
        var results = specs.map {
            ReflectorSample(ip: $0.ip, responded: false, rttMs: timeoutMs, owdValid: false, upRawMs: 0, downRawMs: 0)
        }

        defer {
            for fd in fds where fd >= 0 { close(fd) }
        }

        let pidTag = UInt16(getpid() & 0xffff)
        var activeRemaining = 0

        for i in 0..<count {
            let fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_ICMP)
            guard fd >= 0 else { continue }
            let fl = fcntl(fd, F_GETFL, 0)
            _ = fcntl(fd, F_SETFL, fl | O_NONBLOCK)
            fds[i] = fd

            var addr = sockaddr_in()
            addr.sin_len = UInt8(MemoryLayout<sockaddr_in>.size)
            addr.sin_family = sa_family_t(AF_INET)
            inet_pton(AF_INET, specs[i].ip, &addr.sin_addr)
            targetAddrs[i] = addr

            let icmpType = specs[i].icmpType
            let seq = seqSeed &+ UInt16(i * 17 + 1)
            seqs[i] = seq
            let origMs = utcMidnightMs()
            origDayMs[i] = origMs

            var pkt = [UInt8](repeating: 0, count: icmpType == 13 ? 20 : 16)
            pkt[0] = icmpType
            pkt[1] = 0
            pkt[4] = UInt8(pidTag >> 8); pkt[5] = UInt8(pidTag & 0xff)
            pkt[6] = UInt8(seq >> 8);    pkt[7] = UInt8(seq & 0xff)
            if icmpType == 13 {
                let uOrig = UInt32(origMs & 0x7fffffff)
                pkt[8]  = UInt8((uOrig >> 24) & 0xff)
                pkt[9]  = UInt8((uOrig >> 16) & 0xff)
                pkt[10] = UInt8((uOrig >> 8) & 0xff)
                pkt[11] = UInt8(uOrig & 0xff)
            }
            let csum = icmpChecksum(pkt)
            pkt[2] = UInt8(csum >> 8); pkt[3] = UInt8(csum & 0xff)

            sendMonoNs[i] = clock_gettime_nsec_np(CLOCK_UPTIME_RAW)
            let sent = pkt.withUnsafeBytes { raw in
                withUnsafePointer(to: &addr) { ap in
                    ap.withMemoryRebound(to: sockaddr.self, capacity: 1) { sap in
                        sendto(fd, raw.baseAddress, pkt.count, 0, sap, socklen_t(MemoryLayout<sockaddr_in>.size))
                    }
                }
            }
            if sent > 0 {
                activeRemaining += 1
            } else {
                close(fd)
                fds[i] = -1
            }
        }

        let deadlineNs = clock_gettime_nsec_np(CLOCK_UPTIME_RAW) + UInt64(max(20, timeoutMs)) * 1_000_000
        var rbuf = [UInt8](repeating: 0, count: 256)

        while activeRemaining > 0 {
            let nowNs = clock_gettime_nsec_np(CLOCK_UPTIME_RAW)
            if nowNs >= deadlineNs { break }
            let remMs = Int32(max(1, (deadlineNs - nowNs) / 1_000_000))

            var pfds = [pollfd]()
            var pfdIdx = [Int]()
            for i in 0..<count where fds[i] >= 0 && !results[i].responded {
                pfds.append(pollfd(fd: fds[i], events: Int16(POLLIN), revents: 0))
                pfdIdx.append(i)
            }
            if pfds.isEmpty { break }

            let pr = poll(&pfds, nfds_t(pfds.count), remMs)
            if pr <= 0 {
                if pr < 0 && errno == EINTR { continue }
                break
            }

            let recvMono = clock_gettime_nsec_np(CLOCK_UPTIME_RAW)
            let recvDay = utcMidnightMs()

            for (k, pfd) in pfds.enumerated() where (pfd.revents & Int16(POLLIN)) != 0 {
                let idx = pfdIdx[k]
                var fromAddr = sockaddr_in()
                var fromLen = socklen_t(MemoryLayout<sockaddr_in>.size)
                let n = withUnsafeMutablePointer(to: &fromAddr) { fp in
                    fp.withMemoryRebound(to: sockaddr.self, capacity: 1) { sfp in
                        recvfrom(fds[idx], &rbuf, rbuf.count, MSG_DONTWAIT, sfp, &fromLen)
                    }
                }
                guard n >= 28 else { continue }
                guard fromAddr.sin_addr.s_addr == targetAddrs[idx].sin_addr.s_addr else { continue }

                let ihl = Int(rbuf[0] & 0x0f) * 4
                guard ihl >= 20 && n >= ihl + 8 else { continue }
                let rtype = rbuf[ihl]
                let rseq = (UInt16(rbuf[ihl + 6]) << 8) | UInt16(rbuf[ihl + 7])
                guard rseq == seqs[idx] else { continue }

                let rttMs = max(1, Int((recvMono - sendMonoNs[idx] + 500_000) / 1_000_000))
                if rtype == 14 && n >= ihl + 20 {
                    let rxRaw = (UInt32(rbuf[ihl + 12]) << 24) | (UInt32(rbuf[ihl + 13]) << 16)
                        | (UInt32(rbuf[ihl + 14]) << 8) | UInt32(rbuf[ihl + 15])
                    let txRaw = (UInt32(rbuf[ihl + 16]) << 24) | (UInt32(rbuf[ihl + 17]) << 16)
                        | (UInt32(rbuf[ihl + 18]) << 8) | UInt32(rbuf[ihl + 19])
                    // Reject non-UTC high-bit timestamps (RFC 792 §Timestamp)
                    let nonUtc = ((rxRaw & 0x80000000) != 0) || ((txRaw & 0x80000000) != 0)
                    let upRaw = unwrapDayMs(Int64(rxRaw) - origDayMs[idx])
                    let downRaw = unwrapDayMs(recvDay - Int64(txRaw))
                    let sumDiff = abs((upRaw + downRaw) - rttMs)
                    let validOwd = !nonUtc && sumDiff <= 25
                    results[idx] = ReflectorSample(
                        ip: specs[idx].ip,
                        responded: true,
                        rttMs: rttMs,
                        owdValid: validOwd,
                        upRawMs: validOwd ? upRaw : 0,
                        downRawMs: validOwd ? downRaw : 0
                    )
                    activeRemaining -= 1
                } else if rtype == 0 {
                    results[idx] = ReflectorSample(
                        ip: specs[idx].ip,
                        responded: true,
                        rttMs: rttMs,
                        owdValid: false,
                        upRawMs: 0,
                        downRawMs: 0
                    )
                    activeRemaining -= 1
                }
            }
        }
        return results
    }
}

final class KernelEventReactor {
    private let scriptPath: String
    private let scriptDir: String
    private let prefsPath: String
    private let prefsDir: String
    private let idleTickMs: Int
    private let fastTickMs: Int = 500
    private let parentPid: pid_t

    private var kq: Int32 = -1
    private var routeSock: Int32 = -1
    private var scriptDirFD: Int32 = -1
    private var prefsDirFD: Int32 = -1
    private var scriptFD: Int32 = -1
    private var prefsFD: Int32 = -1

    private var currentTimerMs: Int = 3000
    private var lastScriptMtime: timespec = timespec(tv_sec: 0, tv_nsec: 0)
    private var lastPrefsMtime: timespec = timespec(tv_sec: 0, tv_nsec: 0)

    private var activeHotspotDev: String = ""
    private var prevIbytes: UInt64 = 0
    private var prevObytes: UInt64 = 0
    private var prevCheckNs: UInt64 = 0
    private var fastCooldownTicks: Int = 0
    private var seqCounter: UInt16 = 1

    private var reflectors: [ReflectorBaseline] = [
        ReflectorBaseline(ip: "9.9.9.9", icmpType: 13),
        ReflectorBaseline(ip: "149.112.112.112", icmpType: 13),
        ReflectorBaseline(ip: "1.1.1.1", icmpType: 8)
    ]

    init(scriptPath: String, prefsPath: String, tickMs: Int, parentPid: pid_t) {
        self.scriptPath = scriptPath
        self.scriptDir = (scriptPath as NSString).deletingLastPathComponent
        self.prefsPath = prefsPath
        self.prefsDir = (prefsPath as NSString).deletingLastPathComponent
        self.idleTickMs = max(500, tickMs)
        self.currentTimerMs = max(500, tickMs)
        self.parentPid = parentPid
    }

    private static func fileMtime(_ path: String) -> timespec {
        var st = stat()
        if stat(path, &st) == 0 {
            return st.st_mtimespec
        }
        return timespec(tv_sec: 0, tv_nsec: 0)
    }

    private static func sameTimespec(_ a: timespec, _ b: timespec) -> Bool {
        return a.tv_sec == b.tv_sec && a.tv_nsec == b.tv_nsec
    }

    private func registerVnode(_ fd: Int32) {
        guard fd >= 0 else { return }
        var ev = kevent(
            ident: UInt(fd),
            filter: Int16(EVFILT_VNODE),
            flags: UInt16(EV_ADD | EV_ENABLE | EV_CLEAR),
            fflags: UInt32(NOTE_WRITE | NOTE_RENAME | NOTE_DELETE | NOTE_EXTEND),
            data: 0,
            udata: nil
        )
        _ = kevent(kq, &ev, 1, nil, 0, nil)
    }

    private func rearmFileFDs() {
        if scriptFD >= 0 { close(scriptFD) }
        scriptFD = open(scriptPath, O_EVTONLY)
        registerVnode(scriptFD)

        if prefsFD >= 0 { close(prefsFD) }
        prefsFD = open(prefsPath, O_EVTONLY)
        registerVnode(prefsFD)
    }

    private func setTimerInterval(_ ms: Int) {
        guard ms != currentTimerMs else { return }
        currentTimerMs = ms
        var tev = kevent(
            ident: IdentTag.timer.rawValue,
            filter: Int16(EVFILT_TIMER),
            flags: UInt16(EV_ADD | EV_ENABLE),
            fflags: 0,
            data: ms,
            udata: UnsafeMutableRawPointer(bitPattern: IdentTag.timer.rawValue)
        )
        _ = kevent(kq, &tev, 1, nil, 0, nil)
    }

    private func drainRouteSocket() -> Bool {
        guard routeSock >= 0 else { return false }
        var buf = [UInt8](repeating: 0, count: 4096)
        var relevant = false
        while true {
            let n = recv(routeSock, &buf, buf.count, MSG_DONTWAIT)
            if n <= 0 { break }
            if n >= 12 {
                let rtmType = Int32(buf[3])
                switch rtmType {
                case RTM_IFINFO, RTM_IFINFO2, RTM_NEWADDR, RTM_DELADDR:
                    relevant = true
                case RTM_ADD, RTM_DELETE, RTM_CHANGE:
                    let rtmFlags = Int32(buf[8])
                        | (Int32(buf[9]) << 8)
                        | (Int32(buf[10]) << 16)
                        | (Int32(buf[11]) << 24)
                    if (rtmFlags & (RTF_LLINFO | RTF_WASCLONED)) == 0 && (rtmFlags & RTF_GATEWAY) != 0 {
                        relevant = true
                    }
                default:
                    break
                }
            }
        }
        return relevant
    }

    private func handleTimerTick() -> String {
        guard let dev = TelemetryMath.detectActiveHotspotDev() else {
            if !activeHotspotDev.isEmpty {
                activeHotspotDev = ""
                prevIbytes = 0
                prevObytes = 0
                prevCheckNs = 0
                fastCooldownTicks = 0
                for i in 0..<reflectors.count { reflectors[i].reset() }
            }
            setTimerInterval(idleTickMs)
            return "tick"
        }

        let nowNs = clock_gettime_nsec_np(CLOCK_UPTIME_RAW)
        let io = TelemetryMath.readInterfaceBytes64(dev)
        if dev != activeHotspotDev {
            activeHotspotDev = dev
            prevIbytes = io.ibytes
            prevObytes = io.obytes
            prevCheckNs = nowNs
            fastCooldownTicks = 0
            for i in 0..<reflectors.count { reflectors[i].reset() }
            return "tick"
        }

        let dtMs = max(1, Int((nowNs - prevCheckNs) / 1_000_000))
        let dIn: UInt64 = io.ibytes >= prevIbytes
            ? (io.ibytes - prevIbytes)
            : (prevIbytes <= UInt64(UInt32.max) ? UInt64(UInt32(truncatingIfNeeded: io.ibytes) &- UInt32(truncatingIfNeeded: prevIbytes)) : 0)
        let dOut: UInt64 = io.obytes >= prevObytes
            ? (io.obytes - prevObytes)
            : (prevObytes <= UInt64(UInt32.max) ? UInt64(UInt32(truncatingIfNeeded: io.obytes) &- UInt32(truncatingIfNeeded: prevObytes)) : 0)
        let dTotal = dIn &+ dOut
        prevIbytes = io.ibytes
        prevObytes = io.obytes
        prevCheckNs = nowNs

        // Active threshold: >= 64 KB/s (`dTotal * 1000 >= 65536 * dtMs`)
        let isTrafficActive = (dTotal &* 1000) >= (UInt64(65_536) &* UInt64(dtMs))
        if isTrafficActive {
            // Keep 24 fast ticks (12s) of 500ms post-burst tail so Pontryagin λ -> τ₀ converges rapidly
            fastCooldownTicks = 24
        } else if fastCooldownTicks > 0 {
            fastCooldownTicks -= 1
        } else {
            setTimerInterval(idleTickMs)
            return "tick"
        }

        setTimerInterval(fastTickMs)
        seqCounter &+= 3
        let specs = reflectors.map { ($0.ip, $0.icmpType) }
        let samples = TelemetryMath.probeMultiReflector(specs: specs, timeoutMs: 260, seqSeed: seqCounter)

        var rttExList = [Int]()
        var downExList = [Int]()
        var upExList = [Int]()
        var rawRtts = [Int]()

        for i in 0..<reflectors.count {
            if samples[i].responded {
                rawRtts.append(samples[i].rttMs)
            }
            if let ex = reflectors[i].updateAndExcess(samples[i]) {
                rttExList.append(ex.rttEx)
                if let d = ex.downEx, let u = ex.upEx {
                    downExList.append(d)
                    upExList.append(u)
                }
            }
        }

        let respCount = rawRtts.count
        let minRtt: Int
        let quorumDelta: Int
        if respCount == 3 {
            minRtt = rawRtts.min() ?? 260
            quorumDelta = TelemetryMath.median3(rttExList[0], rttExList[1], rttExList[2])
        } else if respCount == 2 {
            minRtt = min(rawRtts[0], rawRtts[1])
            quorumDelta = min(rttExList[0], rttExList[1])
        } else if respCount == 1 {
            minRtt = rawRtts[0]
            quorumDelta = rttExList[0]
        } else {
            minRtt = 350
            quorumDelta = 250
        }

        let owdMode: String
        let owdDownEx: Int
        let owdUpEx: Int
        if downExList.count >= 2 {
            owdMode = "owd"
            owdDownEx = min(downExList[0], downExList[1])
            owdUpEx = min(upExList[0], upExList[1])
        } else if downExList.count == 1 {
            owdMode = "owd"
            // Guard single OWD responder against single-reflector glitch by capping with quorum RTT excess + 8ms
            let cap = respCount >= 2 ? (quorumDelta + 8) : 350
            owdDownEx = min(downExList[0], cap)
            owdUpEx = min(upExList[0], cap)
        } else {
            owdMode = "rtt"
            owdDownEx = quorumDelta
            owdUpEx = quorumDelta
        }

        return "fasttick|\(dev)|\(dIn)|\(dOut)|\(dtMs)|\(minRtt)|\(quorumDelta)|\(owdDownEx)|\(owdUpEx)|\(owdMode)|\(respCount)"
    }

    func run() -> Never {
        signal(SIGPIPE, SIG_IGN)
        setvbuf(stdout, nil, _IOLBF, 0)

        kq = kqueue()
        if kq < 0 { exit(1) }

        if parentPid > 1 {
            if kill(parentPid, 0) != 0 { exit(0) }
            var pev = kevent(
                ident: UInt(parentPid),
                filter: Int16(EVFILT_PROC),
                flags: UInt16(EV_ADD | EV_ONESHOT),
                fflags: UInt32(NOTE_EXIT),
                data: 0,
                udata: UnsafeMutableRawPointer(bitPattern: IdentTag.parentPid.rawValue)
            )
            _ = kevent(kq, &pev, 1, nil, 0, nil)
        }

        routeSock = socket(AF_ROUTE, SOCK_RAW, 0)
        if routeSock >= 0 {
            let flags = fcntl(routeSock, F_GETFL, 0)
            _ = fcntl(routeSock, F_SETFL, flags | O_NONBLOCK)
            var rev = kevent(
                ident: UInt(routeSock),
                filter: Int16(EVFILT_READ),
                flags: UInt16(EV_ADD | EV_ENABLE),
                fflags: 0,
                data: 0,
                udata: nil
            )
            _ = kevent(kq, &rev, 1, nil, 0, nil)
        }

        lastScriptMtime = Self.fileMtime(scriptPath)
        lastPrefsMtime = Self.fileMtime(prefsPath)

        scriptDirFD = open(scriptDir, O_EVTONLY)
        registerVnode(scriptDirFD)
        prefsDirFD = open(prefsDir, O_EVTONLY)
        registerVnode(prefsDirFD)
        rearmFileFDs()

        var tev = kevent(
            ident: IdentTag.timer.rawValue,
            filter: Int16(EVFILT_TIMER),
            flags: UInt16(EV_ADD | EV_ENABLE),
            fflags: 0,
            data: idleTickMs,
            udata: UnsafeMutableRawPointer(bitPattern: IdentTag.timer.rawValue)
        )
        _ = kevent(kq, &tev, 1, nil, 0, nil)

        var events = Array<Darwin.kevent>(repeating: Darwin.kevent(), count: 16)
        let readyLine = "pid=\(getpid())\n"
        _ = readyLine.withCString { ptr in
            Darwin.write(STDOUT_FILENO, ptr, strlen(ptr))
        }

        while true {
            let n = kevent(kq, nil, 0, &events, Int32(events.count), nil)
            if n < 0 {
                if errno == EINTR { continue }
                exit(0)
            }
            if n == 0 { continue }

            var hasScript = false
            var hasPrefs = false
            var hasRoute = false
            var hasTick = false
            var needRearm = false

            func classify(_ ev: kevent) {
                if ev.filter == Int16(EVFILT_PROC) {
                    exit(0)
                } else if ev.filter == Int16(EVFILT_TIMER) {
                    hasTick = true
                } else if ev.filter == Int16(EVFILT_READ) && Int32(ev.ident) == routeSock {
                    if drainRouteSocket() {
                        hasRoute = true
                    }
                } else if ev.filter == Int16(EVFILT_VNODE) {
                    let fd = Int32(ev.ident)
                    if fd == scriptFD {
                        hasScript = true
                        if (ev.fflags & UInt32(NOTE_DELETE | NOTE_RENAME)) != 0 { needRearm = true }
                    } else if fd == prefsFD {
                        hasPrefs = true
                        if (ev.fflags & UInt32(NOTE_DELETE | NOTE_RENAME)) != 0 { needRearm = true }
                    } else if fd == scriptDirFD || fd == prefsDirFD {
                        let curS = Self.fileMtime(scriptPath)
                        if !Self.sameTimespec(curS, lastScriptMtime) {
                            lastScriptMtime = curS
                            hasScript = true
                            needRearm = true
                        }
                        let curP = Self.fileMtime(prefsPath)
                        if !Self.sameTimespec(curP, lastPrefsMtime) {
                            lastPrefsMtime = curP
                            hasPrefs = true
                            needRearm = true
                        }
                    }
                }
            }

            for i in 0..<Int(n) {
                classify(events[i])
            }

            if hasScript || hasPrefs || hasRoute {
                let windowNs: UInt64 = (hasScript || hasPrefs) ? 15_000_000 : 60_000_000
                let deadlineNs = clock_gettime_nsec_np(CLOCK_UPTIME_RAW) + windowNs
                while true {
                    let nowNs = clock_gettime_nsec_np(CLOCK_UPTIME_RAW)
                    if nowNs + 1_000_000 >= deadlineNs { break }
                    var ts = timespec(tv_sec: 0, tv_nsec: Int(deadlineNs - nowNs))
                    let m = kevent(kq, nil, 0, &events, Int32(events.count), &ts)
                    if m <= 0 { break }
                    for j in 0..<Int(m) {
                        classify(events[j])
                    }
                }
            }

            if needRearm {
                lastScriptMtime = Self.fileMtime(scriptPath)
                lastPrefsMtime = Self.fileMtime(prefsPath)
                rearmFileFDs()
            }

            var outLine = ""
            if hasScript || hasPrefs || hasRoute {
                var tags: [String] = []
                if hasScript { tags.append("script") }
                if hasPrefs  { tags.append("prefs") }
                if hasRoute  { tags.append("route") }
                outLine = tags.joined(separator: ",")
            } else if hasTick {
                outLine = handleTimerTick()
            }

            if !outLine.isEmpty {
                let line = outLine + "\n"
                let written = line.withCString { ptr in
                    Darwin.write(STDOUT_FILENO, ptr, strlen(ptr))
                }
                if written <= 0 {
                    exit(0)
                }
            }
        }
    }
}

func runStandaloneProbe(iface: String, timeoutMs: Int) -> Never {
    let io = TelemetryMath.readInterfaceBytes64(iface)
    let specs: [(String, UInt8)] = [
        ("9.9.9.9", 13),
        ("149.112.112.112", 13),
        ("1.1.1.1", 8)
    ]
    let s = TelemetryMath.probeMultiReflector(specs: specs, timeoutMs: timeoutMs, seqSeed: 100)
    let rtts = s.filter { $0.responded }.map { $0.rttMs }
    let quorumRtt: Int
    if rtts.count == 3 {
        quorumRtt = TelemetryMath.median3(rtts[0], rtts[1], rtts[2])
    } else if rtts.count == 2 {
        quorumRtt = min(rtts[0], rtts[1])
    } else if rtts.count == 1 {
        quorumRtt = rtts[0]
    } else {
        quorumRtt = timeoutMs
    }
    let owdSamples = s.filter { $0.responded && $0.owdValid }
    let owdMode = owdSamples.isEmpty ? "rtt" : "owd"
    let upRaw = owdSamples.first?.upRawMs ?? 0
    let downRaw = owdSamples.first?.downRawMs ?? 0
    let r0 = s[0].responded ? "\(s[0].rttMs)" : "timeout"
    let r1 = s[1].responded ? "\(s[1].rttMs)" : "timeout"
    let r2 = s[2].responded ? "\(s[2].rttMs)" : "timeout"
    print("\(io.ibytes)|\(io.obytes)|\(quorumRtt)|\(upRaw)|\(downRaw)|\(owdMode)|\(owdSamples.count)|\(rtts.count)|\(r0),\(r1),\(r2)")
    exit(0)
}

let resolvedHome: String = {
    if let envHome = ProcessInfo.processInfo.environment["TETHER_HOME"], !envHome.isEmpty {
        return envHome
    }
    var st = stat()
    if stat("/dev/console", &st) == 0 && st.st_uid != 0, let pw = getpwuid(st.st_uid) {
        let dir = String(cString: pw.pointee.pw_dir)
        if !dir.isEmpty && dir != "/var/root" { return dir }
    }
    let home = FileManager.default.homeDirectoryForCurrentUser.path
    return (home.isEmpty || home == "/var/root") ? NSHomeDirectory() : home
}()
let resolvedBinDir: String = {
    let arg0 = CommandLine.arguments.first ?? "/usr/local/bin/tether-events"
    let url = URL(fileURLWithPath: arg0).resolvingSymlinksInPath().deletingLastPathComponent()
    return url.path.isEmpty ? "\(resolvedHome)/bin" : url.path
}()

var scriptArg = "\(resolvedBinDir)/tether-optimize"
var prefsArg = "\(resolvedHome)/.tether-optimize.prefs"
var tickArg = 3000
var ppidArg: pid_t = getppid()

let args = CommandLine.arguments
if args.count >= 2 && args[1] == "--probe" {
    let dev = args.count >= 3 ? args[2] : "en0"
    let tmo = (args.count >= 4 ? Int(args[3]) : nil) ?? 320
    runStandaloneProbe(iface: dev, timeoutMs: tmo)
}

var idx = 1
while idx < args.count {
    switch args[idx] {
    case "--script":
        if idx + 1 < args.count { scriptArg = args[idx + 1]; idx += 2 } else { idx += 1 }
    case "--prefs":
        if idx + 1 < args.count { prefsArg = args[idx + 1]; idx += 2 } else { idx += 1 }
    case "--tick-ms":
        if idx + 1 < args.count, let v = Int(args[idx + 1]) { tickArg = v; idx += 2 } else { idx += 1 }
    case "--parent-pid":
        if idx + 1 < args.count, let v = Int32(args[idx + 1]) { ppidArg = v; idx += 2 } else { idx += 1 }
    default:
        idx += 1
    }
}

let reactor = KernelEventReactor(
    scriptPath: scriptArg,
    prefsPath: prefsArg,
    tickMs: tickArg,
    parentPid: ppidArg
)
reactor.run()
