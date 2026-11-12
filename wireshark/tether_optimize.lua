-- tether_optimize.lua — Native Wireshark 4.x Lua Post-Dissector for tether-optimize
--
-- Automatically annotates every ARP, IPv4, and IPv6 frame with:
--   1. Layer-3 MTU compliance (Home PPPoE 1492 B vs Cellular Hotspot 1420 B)
--   2. TCP SYN MSS clamping tier (1220 / 1332 / 1380 / 1432 / 1452 B) & AccECN/L4S flags
--   3. Dummynet Pipe classification (Fast-Lane #10/#11 vs Bulk #12/#13 vs Overlay vs Local Guard)
--   4. Tailscale WireGuard Disco (`TS💬` magic 54:53:f0:9f:92:ac) control-plane decoding
--   5. Multi-record mDNS / Companion-Link (`rpBA` / `rpHN` / `rpAD`), ARP spoof, cross-subnet
--      VLAN reflection, SNMP sweep, and Tailscale / ZeroTier Watchlist intrusion detection
--      (site-local peers from tether_peers.lua, L2 SNAT).
--
-- Display Filter Fields:
--   tether.l3_len                (uint16) : Exact L3 packet size in bytes (ip.len or ipv6.plen + 40)
--   tether.pppoe_safe            (bool)   : True iff l3_len <= 1492 (PPPoE WAN safe)
--   tether.hotspot_safe          (bool)   : True iff l3_len <= 1420 (Cellular GTP/CLAT46 safe)
--   tether.fragmented            (bool)   : True iff IPv4 fragment or IPv6 Fragment Header present
--   tether.syn_mss               (uint16) : TCP SYN advertised MSS (tcp.options.mss_val)
--   tether.mss_tier              (string) : Clamping profile tier for TCP SYN packets
--   tether.fast_lane             (bool)   : True iff classified into Dummynet Fast-Lane (#10/#11)
--   tether.dummynet_pipe         (string) : Dummynet queue / firewall rule classification
--   tether.ecn                   (string) : L4S / ECN codepoint ("L4S ECT(1)", "Classic ECN ECT(0)", "CE", "Not-ECT")
--   tether.syn_ecn               (string) : TCP SYN/SYN-ACK ECN / AccECN negotiation state
--   tether.icmp_owd              (string) : RFC 792 Type 13/14 OWD or Echo Quorum annotation
--   tether.tailscale.disco       (string) : Decoded Tailscale Disco (`TS💬`) control frame metadata
--   tether.security.suspect_peer (string) : Matched watchlist peer identity (site-local, Sounio-Language, etc.)
--   tether.security.anomaly      (string) : Accumulated("; ") overlay/Tailscale manipulation or intrusion signatures
--   tether.security.severity     (string) : Alert severity ("HIGH" targeted watchlist/intrusion vs "LOW" ambient bridge noise)

if rawget(_G, "__TETHER_OPTIMIZE_LUA_LOADED") then
    return
end
rawset(_G, "__TETHER_OPTIMIZE_LUA_LOADED", true)

local tether_proto = Proto("tether", "Tether-Optimize Network & QoS Audit")

-- Protocol Fields
local pf_l3_len        = ProtoField.uint16("tether.l3_len",                "Layer-3 Packet Length (B)", base.DEC)
local pf_pppoe_safe    = ProtoField.bool("tether.pppoe_safe",              "PPPoE 1492 WAN Safe (<=1492B)")
local pf_hotspot_safe  = ProtoField.bool("tether.hotspot_safe",            "Hotspot 1420 MTU Safe (<=1420B)")
local pf_fragmented    = ProtoField.bool("tether.fragmented",              "IP Fragmented Packet")
local pf_syn_mss       = ProtoField.uint16("tether.syn_mss",               "TCP SYN Advertised MSS (B)", base.DEC)
local pf_mss_tier      = ProtoField.string("tether.mss_tier",              "TCP MSS Clamping Tier")
local pf_fast_lane     = ProtoField.bool("tether.fast_lane",               "Dummynet Fast-Lane (#10/#11)")
local pf_dummynet_pipe = ProtoField.string("tether.dummynet_pipe",         "Dummynet Pipe / Firewall Class")
local pf_ecn           = ProtoField.string("tether.ecn",                   "L4S / ECN Codepoint")
local pf_syn_ecn       = ProtoField.string("tether.syn_ecn",               "TCP Handshake ECN Negotiation")
local pf_icmp_owd      = ProtoField.string("tether.icmp_owd",              "RFC 792 ICMP Timestamp OWD")
local pf_ts_disco      = ProtoField.string("tether.tailscale.disco",       "Tailscale Disco Control Frame")
local pf_suspect_peer  = ProtoField.string("tether.security.suspect_peer", "Watchlist Peer Identity")
local pf_sec_anomaly   = ProtoField.string("tether.security.anomaly",      "Overlay / Tailscale Security Anomaly")
local pf_sec_severity  = ProtoField.string("tether.security.severity",     "Security Alert Severity")

tether_proto.fields = {
    pf_l3_len,
    pf_pppoe_safe,
    pf_hotspot_safe,
    pf_fragmented,
    pf_syn_mss,
    pf_mss_tier,
    pf_fast_lane,
    pf_dummynet_pipe,
    pf_ecn,
    pf_syn_ecn,
    pf_icmp_owd,
    pf_ts_disco,
    pf_suspect_peer,
    pf_sec_anomaly,
    pf_sec_severity
}

-- Expert Info Warnings
local ef_oversized_pppoe = ProtoExpert.new(
    "tether.expert.oversized_pppoe",
    "Tether-Optimize: L3 packet exceeds 1492 B PPPoE WAN MTU (DF fragmentation risk)",
    expert.group.PROTOCOL,
    expert.severity.WARN
)
local ef_unclamped_mss = ProtoExpert.new(
    "tether.expert.unclamped_mss",
    "Tether-Optimize: TCP SYN MSS exceeds 1452 B PPPoE ceiling",
    expert.group.PROTOCOL,
    expert.severity.WARN
)
local ef_ip_fragment = ProtoExpert.new(
    "tether.expert.ip_fragment",
    "Tether-Optimize: IP fragmentation detected on wire",
    expert.group.REASSEMBLE,
    expert.severity.WARN
)
local ef_rogue_dhcp = ProtoExpert.new(
    "tether.expert.rogue_dhcp",
    "Tether-Optimize: BOOTP/DHCP frame observed (verify en9 rogue DHCP guard)",
    expert.group.SECURITY,
    expert.severity.NOTE
)
local ef_suspect_peer = ProtoExpert.new(
    "tether.expert.suspect_peer",
    "Tailscale/Overlay Watchlist: Traffic from/to a configured peer",
    expert.group.SECURITY,
    expert.severity.WARN
)
local ef_overlay_intrusion = ProtoExpert.new(
    "tether.expert.overlay_intrusion",
    "Tailscale/Overlay Security Alert: High-severity probe, masquerade, or manipulation attempt",
    expert.group.SECURITY,
    expert.severity.ERROR
)
local ef_overlay_noise = ProtoExpert.new(
    "tether.expert.overlay_noise",
    "Tailscale/Overlay Ambient Anomaly: Bridge SNAT rewrite or cross-VLAN broadcast noise (PF-blocked)",
    expert.group.SECURITY,
    expert.severity.NOTE
)

tether_proto.experts = {
    ef_oversized_pppoe,
    ef_unclamped_mss,
    ef_ip_fragment,
    ef_rogue_dhcp,
    ef_suspect_peer,
    ef_overlay_intrusion,
    ef_overlay_noise
}

-- Field Extractors
local f_ip_len       = Field.new("ip.len")
local f_ipv6_plen    = Field.new("ipv6.plen")
local f_ip_src       = Field.new("ip.src")
local f_ip_dst       = Field.new("ip.dst")
local f_ipv6_src     = Field.new("ipv6.src")
local f_ipv6_dst     = Field.new("ipv6.dst")
local f_eth_src      = Field.new("eth.src")
local f_eth_dst      = Field.new("eth.dst")
local f_iface_name   = Field.new("frame.interface_name")
local f_ip_ecn       = Field.new("ip.dsfield.ecn")
local f_ipv6_ecn     = Field.new("ipv6.tclass.ecn")
local f_ip_frag_off  = Field.new("ip.frag_offset")
local f_ip_mf        = Field.new("ip.flags.mf")
local f_ipv6_fraghdr = Field.new("ipv6.fraghdr")
local f_tcp_syn      = Field.new("tcp.flags.syn")
local f_tcp_ack      = Field.new("tcp.flags.ack")
local f_tcp_ece      = Field.new("tcp.flags.ece")
local f_tcp_cwr      = Field.new("tcp.flags.cwr")
local f_tcp_ae       = Field.new("tcp.flags.ae")
local f_tcp_mss      = Field.new("tcp.options.mss_val")
local f_tcp_srcport  = Field.new("tcp.srcport")
local f_tcp_dstport  = Field.new("tcp.dstport")
local f_udp_srcport  = Field.new("udp.srcport")
local f_udp_dstport  = Field.new("udp.dstport")
local f_udp_payload  = Field.new("udp.payload")
local f_icmp         = Field.new("icmp")
local f_icmp_type    = Field.new("icmp.type")
local f_icmpv6       = Field.new("icmpv6")
local f_dhcp         = Field.new("dhcp")
local f_dhcp_chaddr  = Field.new("dhcp.hw.mac_addr")
local f_dhcp_req_ip  = Field.new("dhcp.option.requested_ip_address")
local f_dhcp_msgtype = Field.new("dhcp.option.dhcp")
local f_dhcp_host    = Field.new("dhcp.option.hostname")
local f_dhcp_ciaddr  = Field.new("dhcp.ip.client")
local f_dhcp_yiaddr  = Field.new("dhcp.ip.your")
local f_frame_protos = Field.new("frame.protocols")
local f_llc_ctrl     = Field.new("llc.control")
local f_arp_opcode   = Field.new("arp.opcode")
local f_arp_src_ip   = Field.new("arp.src.proto_ipv4")
local f_arp_dst_ip   = Field.new("arp.dst.proto_ipv4")
local f_arp_src_mac  = Field.new("arp.src.hw_mac")
local f_dns_qr       = Field.new("dns.flags.response")
local f_dns_auth_rr  = Field.new("dns.count.auth_rr")
local f_dns_qry      = Field.new("dns.qry.name")
local f_dns_resp     = Field.new("dns.resp.name")
local f_dns_srv_tgt  = Field.new("dns.srv.target")
local f_dns_txt      = Field.new("dns.txt")
local f_dns_a        = Field.new("dns.a")
local f_dns_aaaa     = Field.new("dns.aaaa")

local FAST_LANE_PORTS = {
    [22]    = true, -- SSH
    [53]    = true, -- DNS
    [123]   = true, -- NTP
    [853]   = true, -- DNS-over-TLS (DoT)
    [3478]  = true, -- STUN
    [41641] = true, -- Tailscale SystemExtension WireGuard
    [41642] = true  -- Tailscale Userspace WireGuard
}

local LOCAL_GUARD_PORTS = {
    [3000]  = true, -- Next.js dev server
    [7100]  = true, -- local API
    [8787]  = true, -- Tailscale webhook listener
    [11434] = true  -- Ollama API
}

local SENSITIVE_SERVICE_PORTS = {
    [22]    = "SSH (:22)",
    [88]    = "Kerberos (:88)",
    [161]   = "SNMP (:161)",
    [162]   = "SNMP Trap (:162)",
    [445]   = "SMB (:445)",
    [1055]  = "Tailscale SOCKS5 (:1055)",
    [3000]  = "Next.js (:3000)",
    [3283]  = "Apple Remote Desktop (:3283)",
    [5900]  = "VNC/ScreenSharing (:5900)",
    [7100]  = "Local API (:7100)",
    [8787]  = "Webhook (:8787)",
    [11434] = "Ollama API (:11434)",
    [59124] = "Tailscale PeerAPI v6 (:59124)",
    [62411] = "Tailscale PeerAPI v4 (:62411)"
}

-- Site-local peer labels. The installer writes tether_peers.lua beside this file
-- when a local peer set exists; without it the dissector runs with no named peers.
local function load_local_peers()
    local src = debug.getinfo(1, "S").source
    local dir = src:match("^@(.*[/\\])") or "./"
    local chunk = loadfile(dir .. "tether_peers.lua")
    if not chunk then return {} end
    local ok, peers = pcall(chunk)
    if not ok or type(peers) ~= "table" then return {} end
    return peers
end

local PEERS = load_local_peers()

-- Direct watchlist peers (HIGH severity on direct IP traffic)
local DIRECT_WATCHLIST_IPS = PEERS.direct or {}

-- Indirect / bridge / router watchlist IPs & legitimate bridge MACs
local T560_VMBR0_MAC = PEERS.bridge_primary_mac or ""
local BRIDGE_WATCHLIST_IPS = PEERS.bridge or {}
local BRIDGE_SNAT_IPS = PEERS.bridge_snat_ips or {}
local KNOWN_BRIDGE_MACS = PEERS.bridge_macs or {}

-- Known mDNS cross-VLAN repeaters & Sleep Proxies (qr=1 reflections are LOW, not HIGH masquerades)
local MDNS_PROXY_MACS = PEERS.mdns_proxies or {}

local WATCHLIST_MACS = PEERS.watchlist_macs or {}

-- Local LAN shape (prefixes of your own subnets, broadcast addresses)
local LAN_PREFIXES = PEERS.lan_prefixes or { "169.254." }
local LAN_BROADCASTS = PEERS.lan_broadcasts or { "255.255.255.255" }
local FINGERPRINTS = PEERS.fingerprints or {}

local function has_prefix(value, prefixes)
    if not value or value == "" then return false end
    for _, prefix in ipairs(prefixes) do
        if string.sub(value, 1, #prefix) == prefix then return true end
    end
    return false
end

local SELF_IPS = PEERS.self_ips or {}

-- Pinned ARP bindings to detect L2 ARP spoofing on the local segment
local PINNED_ARP_MACS = PEERS.pinned_arp_macs or {}
local GATEWAY_IPS = PEERS.gateway_ips or {}

-- Per-capture observed ARP sender IP -> MAC map (reset on capture reload via tether_proto.init)
local observed_arp_macs = {}

function tether_proto.init()
    observed_arp_macs = {}
end

local function is_gateway_or_self_arp_target(ip_s)
    if SELF_IPS[ip_s] or PINNED_ARP_MACS[ip_s] or GATEWAY_IPS[ip_s] then
        return true
    end
    return false
end

local function to_num(fi)
    if not fi then return nil end
    local ok, v = pcall(function() return tonumber(tostring(fi)) end)
    if ok and v then return v end
    return nil
end

local function to_bool(fi)
    if not fi then return false end
    local s = tostring(fi)
    return (s == "True" or s == "true" or s == "1")
end

local function to_str(fi)
    if not fi then return nil end
    return tostring(fi)
end

-- Joins ALL FieldInfo values returned by a Wireshark Field extractor (prevents multi-record mDNS blindness)
local function join_all_fields(extractor)
    local ok, vals = pcall(function() return { extractor() } end)
    if not ok or not vals or #vals == 0 then
        return ""
    end
    local out = {}
    local seen = {}
    for i = 1, #vals do
        local s = tostring(vals[i])
        if s ~= "" and not seen[s] then
            seen[s] = true
            out[#out + 1] = s
        end
    end
    return table.concat(out, " ")
end

local function is_overlay_iface(iface)
    if iface == "feth110" or iface == "feth5110" then
        return true
    end
    if string.sub(iface, 1, 4) == "utun" then
        return true
    end
    return false
end

local function is_cross_subnet_feth_ipv4(iface, ip_s)
    if iface ~= "feth110" and iface ~= "feth5110" then
        return false
    end
    if ip_s == "" or ip_s == "0.0.0.0" then
        return false
    end
    if has_prefix(ip_s, LAN_PREFIXES) then
        return false
    end
    return true
end

local function is_cloudflare_doh_dot_target(ip_s, port)
    if port ~= 443 and port ~= 853 then
        return false
    end
    if ip_s == "1.1.1.1" or ip_s == "1.0.0.1" then
        return true
    end
    local low_ip = string.lower(ip_s or "")
    if string.sub(low_ip, 1, 15) == "2606:4700:4700:" then
        return true
    end
    return false
end

local function match_hostname_watchlist(hname)
    if not hname or hname == "" then
        return nil
    end
    local low = string.lower(hname)
    for _, fp in ipairs(FINGERPRINTS) do
        for _, pattern in ipairs(fp.hostnames or {}) do
            if string.find(low, string.lower(pattern), 1, true) then
                return fp.label
            end
        end
    end
    return nil
end

-- Matches mDNS/DNS records AND Apple Continuity (`rpBA`/`rpHN`/`rpAD`) TXT fingerprints across all records
local function match_dns_watchlist(dns_blob, dns_addrs)
    if dns_blob == "" and dns_addrs == "" then
        return nil
    end
    local upper_blob = string.upper(dns_blob or "")
    for _, fp in ipairs(FINGERPRINTS) do
        for _, needle in ipairs(fp.dns_substrings or {}) do
            if string.find(dns_blob, needle, 1, true)
               or string.find(upper_blob, string.upper(needle), 1, true) then
                return fp.label
            end
        end
        for _, addr in ipairs(fp.addresses or {}) do
            if string.find(dns_addrs or "", addr, 1, true) then
                return fp.label
            end
        end
    end
    return nil
end

local DHCP_MSG_NAMES = {
    ["1"] = "Discover",
    ["2"] = "Offer",
    ["3"] = "Request",
    ["4"] = "Decline",
    ["5"] = "ACK",
    ["6"] = "NAK",
    ["7"] = "Release",
    ["8"] = "Inform"
}

function tether_proto.dissector(buffer, pinfo, tree)
    local iface_s   = to_str(f_iface_name()) or ""
    local eth_src_s = string.lower(to_str(f_eth_src()) or "")
    local eth_dst_s = string.lower(to_str(f_eth_dst()) or "")

    -- 1. Layer-2 ARP Security Inspection (runs on non-IP ARP frames!)
    local arp_op = to_num(f_arp_opcode())
    if arp_op then
        local arp_sip      = to_str(f_arp_src_ip()) or ""
        local arp_dip      = to_str(f_arp_dst_ip()) or ""
        local raw_arp_smac = string.lower(to_str(f_arp_src_mac()) or "")
        local arp_smac     = raw_arp_smac ~= "" and raw_arp_smac or eth_src_s
        local direct_arp   = WATCHLIST_MACS[arp_smac] or WATCHLIST_MACS[eth_src_s]
                          or DIRECT_WATCHLIST_IPS[arp_sip] or DIRECT_WATCHLIST_IPS[arp_dip]
        local bridge_arp   = BRIDGE_WATCHLIST_IPS[arp_sip] or BRIDGE_WATCHLIST_IPS[arp_dip]
                          or KNOWN_BRIDGE_MACS[arp_smac] or KNOWN_BRIDGE_MACS[eth_src_s]
        local suspect      = direct_arp or bridge_arp
        local anomalies = {}
        local severity  = nil

        -- Detect Ethernet source MAC vs ARP sender hardware MAC mismatch (classic L2 spoof technique)
        if eth_src_s ~= "" and raw_arp_smac ~= "" and eth_src_s ~= raw_arp_smac then
            anomalies[#anomalies + 1] = "ARP_HEADER_MAC_MISMATCH (eth.src=" .. eth_src_s .. " != arp.src.hw_mac=" .. raw_arp_smac .. " for ip=" .. arp_sip .. ")"
            severity = "HIGH"
        end

        local pinned_mac = PINNED_ARP_MACS[arp_sip]
        if pinned_mac and ((arp_smac ~= "" and arp_smac ~= pinned_mac) or (eth_src_s ~= "" and eth_src_s ~= pinned_mac)) then
            local claimant = (eth_src_s ~= "" and eth_src_s ~= pinned_mac) and eth_src_s or arp_smac
            anomalies[#anomalies + 1] = "ARP_SPOOF_CONFLICT (ip=" .. arp_sip .. " claimed by " .. claimant .. ", expected " .. pinned_mac .. ")"
            severity = "HIGH"
        end

        -- Track sender IP -> MAC consistency across capture, flagging MAC flips on gateways/self or gratuitous ARP from watchlisted MACs
        if arp_sip ~= "" and arp_sip ~= "0.0.0.0" and arp_smac ~= "" then
            local prev_mac = observed_arp_macs[arp_sip]
            if not prev_mac then
                observed_arp_macs[arp_sip] = arp_smac
            elseif prev_mac ~= arp_smac then
                local flip_sev = (is_gateway_or_self_arp_target(arp_sip) or WATCHLIST_MACS[arp_smac] or WATCHLIST_MACS[eth_src_s]) and "HIGH" or "LOW"
                anomalies[#anomalies + 1] = "ARP_MAC_CHANGE_CONFLICT (ip=" .. arp_sip .. " flipped " .. prev_mac .. " -> " .. arp_smac .. ")"
                if flip_sev == "HIGH" then severity = "HIGH" elseif not severity then severity = "LOW" end
            end
        end

        if direct_arp then
            anomalies[#anomalies + 1] = "WATCHLIST_ARP_ACTIVITY (op=" .. tostring(arp_op) .. " " .. arp_sip .. " -> " .. arp_dip .. " mac=" .. (eth_src_s ~= "" and eth_src_s or arp_smac) .. ")"
            severity = "HIGH"
        end
        if is_cross_subnet_feth_ipv4(iface_s, arp_sip) then
            anomalies[#anomalies + 1] = "CROSS_SUBNET_ARP_LEAK (src=" .. arp_sip .. " -> " .. arp_dip .. " from " .. arp_smac .. " on " .. iface_s .. ")"
            if not severity then severity = "LOW" end
        end

        if suspect or #anomalies > 0 then
            local subtree = tree:add(tether_proto, "Tether-Optimize Network & QoS Audit (ARP)")
            subtree:add(pf_dummynet_pipe, "Overlay / LAN ARP Control")
            if suspect then
                subtree:add(pf_suspect_peer, suspect)
                if direct_arp then
                    subtree:add_proto_expert_info(ef_suspect_peer)
                end
            end
            if #anomalies > 0 then
                local anom_str = table.concat(anomalies, "; ")
                local sev_str  = severity or "LOW"
                subtree:add(pf_sec_anomaly, anom_str)
                subtree:add(pf_sec_severity, sev_str)
                if sev_str == "HIGH" then
                    subtree:add_proto_expert_info(ef_overlay_intrusion)
                else
                    subtree:add_proto_expert_info(ef_overlay_noise)
                end
            end
        end
        return
    end

    -- 2. Non-IP / Non-ARP Layer-2 Watchlist Visibility (e.g. IEEE 802.2 LLC XID/RNR broadcasts)
    local ip_len_fi    = f_ip_len()
    local ipv6_plen_fi = f_ipv6_plen()
    if not ip_len_fi and not ipv6_plen_fi then
        local l2_watch = WATCHLIST_MACS[eth_src_s] or WATCHLIST_MACS[eth_dst_s]
        if l2_watch then
            local protos_s   = to_str(f_frame_protos()) or "eth:l2"
            local llc_ctrl_s = to_str(f_llc_ctrl())
            local active_mac = WATCHLIST_MACS[eth_src_s] and eth_src_s or eth_dst_s
            local dst_label  = eth_dst_s ~= "" and eth_dst_s or "broadcast"
            local ctrl_part  = llc_ctrl_s and (" ctrl=" .. llc_ctrl_s) or ""
            local on_part    = iface_s ~= "" and (" on " .. iface_s) or ""
            local l2_anom    = "WATCHLIST_L2_LLC_ACTIVITY (protos=" .. protos_s .. ctrl_part .. " mac=" .. active_mac .. " " .. (eth_src_s ~= "" and eth_src_s or active_mac) .. " -> " .. dst_label .. on_part .. ")"
            local subtree    = tree:add(tether_proto, "Tether-Optimize Network & QoS Audit (L2/LLC)")
            subtree:add(pf_dummynet_pipe, "Overlay / LAN L2 Control")
            subtree:add(pf_suspect_peer, l2_watch)
            subtree:add_proto_expert_info(ef_suspect_peer)
            subtree:add(pf_sec_anomaly, l2_anom)
            subtree:add(pf_sec_severity, "HIGH")
            subtree:add_proto_expert_info(ef_overlay_intrusion)
        end
        return
    end

    -- 3. IPv4 / IPv6 Layer-3 & Layer-4 Audit
    local l3_len = 0
    local is_ipv6 = false
    if ip_len_fi then
        l3_len = to_num(ip_len_fi) or 0
    elseif ipv6_plen_fi then
        l3_len = (to_num(ipv6_plen_fi) or 0) + 40
        is_ipv6 = true
    end

    local pppoe_safe   = (l3_len <= 1492)
    local hotspot_safe = (l3_len <= 1420)

    local frag_off = to_num(f_ip_frag_off()) or 0
    local mf_flag  = to_bool(f_ip_mf())
    local v6_frag  = (f_ipv6_fraghdr() ~= nil)
    local is_frag  = (frag_off > 0) or mf_flag or v6_frag

    -- ECN codepoint decoding
    local ecn_val = to_num(f_ip_ecn()) or to_num(f_ipv6_ecn()) or 0
    local ecn_str = "Not-ECT"
    if ecn_val == 1 then
        ecn_str = "L4S ECT(1)"
    elseif ecn_val == 2 then
        ecn_str = "Classic ECN ECT(0)"
    elseif ecn_val == 3 then
        ecn_str = "Congestion Experienced (CE)"
    end

    -- Dummynet pipe & firewall classification (ignore inner L4 headers quoted inside ICMP/ICMPv6 errors)
    local is_icmp_pkt = (f_icmp() ~= nil) or (f_icmpv6() ~= nil)
    local tcp_sport   = (not is_icmp_pkt) and to_num(f_tcp_srcport()) or nil
    local tcp_dport   = (not is_icmp_pkt) and to_num(f_tcp_dstport()) or nil
    local udp_sport   = (not is_icmp_pkt) and to_num(f_udp_srcport()) or nil
    local udp_dport   = (not is_icmp_pkt) and to_num(f_udp_dstport()) or nil
    local is_tcp_syn  = (not is_icmp_pkt) and to_bool(f_tcp_syn())
    local is_tcp_ack  = (not is_icmp_pkt) and to_bool(f_tcp_ack())

    local pipe_str = "Bulk Pipe (#12/#13)"
    local is_fast_lane = false
    if is_icmp_pkt then
        pipe_str = "Fast-Lane (#10/#11: ICMP/Control)"
        is_fast_lane = true
    elseif tcp_sport and (LOCAL_GUARD_PORTS[tcp_sport] or LOCAL_GUARD_PORTS[tcp_dport]) then
        pipe_str = "Local-Service Firewall Guard (:3000/:7100/:8787/:11434)"
    elseif (tcp_sport and (FAST_LANE_PORTS[tcp_sport] or FAST_LANE_PORTS[tcp_dport])) or
           (udp_sport and (FAST_LANE_PORTS[udp_sport] or FAST_LANE_PORTS[udp_dport])) then
        pipe_str = "Fast-Lane (#10/#11: Interactive/Tailscale)"
        is_fast_lane = true
    elseif udp_sport and (udp_sport == 9993 or udp_dport == 9993) then
        pipe_str = "Overlay Transport (ZeroTier :9993)"
    end

    local subtree = tree:add(tether_proto, "Tether-Optimize Network & QoS Audit")
    subtree:add(pf_l3_len, l3_len)
    subtree:add(pf_pppoe_safe, pppoe_safe)
    subtree:add(pf_hotspot_safe, hotspot_safe)
    subtree:add(pf_fragmented, is_frag)
    subtree:add(pf_fast_lane, is_fast_lane)
    subtree:add(pf_dummynet_pipe, pipe_str)
    subtree:add(pf_ecn, ecn_str)

    -- 4. Tailscale Disco (`TS💬` magic 54:53:f0:9f:92:ac) Control-Plane Detection
    local ip_src_s  = to_str(f_ip_src()) or to_str(f_ipv6_src()) or ""
    local ip_dst_s  = to_str(f_ip_dst()) or to_str(f_ipv6_dst()) or ""
    local ipv4_src  = to_str(f_ip_src()) or ""
    local ipv4_dst  = to_str(f_ip_dst()) or ""
    local disco_str = nil
    if udp_sport then
        local upay_hex = string.lower(string.gsub(to_str(f_udp_payload()) or "", ":", ""))
        if string.sub(upay_hex, 1, 12) == "5453f09f92ac" then
            local sender_key_prefix = string.sub(upay_hex, 13, 28)
            disco_str = "TS-Disco [sender_key=" .. sender_key_prefix .. "… " .. ip_src_s .. ":" .. tostring(udp_sport) .. " -> " .. ip_dst_s .. ":" .. tostring(udp_dport) .. "]"
            subtree:add(pf_ts_disco, disco_str)
        end
    end

    -- 5. DHCP Lease Inspection (Option 50 Requested IP, yiaddr/ciaddr, Option 12 Hostname, Option 53 Msg Type)
    local has_dhcp       = (not is_icmp_pkt) and (f_dhcp() ~= nil)
    local dhcp_chaddr    = ""
    local dhcp_req_ip    = ""
    local dhcp_yiaddr    = ""
    local dhcp_ciaddr    = ""
    local dhcp_msgtype   = ""
    local dhcp_host      = ""
    local eff_dhcp_ip    = ""
    local dhcp_watch_peer = nil
    if has_dhcp then
        dhcp_chaddr  = string.lower(to_str(f_dhcp_chaddr()) or "")
        dhcp_req_ip  = to_str(f_dhcp_req_ip()) or ""
        dhcp_yiaddr  = to_str(f_dhcp_yiaddr()) or ""
        dhcp_ciaddr  = to_str(f_dhcp_ciaddr()) or ""
        dhcp_msgtype = to_str(f_dhcp_msgtype()) or ""
        dhcp_host    = to_str(f_dhcp_host()) or ""
        if dhcp_req_ip ~= "" and dhcp_req_ip ~= "0.0.0.0" then
            eff_dhcp_ip = dhcp_req_ip
        elseif dhcp_yiaddr ~= "" and dhcp_yiaddr ~= "0.0.0.0" then
            eff_dhcp_ip = dhcp_yiaddr
        elseif dhcp_ciaddr ~= "" and dhcp_ciaddr ~= "0.0.0.0" then
            eff_dhcp_ip = dhcp_ciaddr
        end
        dhcp_watch_peer = WATCHLIST_MACS[eth_src_s]
                       or WATCHLIST_MACS[dhcp_chaddr]
                       or DIRECT_WATCHLIST_IPS[eff_dhcp_ip]
                       or match_hostname_watchlist(dhcp_host)
    end

    -- 6. Multi-Record DNS/mDNS/Companion-Link & Overlay Watchlist Intrusion Detection
    local dns_is_resp  = false
    local dns_auth_cnt = 0
    local dns_suspect  = nil
    if not is_icmp_pkt then
        dns_is_resp      = to_bool(f_dns_qr())
        dns_auth_cnt     = to_num(f_dns_auth_rr()) or 0
        local dns_q_s    = join_all_fields(f_dns_qry)
        local dns_r_s    = join_all_fields(f_dns_resp)
        local dns_srv_s  = join_all_fields(f_dns_srv_tgt)
        local dns_txt_s  = join_all_fields(f_dns_txt)
        local dns_addr_s = join_all_fields(f_dns_a) .. " " .. join_all_fields(f_dns_aaaa)
        local dns_blob   = dns_q_s .. " " .. dns_r_s .. " " .. dns_srv_s .. " " .. dns_txt_s
        dns_suspect      = match_dns_watchlist(dns_blob, dns_addr_s)
    end

    -- Never grant mDNS proxy exemption if the L3 source IP itself is a direct watchlist peer
    local mdns_proxy  = (not DIRECT_WATCHLIST_IPS[ip_src_s]) and MDNS_PROXY_MACS[eth_src_s] or nil
    local matched_mac = WATCHLIST_MACS[eth_src_s] or WATCHLIST_MACS[eth_dst_s]
    local direct_peer = matched_mac
                     or dhcp_watch_peer
                     or DIRECT_WATCHLIST_IPS[ip_src_s] or DIRECT_WATCHLIST_IPS[ip_dst_s]
    local bridge_peer = BRIDGE_WATCHLIST_IPS[ip_src_s] or BRIDGE_WATCHLIST_IPS[ip_dst_s]
                     or KNOWN_BRIDGE_MACS[eth_src_s] or KNOWN_BRIDGE_MACS[eth_dst_s]
    local dns_peer    = (dns_suspect and mdns_proxy) and (mdns_proxy .. " -> " .. dns_suspect) or dns_suspect
    local suspect     = direct_peer or dns_peer or bridge_peer
    -- Only qr=1 non-proxy responses, direct watchlist peers, or RFC 6762 §8.1 ownership probes (auth_rr > 0) are HIGH claims;
    -- innocent third-party qr=0 queries carrying cached Known-Answer suppression records (RFC 6762 §7.1, auth_rr == 0) stay LOW.
    local dns_high_claim = (dns_suspect ~= nil)
                       and (not mdns_proxy)
                       and (dns_is_resp or direct_peer ~= nil or dns_auth_cnt > 0)

    local anomalies = {}
    local severity  = nil
    local function add_anomaly(msg, sev)
        anomalies[#anomalies + 1] = msg
        if sev == "HIGH" then
            severity = "HIGH"
        elseif not severity then
            severity = sev or "LOW"
        end
    end

    -- Signature DHCP: Watchlist MAC / Hostname / Requested-or-Assigned-IP DHCP Lease Activity (Option 50 / yiaddr)
    if has_dhcp and dhcp_watch_peer then
        local eff_mac    = (dhcp_chaddr ~= "" and dhcp_chaddr) or (eth_src_s ~= "" and eth_src_s) or "unknown"
        local req_label  = eff_dhcp_ip ~= "" and eff_dhcp_ip or "unspecified"
        local host_part  = dhcp_host ~= "" and (" hostname=" .. dhcp_host) or ""
        local mtype_name = DHCP_MSG_NAMES[dhcp_msgtype] or (dhcp_msgtype ~= "" and ("type-" .. dhcp_msgtype) or "DHCP")
        local on_part    = iface_s ~= "" and (" on " .. iface_s) or ""
        add_anomaly("WATCHLIST_DHCP_LEASE_REQUEST (" .. mtype_name .. " mac=" .. eff_mac .. " req_ip=" .. req_label .. host_part .. on_part .. ")", "HIGH")
    end

    -- Signature A: Bridge L2 SNAT Rewrite (bridge address with a non-primary source MAC)
    if BRIDGE_SNAT_IPS[ip_src_s] and eth_src_s ~= "" and eth_src_s ~= T560_VMBR0_MAC then
        local snat_sev = WATCHLIST_MACS[eth_src_s] and "HIGH" or "LOW"
        add_anomaly("BRIDGE_L2_SNAT_REWRITE (src=" .. ip_src_s .. " from MAC=" .. eth_src_s .. ")", snat_sev)
    end

    -- Signature B: Cross-Subnet IPv4 / 6-VLAN UniFi mDNS Reflector on ZeroTier feth110
    if is_cross_subnet_feth_ipv4(iface_s, ipv4_src) then
        local ref_sev = (dns_high_claim or WATCHLIST_MACS[eth_src_s] ~= nil) and "HIGH" or "LOW"
        add_anomaly("CROSS_SUBNET_MDNS_REFLECTOR (src=" .. ipv4_src .. " mac=" .. (eth_src_s ~= "" and eth_src_s or "unknown") .. " on " .. iface_s .. ")", ref_sev)
    end

    -- Signature C: Watchlist mDNS / Apple Companion-Link Masquerade vs Proxy Reflection vs Query (gated on qr=1)
    if dns_suspect then
        if dns_is_resp then
            if mdns_proxy then
                add_anomaly("WATCHLIST_MDNS_PROXY_REFLECTION (" .. dns_suspect .. " reflected by " .. mdns_proxy .. " src=" .. ip_src_s .. ")", "LOW")
            else
                add_anomaly("WATCHLIST_MDNS_MASQUERADE (" .. dns_suspect .. " via " .. (eth_src_s ~= "" and eth_src_s or ip_src_s) .. " src=" .. ip_src_s .. ")", "HIGH")
            end
        else
            local q_sev = dns_high_claim and "HIGH" or "LOW"
            local q_verb = (dns_auth_cnt > 0) and " ownership-probe by " or " queried by "
            add_anomaly("WATCHLIST_MDNS_QUERY (" .. dns_suspect .. q_verb .. ip_src_s .. ")", q_sev)
        end
    end

    -- Signature D: Direct IPv4/IPv6 Traffic OR Rotated-IP L2 MAC Traffic from Watchlist Hosts
    if DIRECT_WATCHLIST_IPS[ip_src_s] or DIRECT_WATCHLIST_IPS[ip_dst_s] then
        add_anomaly("WATCHLIST_DIRECT_TRAFFIC (src=" .. ip_src_s .. " -> dst=" .. ip_dst_s .. ")", "HIGH")
    elseif matched_mac then
        local active_mac = WATCHLIST_MACS[eth_src_s] and eth_src_s or eth_dst_s
        if not (has_dhcp and dhcp_watch_peer and (ip_src_s == "0.0.0.0" or ip_dst_s == "255.255.255.255")) then
            if not BRIDGE_WATCHLIST_IPS[ip_src_s] and not BRIDGE_WATCHLIST_IPS[ip_dst_s] then
                add_anomaly("WATCHLIST_MAC_IP_ROTATION (mac=" .. active_mac .. " using rotated ip " .. ip_src_s .. " -> " .. ip_dst_s .. ")", "HIGH")
            else
                add_anomaly("WATCHLIST_MAC_TRAFFIC (mac=" .. active_mac .. " " .. ip_src_s .. " -> " .. ip_dst_s .. ")", "HIGH")
            end
        end
    end

    -- Signature E: SNMP Enumeration Sweep (:161/:162) — omit ephemeral udp_sport so AlertDeduplicator collapses sweeps
    if udp_dport == 161 or udp_dport == 162 or udp_sport == 161 or udp_sport == 162 then
        if is_overlay_iface(iface_s) or suspect then
            local snmp_port = (udp_dport == 161 or udp_dport == 162) and udp_dport or udp_sport
            add_anomaly("SNMP_ENUMERATION_SWEEP (udp " .. ip_src_s .. " -> " .. ip_dst_s .. ":" .. tostring(snmp_port) .. " mac=" .. eth_src_s .. ")", "HIGH")
        end
    end

    -- Signature F: Sensitive Service Port Access on Overlay or from Watchlist Peer
    local dst_port = tcp_dport or udp_dport
    if dst_port and SENSITIVE_SERVICE_PORTS[dst_port] then
        local inbound_to_self = (not SELF_IPS[ip_src_s])
        if inbound_to_self and (is_overlay_iface(iface_s) or direct_peer or dns_high_claim) then
            add_anomaly("SENSITIVE_PORT_ACCESS (" .. SENSITIVE_SERVICE_PORTS[dst_port] .. " on " .. (iface_s ~= "" and iface_s or "overlay") .. " from " .. ip_src_s .. ")", "HIGH")
        end
    end

    -- Signature G: Unsolicited Inbound TCP SYN on Overlay Interfaces
    if is_tcp_syn and (not is_tcp_ack) and is_overlay_iface(iface_s) and SELF_IPS[ip_dst_s] and (not SELF_IPS[ip_src_s]) then
        add_anomaly("OVERLAY_INBOUND_TCP_SYN (" .. ip_src_s .. " -> " .. ip_dst_s .. ":" .. tostring(tcp_dport or 0) .. " on " .. iface_s .. ")", "HIGH")
    end

    -- Signature H: Tailscale Disco Probing + Tailscale Tunnel Route-Overlap / Overlay-in-Overlay / LAN Source-IP / Blackholed DoH/DoT SYNs
    if disco_str and (DIRECT_WATCHLIST_IPS[ip_src_s] or DIRECT_WATCHLIST_IPS[ip_dst_s] or BRIDGE_WATCHLIST_IPS[ip_src_s] or BRIDGE_WATCHLIST_IPS[ip_dst_s]) then
        local disco_sev = (DIRECT_WATCHLIST_IPS[ip_src_s] or DIRECT_WATCHLIST_IPS[ip_dst_s]) and "HIGH" or "LOW"
        add_anomaly("TAILSCALE_DISCO_WATCHLIST_PROBE (" .. ip_src_s .. " <-> " .. ip_dst_s .. ")", disco_sev)
    end
    if string.sub(iface_s, 1, 4) == "utun" then
        local is_lan_broadcast = false
        for _, bcast in ipairs(LAN_BROADCASTS) do
            if ip_dst_s == bcast then is_lan_broadcast = true break end
        end
        if SELF_IPS[ip_src_s] and is_lan_broadcast then
            add_anomaly("TAILSCALE_SUBNET_BROADCAST_LEAK (" .. ip_src_s .. " -> " .. ip_dst_s .. " on " .. iface_s .. " via an overlapping LAN route)", "LOW")
        elseif has_prefix(ipv4_src, LAN_PREFIXES) or has_prefix(ipv4_dst, LAN_PREFIXES) then
            local overlap_sev = (DIRECT_WATCHLIST_IPS[ipv4_src] or DIRECT_WATCHLIST_IPS[ipv4_dst]) and "HIGH" or "LOW"
            add_anomaly("TAILSCALE_ROUTE_OVERLAP_LEAK (LAN traffic " .. ipv4_src .. " -> " .. ipv4_dst .. " diverted onto " .. iface_s .. " instead of the LAN interface)", overlap_sev)
        end
        if udp_sport == 9993 or udp_dport == 9993 or udp_sport == 41641 or udp_dport == 41641 or udp_sport == 41642 or udp_dport == 41642 then
            local ov_port = (udp_dport == 9993 or udp_dport == 41641 or udp_dport == 41642) and udp_dport or udp_sport
            add_anomaly("OVERLAY_IN_OVERLAY_TUNNEL_RECURSION (udp " .. ip_src_s .. " -> " .. ip_dst_s .. ":" .. tostring(ov_port) .. " encapsulated inside " .. iface_s .. ")", "LOW")
        end
        if is_tcp_syn and (not is_tcp_ack) and is_cloudflare_doh_dot_target(ip_dst_s, tcp_dport) then
            add_anomaly("TAILSCALE_BLACKHOLED_DOH_DOT_SYN (tcp " .. ip_src_s .. " -> " .. ip_dst_s .. ":" .. tostring(tcp_dport) .. " on " .. iface_s .. ")", "LOW")
        end
        if has_prefix(ipv4_src, LAN_PREFIXES) then
            add_anomaly("TAILSCALE_LAN_SOURCE_IP_LEAK (Wi-Fi LAN source " .. ipv4_src .. " -> " .. ip_dst_s .. " leaked onto " .. iface_s .. ")", "LOW")
        end
    end

    if suspect then
        subtree:add(pf_suspect_peer, suspect)
        if direct_peer or dns_high_claim then
            subtree:add_proto_expert_info(ef_suspect_peer)
        end
    end
    if #anomalies > 0 then
        local anom_str = table.concat(anomalies, "; ")
        local sev_str  = severity or "LOW"
        subtree:add(pf_sec_anomaly, anom_str)
        subtree:add(pf_sec_severity, sev_str)
        if sev_str == "HIGH" then
            subtree:add_proto_expert_info(ef_overlay_intrusion)
        else
            subtree:add_proto_expert_info(ef_overlay_noise)
        end
    end

    local icmp_t = to_num(f_icmp_type())
    if icmp_t == 13 then
        subtree:add(pf_icmp_owd, "RFC 792 Type 13 Timestamp Request (OWD Probe)")
    elseif icmp_t == 14 then
        subtree:add(pf_icmp_owd, "RFC 792 Type 14 Timestamp Reply (Clock-Offset-Cancelled OWD)")
    elseif icmp_t == 8 or icmp_t == 0 then
        subtree:add(pf_icmp_owd, "RFC 792 Type 8/0 Echo Quorum Cross-Check")
    end

    if not pppoe_safe then
        subtree:add_proto_expert_info(ef_oversized_pppoe)
    end
    if is_frag then
        subtree:add_proto_expert_info(ef_ip_fragment)
    end
    if has_dhcp then
        subtree:add_proto_expert_info(ef_rogue_dhcp)
    end

    -- TCP SYN MSS & ECN Handshake Negotiation audit
    -- (macOS BPF taps outbound post-PF scrub, inbound pre-PF scrub)
    if is_tcp_syn then
        local is_ack  = is_tcp_ack
        local has_ece = to_bool(f_tcp_ece())
        local has_cwr = to_bool(f_tcp_cwr())
        local has_ae  = to_bool(f_tcp_ae())
        local syn_ecn = "Non-ECN"
        if not is_ack then
            if has_ae and has_ece and has_cwr then
                syn_ecn = "AccECN/L4S SYN (AE+CWR+ECE)"
            elseif has_ece and has_cwr then
                syn_ecn = "RFC3168 ECN SYN (CWR+ECE)"
            end
        else
            if has_ae then
                syn_ecn = "AccECN/L4S SYN-ACK"
            elseif has_ece and not has_cwr then
                syn_ecn = "RFC3168 ECN Accepted (ECE)"
            end
        end
        subtree:add(pf_syn_ecn, syn_ecn)

        local mss_val = to_num(f_tcp_mss())
        if mss_val then
            subtree:add(pf_syn_mss, mss_val)
            local tier
            if is_ack then
                if mss_val <= 1380 then
                    tier = "Inbound SYN-ACK pre-PF (<=1380B, Hotspot & PPPoE safe)"
                elseif mss_val <= 1432 then
                    tier = "Inbound SYN-ACK pre-PF (<=1432B, IPv6 PPPoE safe)"
                elseif mss_val <= 1452 then
                    tier = "Inbound SYN-ACK pre-PF (<=1452B, IPv4 PPPoE safe)"
                else
                    tier = "Inbound SYN-ACK pre-PF (>1452B, clamped in PF)"
                end
            else
                if mss_val <= 1220 then
                    tier = "Outbound SYN: Overlay Hotspot (<=1220B)"
                elseif mss_val <= 1332 then
                    tier = "Outbound SYN: Overlay Home PPPoE (<=1332B)"
                elseif mss_val <= 1380 then
                    tier = "Outbound SYN: Outer Hotspot (<=1380B)"
                elseif mss_val <= 1432 then
                    tier = "Outbound SYN: Outer Home PPPoE IPv6 (<=1432B)"
                elseif mss_val <= 1452 then
                    tier = "Outbound SYN: Outer Home PPPoE IPv4 (<=1452B)"
                else
                    tier = "UNCLAMPED Outbound SYN (>1452B - Fragmentation Risk!)"
                end
            end
            subtree:add(pf_mss_tier, tier)
            if (not is_ack) and (mss_val > 1452 or (is_ipv6 and mss_val > 1432)) then
                subtree:add_proto_expert_info(ef_unclamped_mss)
            end
        end
    end
end

register_postdissector(tether_proto)
