-- tether_optimize.lua — Native Wireshark 4.x Lua Post-Dissector for tether-optimize
--
-- Automatically annotates every IPv4/IPv6 frame with Layer-3 MTU compliance
-- (Home PPPoE 1492 B vs Cellular Hotspot 1420 B), TCP SYN MSS clamping tier
-- (1220 / 1332 / 1380 / 1432 / 1452 B), Dummynet Pipe classification
-- (Fast-Lane #10/#11 vs Bulk #12/#13 vs Overlay vs Local Firewall Guard),
-- and L4S / ECN codepoint decoding.
--
-- Display Filter Fields:
--   tether.l3_len         (uint16) : Exact L3 packet size in bytes (ip.len or ipv6.plen + 40)
--   tether.pppoe_safe     (bool)   : True iff l3_len <= 1492 (PPPoE WAN safe)
--   tether.hotspot_safe   (bool)   : True iff l3_len <= 1420 (Cellular GTP/CLAT46 safe)
--   tether.fragmented     (bool)   : True iff IPv4 fragment or IPv6 Fragment Header present
--   tether.syn_mss        (uint16) : TCP SYN advertised MSS (tcp.options.mss_val)
--   tether.mss_tier       (string) : Clamping profile tier for TCP SYN packets
--   tether.dummynet_pipe  (string) : Dummynet queue / firewall rule classification
--   tether.ecn            (string) : L4S / ECN codepoint ("L4S ECT(1)", "ECN ECT(0)", "CE", "Not-ECT")

local tether_proto = Proto("tether", "Tether-Optimize Network & QoS Audit")

-- Protocol Fields
local pf_l3_len        = ProtoField.uint16("tether.l3_len",        "Layer-3 Packet Length (B)", base.DEC)
local pf_pppoe_safe    = ProtoField.bool("tether.pppoe_safe",      "PPPoE 1492 WAN Safe (<=1492B)")
local pf_hotspot_safe  = ProtoField.bool("tether.hotspot_safe",    "Hotspot 1420 MTU Safe (<=1420B)")
local pf_fragmented    = ProtoField.bool("tether.fragmented",      "IP Fragmented Packet")
local pf_syn_mss       = ProtoField.uint16("tether.syn_mss",       "TCP SYN Advertised MSS (B)", base.DEC)
local pf_mss_tier      = ProtoField.string("tether.mss_tier",      "TCP MSS Clamping Tier")
local pf_fast_lane     = ProtoField.bool("tether.fast_lane",       "Dummynet Fast-Lane (#10/#11)")
local pf_dummynet_pipe = ProtoField.string("tether.dummynet_pipe", "Dummynet Pipe / Firewall Class")
local pf_ecn           = ProtoField.string("tether.ecn",           "L4S / ECN Codepoint")
local pf_syn_ecn       = ProtoField.string("tether.syn_ecn",       "TCP Handshake ECN Negotiation")
local pf_icmp_owd      = ProtoField.string("tether.icmp_owd",      "RFC 792 ICMP Timestamp OWD")

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
    pf_icmp_owd
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

tether_proto.experts = {
    ef_oversized_pppoe,
    ef_unclamped_mss,
    ef_ip_fragment,
    ef_rogue_dhcp
}

-- Field Extractors
local f_ip_len       = Field.new("ip.len")
local f_ipv6_plen    = Field.new("ipv6.plen")
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
local f_icmp         = Field.new("icmp")
local f_icmp_type    = Field.new("icmp.type")
local f_icmpv6       = Field.new("icmpv6")
local f_dhcp         = Field.new("dhcp")

local FAST_LANE_PORTS = {
    [22]    = true, -- SSH
    [53]    = true, -- DNS
    [123]   = true, -- NTP
    [853]   = true, -- DNS-over-TLS (DoT)
    [3478]  = true, -- STUN
    [41641] = true, -- Tailscale WireGuard
    [41642] = true  -- Tailscale Userspace WireGuard
}

local LOCAL_GUARD_PORTS = {
    [3000]  = true, -- Next.js dev server
    [11434] = true  -- Ollama API
}

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

function tether_proto.dissector(buffer, pinfo, tree)
    local ip_len_fi    = f_ip_len()
    local ipv6_plen_fi = f_ipv6_plen()
    if not ip_len_fi and not ipv6_plen_fi then
        return
    end

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

    -- Dummynet pipe & firewall classification
    local tcp_sport = to_num(f_tcp_srcport())
    local tcp_dport = to_num(f_tcp_dstport())
    local udp_sport = to_num(f_udp_srcport())
    local udp_dport = to_num(f_udp_dstport())

    local pipe_str = "Bulk Pipe (#12/#13)"
    local is_fast_lane = false
    if tcp_sport and (LOCAL_GUARD_PORTS[tcp_sport] or LOCAL_GUARD_PORTS[tcp_dport]) then
        pipe_str = "Local-Service Firewall Guard (:3000/:11434)"
    elseif f_icmp() or f_icmpv6() then
        pipe_str = "Fast-Lane (#10/#11: ICMP/Control)"
        is_fast_lane = true
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
    if f_dhcp() then
        subtree:add_proto_expert_info(ef_rogue_dhcp)
    end

    -- TCP SYN MSS & ECN Handshake Negotiation audit
    -- (macOS BPF taps outbound post-PF scrub, inbound pre-PF scrub)
    if to_bool(f_tcp_syn()) then
        local is_ack  = to_bool(f_tcp_ack())
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
