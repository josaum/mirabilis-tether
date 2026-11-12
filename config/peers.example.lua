-- Site-local peer labels for the Tether-Optimize Wireshark dissector.
--
-- Copy to tether_peers.lua next to tether_optimize.lua (the installer places it
-- under ~/.local/lib/wireshark/plugins/) to teach the dissector which addresses
-- and hardware addresses belong to hosts you care about. Without this file the
-- dissector still works — it simply has no named peers to flag.
--
-- Everything here is optional; omit any table you do not need.

return {
    -- Direct peers: traffic to/from these addresses is reported at HIGH severity.
    direct = {
        ["192.0.2.50"] = "Laptop [192.0.2.50]",
        ["2001:db8::50"] = "Laptop [IPv6]",
    },

    -- Infrastructure peers (routers, bridges, hypervisors): reported at LOW severity.
    bridge = {
        ["192.0.2.1"] = "Gateway [192.0.2.1]",
    },

    -- Hardware addresses that route for a bridge peer.
    bridge_macs = {
        ["02:00:5e:10:00:01"] = "Gateway bridge",
    },

    -- The bridge port address used for L2 SNAT detection.
    bridge_snat_ips = {
        ["192.0.2.1"] = true,
    },

    -- Address of the primary bridge NIC, used to spot SNAT MAC rewrites.
    bridge_primary_mac = "02:00:5e:10:00:01",

    -- Multicast DNS repeaters / sleep proxies: reflections are LOW, not HIGH.
    mdns_proxies = {
        ["02:00:5e:10:00:02"] = "VLAN mDNS repeater",
    },

    -- Extra hardware addresses that stand in for a direct peer (DHCP rotation).
    watchlist_macs = {
        ["02:00:5e:10:00:03"] = "Laptop advertiser",
    },
}
