# Measuring the benefit — A/B bufferbloat benchmark

`tether-optimize benchmark` is the field test that turns the verified policy into a
measured outcome. It saturates your tethered link once with shaping off and once
with shaping on, samples latency under load both times, and reports the before/after.

## What it measures

| Metric | Meaning |
|---|---|
| Gateway RTT p50 / p95 / max | Round-trip time to the phone/gateway while the link is saturated — the bufferbloat number |
| HTTP TTFB p50 / p95 / max | Time-to-first-byte from Cloudflare's edge under load — what a web request / call setup feels like |

Saturation uses Cloudflare's speed-test endpoint with a bounded byte count, so the
load is controlled and reproducible rather than a random big download.

## Run it (needs your phone and a non-metered link)

1. Tether the phone to this Mac — **USB is best** (avoids Wi-Fi contention), or
   Personal Hotspot over Wi-Fi.
2. Set the cap you intend to ship against (optional, default 25/8):

   ```bash
   sudo tether-optimize cap 15 5      # e.g. a 15 Mbps down / 5 Mbps up plan
   ```

3. Run the A/B (default 20 s per phase; 30 s is more stable):

   ```bash
   sudo tether-optimize benchmark --seconds 30
   ```

The run saturates the link on purpose and pulls roughly
`down_mbps × seconds / 8` MB per phase. On a metered SIM, stop and lower `--seconds`
first.

## Read the result

```
=== A/B result (gateway RTT ms: p50 / p95 / max · HTTP TTFB ms: p50 / p95 / max) ===
                stock        shaped
RTT p50           24.1          22.8
RTT p95          612.0          47.3      <- the number that matters
RTT max         1150.0         108.1
TTFB p50          89.0          41.0
TTFB p95         740.0          62.0
```

The headline claim is the **RTT p95 (or max) drop under load** — stock macOS lets
TCP buffers balloon and the saturated queue builds multi-hundred-ms latency; the
shaper bounds it. Results also land in `~/.local/state/tether-optimize/benchmark.json`.

## Turning this into a publishable number

- Run **three times** and cite the median p95, not the best run.
- Run over **USB** and again over **Wi-Fi Personal Hotspot** — report both; USB is
  the cleanest single variable.
- Pair it with one **manual check the script cannot do**: start a video call or a
  large transfer, watch it for the same 30 s window in each phase. The RTT table is
  the measurement; "the call stopped stuttering" is the human confirmation.

## What it cannot measure

- End-to-end call quality (that needs a real call, as above).
- Upload-side bufferbloat (saturation is download-only; the controller shapes both,
  but this harness only drives down).
- Multiple devices or non-macOS links — the tool is single-machine by design.

## Why this beats "just use a travel router" (for the README)

A CAKE/SQM travel router fixes the queue *after* the Mac has already ballooned its
own TCP socket buffers to 16 MB and handed a burst to the OS. The fix has to live on
the Mac — that is where the bufferbloat is created — and `tether-optimize` is that
fix with no extra hardware to carry, charge, or get approved by IT.
