"""Exact witnesses distinguishing latency dispersion from absolute age."""

import json
from fractions import Fraction as F
from pathlib import Path

h = F(1, 2000)
rows = []
for name, low, high in [
    ("original", F(0), h),
    ("reserved_network", F(0), F(9, 20000)),
    ("large_common_offset", F(1, 10), F(251, 2500)),
]:
    gap = h + low - high
    rows.append(
        {
            "fixture": name,
            "old_latency": str(high),
            "new_latency": str(low),
            "adjacent_arrival_gap": str(gap),
            "strict_order": gap > 0,
            "old_packet_end_hold_age": str(high + h),
            "original_1ms_age_bound": high + h <= F(1, 1000),
        }
    )
assert rows[0]["adjacent_arrival_gap"] == "0"
assert rows[1]["adjacent_arrival_gap"] == "1/20000"
assert rows[2]["strict_order"] and not rows[2]["original_1ms_age_bound"]
reserve = F(1, 20000)
old_network, old_processing = h - reserve, reserve
new_network, new_processing = F(0), F(0)
assert 632 * h + old_network < 633 * h + new_network
assert 632 * h + old_network + old_processing == 633 * h + new_network + new_processing
result = {
    "reserved_processing_tie": {
        "reserve": str(reserve),
        "old_network": str(old_network),
        "old_processing": str(old_processing),
        "new_network": str(new_network),
        "new_processing": str(new_processing),
        "equal_ready_time": str(633 * h),
    },
    "derivation": "Forj>i: arrivalj-arrivali=(j-i)h+latencyj-latencyi >= (j-i)h-(upper-lower). Spread<h gives strict order; common offset cancels. Absolute latency still controls sample age. This analytic derivation is not newly kernel-proved here.",
    "fixtures": rows,
    "boundary": "Reserved network budget need not imply strictly ordered end-to-end readiness if variable processing expands the total latency range back to[0,h].",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
