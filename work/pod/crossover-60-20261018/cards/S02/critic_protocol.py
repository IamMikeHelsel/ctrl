"""Exact original-grid tie witness and protocol-assumption negative controls."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
H = F(1, 2000)


def state(t):
    return (F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t, F(39, 100) - F(6, 5) * t, -F(6, 5))


def guard(m):
    return m[0] <= F(143, 1000) and abs(m[1]) <= F(561, 50000) and -F(127, 100) <= m[2] <= -F(1, 5)


def measurement(k):
    m = list(state(k * H))
    if k == 633:
        m[1] += F(1, 100)
    return tuple(m)


assert all(not guard(measurement(k)) for k in range(632))
assert guard(measurement(632)) and not guard(measurement(633))
assert measurement(633)[1] - state(633 * H)[1] == F(1, 100)
arrivals = {632: 632 * H + H, 633: 633 * H}
assert arrivals[632] == arrivals[633]
assert max(arrivals.values()) - 632 * H == H
batch = [633, 632]
latest = max(batch)
assert not guard(measurement(latest))
first_complete = min(k for k in batch if guard(measurement(k)))
assert first_complete == 632
# If both qualify, committing before the tied batch is closed selects the wrong first.
assert guard(state(632 * H)) and guard(state(633 * H))
premature_choice = batch[0]
assert premature_choice != first_complete
# Original half-millisecond bounded delays cannot strictly reorder consecutive samples.
for d0, d1 in product((F(0), H / 2, H), repeat=2):
    assert 632 * H + d0 <= 633 * H + d1
assert 632 * H + (H + H / 2) > 633 * H  # Changed bound, explicitly outside source contract.
# Release at stamp+h requires closed, inclusive arrival processing at that deadline.
deadline = 632 * H + H
arrived_strictly_before_timer = [k for k, a in arrivals.items() if a < deadline]
assert 632 not in arrived_strictly_before_timer
arrived_by_deadline = [k for k, a in arrivals.items() if a <= deadline]
assert 632 in arrived_by_deadline
# A dropped qualifying message cannot be replaced by an upper bound on delivered delays.
dropped_batch = [633]
assert not any(guard(measurement(k)) for k in dropped_batch)
# Positive sensor timestamp skew can satisfy a nominal age check while true age fails.
actual_sample, stamped, now = F(0), F(1, 5000), F(11, 10000)
assert now - stamped <= F(1, 1000) < now - actual_sample
# Duplicate IDs with conflicting values must not silently replace the old reading.
duplicate_conflict = measurement(632) != measurement(633)
assert duplicate_conflict
payload = {
    "source_witness": "x=.001+.39t-.6t^2, v=.39-1.2t, a=-1.2; source C8 admitted C6 witness",
    "reading632": list(map(str, measurement(632))),
    "reading633": list(map(str, measurement(633))),
    "arrival": str(deadline),
    "latest_only_loses_first": True,
    "complete_batch_first": first_complete,
    "negative_controls": [
        "premature tie commit",
        "missing first message",
        "inclusive-deadline race",
        "clock skew",
        "conflicting duplicate payload",
    ],
    "strict_reorder_scope": "Impossible for original delays[0,h]; positive witness uses changed upper bound1.5h.",
    "scope": "Exact detector/protocol counterexamples, not a physical safety violation or whole switched execution proof.",
}
(HERE / "critic_protocol.json").write_text(json.dumps(payload, indent=2) + "\n")
print(json.dumps(payload, indent=2))
