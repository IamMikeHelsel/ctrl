"""Independent exact replay of duplicate-event and delayed-execution witnesses."""

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

P = Path(__file__).parent
src = json.loads((P / "inventor_protocol.json").read_text())
h = F(1, 5)


def primitive(z):
    return sum(F((-1) ** i * comb(4, i)) * max(z - i, 0) ** 4 for i in range(5)) / 24


def third(z):
    return sum(F((-1) ** i * comb(4, i)) * max(z - i, 0) for i in range(5))


def reference(events, t):
    return sum(delta * primitive((t - tau) / h) for tau, delta in events)


def jerk(events, t):
    return sum(delta / F(1000) * third((t - tau) / h) / h**3 for tau, delta in events)


events = [tuple(map(F, e)) for e in src["duplicate_displacement_failure"]["events"]]
knots = sorted({tau + i * h for tau, delta in events for i in range(5)})
values = [[t, jerk(events, t)] for t in knots]
reported = [
    [F(t), F(v)] for t, v in src["duplicate_displacement_failure"]["piecewise_linear_jerk_knots"]
]
assert values == reported
peak = max(abs(v) for t, v in values)
assert peak == F(77, 160) < F(15, 2)
assert reference(events, F(3, 2)) == 2
assert abs(reference(events, F(3, 2)) - 1) - F(1, 5) == F(4, 5)
late = [(F(13, 10), F(20))]
assert reference(late, F(3, 2)) == F(5, 6)
assert 20 - reference(late, F(3, 2)) - F(1, 5) == F(569, 30)
assert reference(late, F(51, 50)) == 0
# A single-event replay changes the claimed duplicate overshoot; wrong units change
# jerk by1000; using nominal execution incorrectly changes late-deadline reference.
assert reference(events[:1], F(3, 2)) != 2
assert peak * 1000 != F(src["duplicate_displacement_failure"]["exact_peak_reference_jerk_m_per_s3"])
assert reference([(F(11, 50), F(20))], F(3, 2)) != F(5, 6)
out = {
    "peak_jerk_m_per_s3": str(peak),
    "duplicate_reference_mm": "2",
    "late_reference_mm": "5/6",
    "late_tube_conditional_error_lower_mm": "569/30",
    "negative_controls": 3,
    "scope": "Exact primitive replay and conditional tracking-tube implications; no fresh physical trajectory or original guard executable replay.",
}
(P / "critic_reference_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
