"""Independent truncated-power derivatives, without producer imports."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
H = F(1, 5)
BINOM = [1, -4, 6, -4, 1]


def derivative(events, t, order):
    return sum(
        delta * c * max(t - tau - i * H, F(0)) ** (4 - order) / (factorial(4 - order) * H**4)
        for tau, delta in events
        for i, c in enumerate(BINOM)
    )


def extrema(events):
    knots = sorted({tau + i * H for tau, _ in events for i in range(5)})
    acc_candidates = [(t, derivative(events, t, 2)) for t in knots]
    for left, right in zip(knots, knots[1:], strict=False):
        jl = derivative(events, left, 3)
        jr = derivative(events, right, 3)
        if jl != jr:
            root = left - jl * (right - left) / (jr - jl)
            if left < root < right:
                acc_candidates.append((root, derivative(events, root, 2)))
    jerk = max(((t, derivative(events, t, 3)) for t in knots), key=lambda p: abs(p[1]))
    acc = max(acc_candidates, key=lambda p: abs(p[1]))
    return {"acceleration": list(map(str, acc)), "jerk": list(map(str, jerk))}


old = [(F(11, 50), F(1, 50))]
ordinary = old + [(F(13, 25), -F(1, 50))]
far = old + [(F(13, 25), -F(1, 25))]
results = {
    name: extrema(events)
    for name, events in [("old", old), ("ordinary", ordinary), ("far_candidate", far)]
}
assert abs(F(results["ordinary"]["acceleration"][1])) == F(21, 32)
assert abs(F(results["far_candidate"]["jerk"][1])) == F(45, 4)
assert abs(F(results["ordinary"]["jerk"][1])) == F(25, 4)
assert derivative(old, F(19, 10), 0) - (-F(1, 50)) == F(1, 25)
# Exact pre-execution matching, including derivatives at execution.
for n in range(53):
    t = F(n, 100)
    for k in range(4):
        assert derivative(old, t, k) == derivative(ordinary, t, k)
# Removing old history is a reference-state reset, even if the new pulse is smooth.
t = F(13, 25)
old_state = [derivative(old, t, k) for k in range(4)]
assert old_state[1] != 0 and old_state[2] != 0
results["execution_old_qvaj"] = list(map(str, old_state))
results["rejected_far_reference_goal_error"] = "1/25"
results["deadline_before_delivery"] = F(51, 100) < F(13, 25)
# A knot-only velocity checker is not sound on a cubic velocity segment.
# v=t(1-t), a=1-2t, j=-2: knot velocity zero, interior peak1/4.
assert F(1, 2) * (1 - F(1, 2)) == F(1, 4)
results["velocity_knots_negative_control"] = {
    "v_endpoints": ["0", "0"],
    "v_half": "1/4",
    "limit": "1/5",
    "knots_pass_interior_fails": True,
}
(HERE / "critic_exact.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
