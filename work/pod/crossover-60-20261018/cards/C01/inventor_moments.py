"""Exact transfer-polynomial and reference-regularity checks."""

import json
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def derivative(p):
    return [i * p[i] for i in range(1, len(p))] or [F(0)]


def evaluate(p, t):
    return sum(v * t**i for i, v in enumerate(p))


def series(num, den, n=4):
    out = []
    for i in range(n):
        v = num[i] if i < len(num) else F(0)
        v -= sum(den[j] * out[i - j] for j in range(1, min(i + 1, len(den))))
        out.append(v / den[0])
    return out


direct = [F(64000), F(4800), F(120), F(1)]
filtered = [F(1280000), F(96000), F(2400), F(100), F(1)]
difference = [filtered[i] - (20 * direct[i] if i < len(direct) else 0) for i in range(5)]
assert difference == [0, 0, 0, 80, 1]
rows = {
    "direct": series([F(-1, 6)], direct),
    "original": series([F(-250, 3), F(-1)], filtered),
    "compensated": series([F(-10, 3), F(-1)], filtered),
    "snap_compensated": series([F(-10, 3)], filtered),
}
assert rows["snap_compensated"][:3] == rows["direct"][:3]
assert rows["compensated"][0] == rows["direct"][0]
phases = json.loads(SOURCE.read_text())
checks = []
for before, after in zip(phases, phases[1:], strict=False):
    dt = F(before["end"]) - F(before["start"])
    p = list(map(F, before["position_coefficients_local_time"]))
    q = list(map(F, after["position_coefficients_local_time"]))
    jets = []
    for order in range(5):
        left, right = evaluate(p, dt), q[0]
        jets.append(
            {"order": order, "left": str(left), "right": str(right), "continuous": left == right}
        )
        p, q = derivative(p), derivative(q)
    assert all(j["continuous"] for j in jets[:4])
    checks.append({"join": after["start"], "jet": jets})
result = {
    "low_frequency_error_over_jerk_series": {k: list(map(str, v)) for k, v in rows.items()},
    "denominator_identity": "Df = 20 Ddirect + s^3(s+80)",
    "reference_join_checks": checks,
    "initial_jerk": "10",
    "zero_filter_initial_condition": True,
    "scope": "Transfer moments assume conventional zero-state input derivatives; actual run uses bounded piecewise snap without an impulse at initial jerk step, so startup remains and is retained in screen.",
}
Path(__file__).with_name("inventor_moments.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result["low_frequency_error_over_jerk_series"], indent=2))
