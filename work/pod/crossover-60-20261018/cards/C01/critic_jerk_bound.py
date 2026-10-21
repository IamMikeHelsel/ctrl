"""Exact rational necessary peak-jerk bound from rest and position tracking."""

import json
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)
PHASES = json.loads(SOURCE.read_text())


def position(time):
    for phase in PHASES:
        start, end = [F(phase[k]) for k in ["start", "end"]]
        if start <= time <= end:
            tau = time - start
            value = F(0)
            for c in reversed(phase["position_coefficients_local_time"]):
                value = value * tau + F(c)
            return value
    raise ValueError(time)


def bound(time, tolerance):
    return 6 * (position(time) - tolerance) / time**3


pm = json.loads((BASE / "pm_jerk_lower_bound.json").read_text())
t = F(pm["q_time"])
if position(t) != F(pm["q_position"]) or bound(t, F(pm["tracking_tolerance"])) != F(
    pm["peak_abs_jerk_necessary_lower_bound"]
):
    raise ValueError("PM bound did not reproduce")
candidates = [F(n, 10000) for n in range(2550, 4001)]
best = max(candidates, key=lambda s: bound(s, F(1, 5000)))
# A single time gives a valid necessary bound; search need not certify optimality.
value = bound(best, F(1, 5000))
if value <= F(pm["peak_abs_jerk_necessary_lower_bound"]):
    raise ValueError("search did not strengthen bound")
# Corruption controls: changed tolerance and nonzero initial acceleration must change formula.
if bound(best, F(1, 4000)) == value:
    raise ValueError("tolerance corruption undetected")
corrected_nonzero_accel = 6 * (position(best) - F(1, 5000) - F(1, 10) * best**2 / 2) / best**3
if corrected_nonzero_accel == value:
    raise ValueError("initial-state correction undetected")
out = dict(
    pm_reproduced=True,
    stronger_time=str(best),
    q=str(position(best)),
    bound=str(value),
    decimal=float(value),
    proof="x(t)= integral_0^t (t-s)^2 actual_jerk(s)/2 ds <= J t^3/6 from zero x,v,a; tracking gives x(t)>=q(t)-epsilon.",
    scope="Necessary bound from one rational time; no global optimum, attainability, or sufficiency claim. Python rational arithmetic plus hand integral argument, not Lean.",
    negative_controls=[
        "changed tracking tolerance",
        "nonzero initial acceleration requires extra term",
    ],
)
(BASE / "critic_jerk_bound_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
