"""Exact queued smooth-lead versus zero-order-hold bound and source binding."""

import csv
import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08"
)
cfg = json.loads((SRC / "protocol.json").read_text())
assert F(str(cfg["h_s"])) == F(1, 5) and cfg["command_period_ns"] == 1000000
packets = cfg["cases"]["queued_reversal"]
events = []
last = F(0)
for p in packets:
    assert p["issue_ns"] <= p["arrival_ns"] <= p["execute_ns"]
    goal = F(str(p["target_rad"]))
    events.append((F(p["execute_ns"], 10**9), goal - last))
    last = goal
assert events == [(F(11, 50), F(1, 25)), (F(67, 100), F(-3, 50))]


def kernel(t, order):
    h = F(1, 5)
    if t <= 0:
        return F(0)
    if t >= 4 * h:
        return F(1) if order == 0 else F(0)
    return sum((-1) ** k * comb(4, k) * max(t - k * h, 0) ** (4 - order) for k in range(5)) / (
        factorial(4 - order) * h**4
    )


def q(t, order):
    return sum(delta * kernel(t - time, order) for time, delta in events)


def lead(t):
    return q(t, 0) + F(1, 10) * q(t, 1)


# Kernel analytic certificates are hand-derived in critic_hold.md; these exact
# identities check their coefficients, not just sampled reference trajectories.
for x in [F(k, 17) for k in range(18, 34)]:
    density = (-3 * x**3 + 12 * x * x - 12 * x + 4) / 6
    derivative = (-3 * x * x + 8 * x - 4) / 2
    assert F(2, 3) - derivative == F(3, 2) * (x - F(4, 3)) ** 2
    assert F(2, 3) - density == x * (2 - x) ** 2 / 2
V = F(1, 5)
A = F(5, 3)
gain = F(1, 10)
dt = F(1, 1000)
bound = (V + gain * A) * dt
assert bound == F(11, 30000)
rows = list(
    csv.DictReader((SRC / "results/queued_reversal__model_bias_compensation__500us.csv").open())
)
errors = {key: F(0) for key in ["ref_offset_rad", "ref_velocity_rad_s", "ref_acceleration_rad_s2"]}
for row in rows:
    t = F(row["time_s"])
    for order, key in enumerate(errors):
        errors[key] = max(errors[key], abs(F(row[key]) - q(t, order)))
    # Every not-yet-arrived packet has zero position and velocity contribution.
    for packet, (execution, _delta) in zip(packets, events, strict=True):
        if t < F(packet["arrival_ns"], 10**9):
            assert kernel(t - execution, 0) == kernel(t - execution, 1) == 0
jumps = [(abs(lead(F(n + 1, 1000)) - lead(F(n, 1000))), n) for n in range(2000)]
peak, n = max(jumps)
assert V * dt < peak <= bound
interior = F(n + 1, 1000) - F(1, 10**6)
interior_error = abs(lead(interior) - lead(F(n, 1000)))
assert V * dt < interior_error <= bound
result = {
    "V_rad_s": str(V),
    "A_rad_s2": str(A),
    "lead_gain_s": str(gain),
    "hold_period_s": str(dt),
    "led_hold_error_bound_rad": str(bound),
    "saved_reference_exact_errors": {k: str(v) for k, v in errors.items()},
    "drop_acceleration_term_negative": {
        "start_s": str(F(n, 1000)),
        "led_command_jump_rad": str(peak),
        "incorrect_old_bound_rad": str(V * dt),
        "strictly_interior_time_s": str(interior),
        "strictly_interior_error_rad": str(interior_error),
    },
    "scope": "Exact analytic led reference and its ideal1kHz zero-order hold. No physical state/output tube, continuous implementation rounding bound, or arbitrary revised history guarantee.",
}
(HERE / "critic_hold.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
