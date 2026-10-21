"""Exact S11 diagnostic arithmetic, not a trajectory/kernel proof."""

import hashlib
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/"
    "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
)
weights = [F(51, 50), F(101, 100), F(1)]
errors = [F(101533, 100000000), F(368033, 100000000), F(1042283, 100000000)]
target = F(9, 200)


def old(t):
    return [F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t, F(39, 100) - F(6, 5) * t, -F(6, 5)]


def policy(m):
    offsets = [m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16]
    radius = max(
        [target]
        + [
            (offsets[i] - offsets[j] + errors[i] + errors[j]) / (weights[i] + weights[j])
            for i in range(3)
            for j in range(3)
        ]
    )
    center = max(offsets[i] + errors[i] - weights[i] * radius for i in range(3))
    return center, radius


def physical(z):
    return [z[0], 4 * (z[1] - z[0]), 16 * (z[2] - 2 * z[1] + z[0])]


def box_extrema(radius):
    values = [
        physical([s * w * radius for s, w in zip(signs, weights, strict=True)])
        for signs in itertools.product([-1, 1], repeat=3)
    ]
    return [max(abs(row[i]) for row in values) for i in range(3)]


first_zero = F(13, 40)
assert old(first_zero) == [F(103, 1600), 0, -F(6, 5)]
assert old(F(33, 50))[0] == -F(37, 12500)
assert box_extrema(target) == [F(459, 10000), F(1827, 5000), F(1818, 625)]
sample = F(79, 250)
center, radius = policy(old(sample))
assert -8 * (old(sample)[0] - center) - 6 * old(sample)[1] - old(sample)[2] / 2 == F(
    2783033, 12500000
)
lo, hi = center - weights[0] * radius, center + weights[0] * radius
assert lo < 0 < hi < F(3, 20)
assert -F(3, 100) <= lo
# Exact zero-effective-target continuation, r=8, s=1:
# x = 103/1600 - (3/20)*(1-(1-exp(-8))/8)
#   = -107/1600 - (3/160)*exp(-8) < 0.
assert F(103, 1600) - F(3, 20) + F(3, 160) == -F(107, 1600)
# A fixed-r actuator-memory coordinate p=v+a/r obeys p'=b.
# Changing r from 8 to 12 while preserving physical state changes p by 1/20.
momentum8, momentum12 = -F(6, 5) / 8, -F(6, 5) / 12
assert momentum12 - momentum8 == F(1, 20)
# Exact fixed-center holding equilibria for both allowed target disturbances.
equilibria = []
for disturbance in [-F(1, 100), F(1, 100)]:
    displacement = disturbance / 8
    command = -8 * displacement
    assert command + disturbance == 0 and abs(command) <= 2
    equilibria.append([displacement, 0, 0, command, disturbance])

# A controller-independent local viability necessary condition under the source
# post-handoff clamp and target-error bounds. The barrier proof is in inventor.md.
accel_magnitude = F(6, 5)
max_effective_target = F(201, 100)
slope = 12 * (max_effective_target + accel_magnitude)
barrier_time = accel_magnitude / slope
retreat = accel_magnitude**3 / (3 * slope**2)
assert -accel_magnitude * barrier_time**2 / 2 + slope * barrier_time**3 / 6 == -retreat
assert retreat > F(3, 10000)
barrier_checks = []
for t in [0, barrier_time / 2, barrier_time]:
    upper_a = -accel_magnitude + slope * t
    for r in [8, 12]:
        for b in [-max_effective_target, max_effective_target]:
            derivative_gap = r * (b - upper_a) - slope
            assert derivative_gap <= 0
            barrier_checks.append([t, r, b, derivative_gap])

result = {
    "evidence": "Exact rational diagnostic arithmetic; no new Lean or full trajectory certificate",
    "source_hashes": {
        str(SOURCE / p): hashlib.sha256((SOURCE / p).read_bytes()).hexdigest()
        for p in [
            "HandoffWitness.lean",
            "inputs/ClearancePolicy.lean",
            "inputs/WeightedEntry.lean",
            "inputs/ClearanceEntry.lean",
        ]
    },
    "counterfactual_continued_braking": {
        "first_zero": first_zero,
        "state": old(first_zero),
        "later_t": F(33, 50),
        "later_x": old(F(33, 50))[0],
        "scope": "Old C8 prefix extended; actual C8 switches before first zero, so not its continuation",
    },
    "new_ideal_zero_effective_target_mode": {
        "r": 8,
        "relative_t": 1,
        "x_constant": -F(107, 1600),
        "x_exp_minus8_coefficient": -F(3, 160),
        "limiting_velocity": momentum8,
        "scope": "New ideal b=0 mode, not an assertion about unknown disturbance under command u=0",
    },
    "weighted_terminal_extrema": box_extrema(target),
    "actual_C8_sample_policy": {
        "sample": sample,
        "reading": old(sample),
        "center": center,
        "radius": radius,
        "certified_position_interval_from_box": [lo, hi],
        "lower_zero_admission": False,
        "lower_minus_0_03_admission": True,
        "scope": "Box implication only; negative lower endpoint does not establish actual negative travel",
    },
    "actuator_memory": {
        "p_r8": momentum8,
        "p_r12": momentum12,
        "coordinate_jump_if_rate_changes": momentum12 - momentum8,
    },
    "same_feedback_constant_disturbance_equilibria": equilibria,
    "fixed_center_accuracy_floor_for_both_equilibria": F(1, 800),
    "necessary_retreat_buffer": {
        "a0": -accel_magnitude,
        "max_effective_target": max_effective_target,
        "barrier_slope": slope,
        "elapsed_time": barrier_time,
        "minimum_retreat": retreat,
        "minimum_retreat_decimal_m": float(retreat),
        "sampled_algebra_negative_controls": barrier_checks,
        "scope": "Analytic affine-barrier implication for any admitted clipped post-controller;"
        " initial a0 is conditional, not the actual C8 first-zero acceleration",
    },
    "critic_improved_linear_barrier": {
        "elapsed_time": 2 * barrier_time,
        "minimum_retreat": 2 * retreat,
        "minimum_retreat_decimal_m": float(2 * retreat),
        "reason": "Integrated cubic upper bound minimized at 2A/K; earlier bound retained",
    },
    "root_exponential_barrier_candidate": {
        "elapsed_time": F(1, 12),
        "exp_minus_one_lower": F(367, 1000),
        "minimum_retreat": F(1923, 1600000),
        "scope": "Analytic comparison plus rational Taylor bound, not a full kernel trajectory theorem",
    },
}
partial = F(0)
factorial = 1
for k in range(8):
    if k:
        factorial *= k
    partial += F((-1) ** k, factorial)
assert partial > F(367, 1000)  # odd alternating partial lies below exp(-1)
assert F(201, 100) / 288 - F(321, 100) * F(367, 1000) / 144 == -F(1923, 1600000)
encoded = json.dumps(result, default=str, indent=2)
(HERE / "inventor_terminal.json").write_text(encoded + "\n")
print(encoded)
