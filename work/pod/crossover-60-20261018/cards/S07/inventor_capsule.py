"""Independent capsule shape checks and coupling-condition negative controls."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
g = [F(1), -F(1), F(1)]


def energy(z):
    return sum((z[i] * P[i][j] * z[j] for i in range(3) for j in range(3)), F(0))


def dot(a, b):
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def mul(z):
    return [dot(row, z) for row in P]


def solve(A, b):
    M = [row[:] + [x] for row, x in zip(A, b, strict=True)]
    for i in range(3):
        p = M[i][i]
        M[i] = [x / p for x in M[i]]
        for j in range(3):
            if j != i:
                q = M[j][i]
                M[j] = [x - q * y for x, y in zip(M[j], M[i], strict=True)]
    return [row[-1] for row in M]


# E12 point whose distance to the capsule's segment cannot reach E11.
z = [F(5, 4), F(0), F(0)]
quad = energy(g)
linear = dot(g, mul(z))
delta_unconstrained = linear / quad
assert delta_unconstrained == F(145, 189) > F(1, 8)
nearest = [x - F(1, 8) * y for x, y in zip(z, g, strict=True)]
assert energy(z) == F(95, 8) < 12
assert energy(nearest) == F(35869, 3200) > 11
# Capsule point outside E12; pure hidden direction suffices for noncontainment.
base = [F(17, 10) * x for x in g]
outside = [F(73, 40) * x for x in g]
assert energy(base) < 11 and energy(outside) == F(1007181, 80000) > 12
# Replacing E11 by E12 in the lift violates travel2 immediately.
invpos = solve(P, [F(1), F(0), F(0)])
assert mul(invpos) == [F(1), F(0), F(0)]
c = invpos[0]
assert c == F(3550075, 11131832)
travel_base = [F(19, 10) * x / c for x in invpos]
travel_shift = [x + y / 8 for x, y in zip(travel_base, g, strict=True)]
assert energy(travel_base) < 12 and energy(travel_base) > 11
assert travel_shift[0] == F(81, 40) > 2
# Mismatched lagrate violates the hidden-mode derivative identity at t0.
d = F(1, 8)
A2g = [-F(1), F(1), -F(2)]
lag_residual = [d * (x + y) for x, y in zip(A2g, g, strict=True)]
assert lag_residual == [F(0), F(0), -F(1, 8)]
# Matched state offset but different permitted held disturbances.
disturbance_residual = [F(0), F(0), F(1, 100)]
assert dot([-F(1), -F(3), -F(2)], disturbance_residual) == -F(1, 50)
# Different permitted sample clocks: at t.1 one resamples while other holds to.2.
request_at_tenth = -F(11, 10) + F(3, 2) * F(1, 10) + F(1, 2) * F(1, 10) ** 2
assert request_at_tenth == -F(189, 200)
new_input = request_at_tenth
old_input = -F(1)
assert new_input - old_input == F(11, 200)
# Source E11 and output arithmetic independently rechecked.
eta = F(5, 451)
assert 13 * (F(1, 5) + 1 / eta) * F(1, 100) ** 2 <= eta * 11
assert 11 * c <= F(15, 8) ** 2
assert F(15, 8) + F(1, 8) == 2
out = {
    "scope": "Exact geometry/coupling diagnostics. Lifted dynamics rely on matched signal construction and E11 invariant, not proved here.",
    "not_superset": {
        "old_E12_point": list(map(str, z)),
        "energy": str(energy(z)),
        "closest_segment_shift": "1/8",
        "minimum_base_energy": str(energy(nearest)),
    },
    "not_subset": {
        "base": list(map(str, base)),
        "base_energy": str(energy(base)),
        "capsule_point": list(map(str, outside)),
        "energy": str(energy(outside)),
    },
    "wrong_E12_base_loses_travel": {
        "base": list(map(str, travel_base)),
        "base_energy": str(energy(travel_base)),
        "shifted_position": str(travel_shift[0]),
    },
    "coupling_negatives": {
        "lagrate2_derivative_residual": list(map(str, lag_residual)),
        "unequal_disturbance_accel_derivative_residual": "1/100",
        "unequal_clock_input_residual_at_1_10": "11/200",
    },
    "E11_budget_and_travel_arithmetic": "passed",
}
(HERE / "inventor_capsule.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))

# A simple active point in the new part (not merely the zero-request hidden ray).
active_base = [F(27, 20), -F(5, 4), F(7, 4)]
active_lift = [x + y / 8 for x, y in zip(active_base, g, strict=True)]
active_request = -active_base[0] - 3 * active_base[1] - 2 * active_base[2]
assert active_request == -F(11, 10)
assert energy(active_base) < 11 and energy(active_lift) > 12
out["active_new_part"] = {
    "base": list(map(str, active_base)),
    "base_energy": str(energy(active_base)),
    "lift": list(map(str, active_lift)),
    "lift_energy": str(energy(active_lift)),
    "request": str(active_request),
}
(HERE / "inventor_capsule.json").write_text(json.dumps(out, indent=2) + "\n")
print("Active new part", out["active_new_part"])
