"""Exact polynomial integration of a necessary endpoint-moment dual."""

import json
from fractions import Fraction as F
from pathlib import Path


def integral(poly, left, right):
    return sum(c * (right ** (i + 1) - left ** (i + 1)) / (i + 1) for i, c in enumerate(poly))


def bound(T):
    J, S, a, v = F(10), F(400), F(51, 20), F(2601, 8000)
    alpha = (T + a / J + 3 * J / (2 * S)) / 2
    h, k = 2 * J / S, J / S
    assert h <= alpha <= T - k
    # Piecewise extremizer of p*j under pointwise necessary envelopes.
    # Its jump at alpha means it is NOT an admissible bounded-snap trajectory.
    pieces = [
        (F(0), h, J, -S),
        (h, alpha, -J, F(0)),
        (alpha, T - k, J, F(0)),
        (T - k, T, S * T, -S),
    ]
    dual = sum(integral([-alpha * b, b - alpha * c, c], l, r) for l, r, b, c in pieces)
    B = dual - alpha * a
    formula = (
        -alpha * a
        + J * (alpha**2 - T * alpha + T**2 / 2)
        - (3 * alpha + T) * J**2 / (2 * S)
        + 3 * J**3 / (2 * S**2)
    )
    assert B == formula == F(5, 2) * T**2 - F(127, 80) * T - F(13089, 64000)
    return {
        "T": str(T),
        "alpha": str(alpha),
        "upper_first_jerk_moment": str(B),
        "required_first_jerk_moment": str(v),
        "rejection_margin": str(v - B),
        "reject": B < v,
    }


arrival = [F(5, 192), F(5, 16), F(5, 2), F(10)]
ell = F(1, 200)
q, v, a, j = arrival
execution = [
    q + v * ell + a * ell**2 / 2 + j * ell**3 / 6,
    v + a * ell + j * ell**2 / 2,
    a + j * ell,
    j,
]
assert execution == [F(44217, 1600000), F(2601, 8000), F(51, 20), F(10)]
rows = [bound(F(4, 5)), bound(F(7, 8)), bound(F(249, 200))]
assert rows[1]["rejection_margin"] == "297/64000"
# Sharpened first a=j=0 time; integrates actual three-phase source blend.
T = F(127, 400)
state = execution[:]
for duration, snap in [(F(1, 20), F(-400)), (F(97, 400), F(0)), (F(1, 40), F(400))]:
    q, v, a, j = state
    d = duration
    state = [
        q + v * d + a * d * d / 2 + j * d**3 / 6 + snap * d**4 / 24,
        v + a * d + j * d * d / 2 + snap * d**3 / 6,
        a + j * d + snap * d * d / 2,
        j + snap * d,
    ]
assert state == [F(8782613, 38400000), F(75089, 96000), F(0), F(0)]
result = {
    "execution_state": list(map(str, execution)),
    "dual_tests": rows,
    "earliest_a_j_zero_execution_time": str(T),
    "source_blend_end_state": list(map(str, state)),
    "scope": "Necessary dual gate; no sufficient admission or full ODE kernel proof.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
