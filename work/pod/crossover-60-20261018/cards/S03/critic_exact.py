"""Independent exact boundary and semantics tests, no producer imports."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def energy(x, v):
    return 4 * x * x + (x + v) ** 2


def step(x, v, u, h, w=F(0)):
    return x + h * v + h * h * (u + w) / 2, v + h * (u + w)


def nearest(x):
    low = x.numerator // x.denominator
    r = x - low
    return low if r < F(1, 2) else low + 1 if r > F(1, 2) else low + (low % 2)


x, v = F(-1, 20), F(7, 20)
assert energy(x, v) == F(1, 10)
X, V = -500, 3500
corners = [energy(F(2 * X + a, 20000), F(2 * V + b, 20000)) for a in (-1, 1) for b in (-1, 1)]
assert max(corners) > F(1, 10)
x_bad, v_bad = x + F(1, 25000), v + F(1, 25000)
assert nearest(10000 * x_bad) == X and nearest(10000 * v_bad) == V
assert energy(x_bad, v_bad) > F(1, 10)
fallback = step(x, v, F(0), F(1, 2))
assert energy(*fallback) == F(461, 1600) > F(1, 10)
# truncation is not a half-grid quantizer: simultaneous just-below-grid coordinates.
x_trunc, v_trunc = F(9, 100000), F(9, 100000)
trunc_error = abs(-2 * x_trunc - 3 * v_trunc)
assert trunc_error == F(9, 20000) > F(1, 4000)
# Different nearest tie rules satisfy the same bound but are not the identical function.
ties = []
for n in range(-4, 5):
    y = F(2 * n + 1, 2)
    even = nearest(y)
    up = n + 1
    assert abs(even - y) == abs(up - y) == F(1, 2)
    ties.append([str(y), even, up])
# Separate exact Q16 intermediate wrapping diagnostic; never C signed-UB claim.
S = 65536
qx, qv = nearest(S * x), nearest(S * v)
raw = -2 * qx - 3 * qv


def wrap(z):
    return (z + 32768) % 65536 - 32768


wrong = -2 * qx - wrap(3 * qv)
assert (qx, qv, raw, wrong) == (-3277, 22938, -62260, 3276)
assert abs(F(wrong, S) - (-2 * x - 3 * v)) > F(1, 4000)
# Delayed true-state binding can consume the full ADC budget even with perfect old sample.
# At retained x=0,v=.1, a=0 and age .002, state differs by .0002 in x.
u_stale = F(-3, 10)
x_now = F(1, 5000)
v_now = F(1, 10)
assert energy(x_now, v_now) < F(1, 10)
stale_error = abs(u_stale - (-2 * x_now - 3 * v_now))
assert stale_error == F(1, 2500) > F(1, 4000)
results = {
    "boundary_cell": {
        "codes": [X, V],
        "safe_center_energy": energy(x, v),
        "corner_energies": corners,
        "same_code_unsafe_true_state": [x_bad, v_bad],
        "unsafe_energy": energy(x_bad, v_bad),
    },
    "rejection_zero_fallback": {
        "state": fallback,
        "energy": energy(*fallback),
        "scope": "No such fallback exists in source theorem; diagnostic changed policy.",
    },
    "truncation_error": trunc_error,
    "nearest_ties": ties,
    "Q16": {"inputs": [qx, qv], "correct": raw, "explicit_wrap16_intermediate": wrong},
    "stale_perfect_sample_error": stale_error,
}
(P / "critic_exact.json").write_text(json.dumps(results, default=str, indent=2) + "\n")
print(json.dumps(results, default=str))
