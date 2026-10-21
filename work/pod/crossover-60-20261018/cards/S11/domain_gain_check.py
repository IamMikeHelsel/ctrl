"""Exact rational checks for fixed-r8 convolution-gain bounds; no ODE formalization."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def exp_positive_interval(x, n=60):
    partial = sum((x**k / F(factorial(k)) for k in range(n + 1)), F(0))
    assert 0 <= x < n + 2
    remainder = x ** (n + 1) / factorial(n + 1) / (1 - x / F(n + 2))
    return partial, partial + remainder


def negative_exp_interval(lo, hi):
    return 1 / exp_positive_interval(hi)[1], 1 / exp_positive_interval(lo)[0]


sl, su = F(1414213562373, 10**12), F(1414213562374, 10**12)
assert sl * sl < 2 < su * su
al, au = (2 - su) / 4, (2 - sl) / 4
bl, bu = (2 + sl) / 4, (2 + su) / 4
ela, eua = negative_exp_interval(4 * al, 4 * au)
elb, eub = negative_exp_interval(4 * bl, 4 * bu)
# a(1-2a) increasing on this a interval; b(2b-1) increasing on b interval.
assert 0 < al < au < F(1, 4) and F(1, 2) < bl < bu
Alo = 16 * (al * (1 - 2 * al) * ela + bl * (2 * bl - 1) * elb)
Ahi = 16 * (au * (1 - 2 * au) * eua + bu * (2 * bu - 1) * eub)
assert Ahi < F(1241, 1000)
assert sum((F(2) ** k / factorial(k) for k in range(8)), F()) == F(155, 21) > F(2000, 271)
assert sum((F(4) ** k / factorial(k) for k in range(10)), F()) == F(153527, 2835) > 54
C = F(76, 9)
M = F(103, 1000)
W = M / (1 - C / 1000)
V = F(271, 1000) * W
U = (8 * F(1, 8) + 6 * F(271, 1000) + F(1, 2) * F(1241, 1000)) * W
assert W == F(927, 8924) and V == F(251217, 8924000) < F(29, 1000)
assert U + F(93, 1000) < 2
result = {
    "scope": "Fixed r8 zero-state gains, or asymptotic gains after a separate boundedness/fading-memory argument. Not arbitrary r or an entry deadline.",
    "X_gain": "1/8",
    "V_gain_exact": "2 exp(-2)",
    "V_gain_upper": "271/1000",
    "A_gain_exact": "16*(h_prime((2-sqrt2)/4)-h_prime((2+sqrt2)/4))",
    "A_gain_lower": str(Alo),
    "A_gain_upper": str(Ahi),
    "A_gain_coarse_upper": "1241/1000",
    "command_derivative_gain_exact": "8+24 exp(-4)",
    "command_derivative_gain_upper": str(C),
    "M": str(M),
    "age": "1/1000",
    "residual_gain_bound": str(W),
    "speed_bound": str(V),
    "position_bound": str(W / 8),
    "command_plus_sensor_bound": str(U + F(93, 1000)),
    "decimal_display_only": {
        "A_lower": float(Alo),
        "A_upper": float(Ahi),
        "W": float(W),
        "V": float(V),
        "command_plus_sensor": float(U + F(93, 1000)),
    },
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result["decimal_display_only"]))
