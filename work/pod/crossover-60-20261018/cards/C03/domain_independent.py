"""Independent critic diagnostic integration, without importing producer modules."""

import json
from fractions import Fraction as F
from pathlib import Path


def mul(a, b):
    p = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i + j] += x * y
    return p


def evaluate(pieces, kernel):
    total = F(0)
    for lo, hi, poly in pieces:
        product = mul(poly, kernel)
        total += sum(c * (hi ** (i + 1) - lo ** (i + 1)) / (i + 1) for i, c in enumerate(product))
    return total


L = [(F(0), F(1, 2), [F(1), F(-4)]), (F(1, 2), F(3, 4), [F(-1)]), (F(3, 4), F(1), [F(-4), F(4)])]
U = [(F(0), F(3, 4), [F(1)]), (F(3, 4), F(1), [F(4), F(-4)])]
kernels = [[F(1)], [F(1), F(-1)], [F(1, 2), F(-1), F(1, 2)]]
bounds = [(evaluate(L, k), evaluate(U, k)) for k in kernels]
assert bounds == [(F(-3, 8), F(7, 8)), (F(-7, 96), F(47, 96)), (F(17, 1536), F(85, 512))]
# Sign switches at1/2: choose lower before, upper after.
selected = [L[0], (F(1, 2), F(3, 4), [F(1)]), U[1]]
support = evaluate(selected, [F(-1), F(2)])
assert support == F(1, 16)
result = {
    "critic_bounds": [[str(x) for x in row] for row in bounds],
    "support": str(support),
    "rejected_a_minus_2v": "1/2",
    "producer_imported": False,
    "root_rest_to_rest_moment_check": {
        "t1_plus_t3": "T",
        "t1_times_t3": "T^2/8",
        "sum_fourth_powers_t1_t3": "17*T^4/32",
        "snap_third_moment": "-S*T^4/64",
        "position": "S*T^4/384",
        "jerk_peak": "S*T*(sqrt(2)-1)/2",
        "scope": "Symbolic hand identities independently derived; no algebraic-number code.",
    },
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print("Independent critic interval and joint support values matched.")
