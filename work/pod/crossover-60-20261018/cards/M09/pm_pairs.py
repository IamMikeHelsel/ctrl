"""Exact diagnostic coordinate transport; no source bundle claim."""

import json
from fractions import Fraction as F
from pathlib import Path


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def tr(a):
    return [list(x) for x in zip(*a, strict=True)]


def inv(a):
    d = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    return [[a[1][1] / d, -a[0][1] / d], [-a[1][0] / d, a[0][0] / d]]


def trace(a):
    return a[0][0] + a[1][1]


def sub(a, b):
    return [[a[i][j] - b[i][j] for j in range(2)] for i in range(2)]


I = [[F(1), F(0)], [F(0), F(1)]]
K = [[F(1), F(0)], [F(0), F(-1)]]
W = [[F(0), F(1)], [F(-1), F(0)]]
rows = []
for z in map(F, [0, "1/4", "-1/4", "1/3", "1/2", 2, -2]):
    a, b = (1 + z * z) / (1 - z * z), 2 * z / (1 - z * z)
    s = [[a, b], [-b, a]]
    t = 2 * a * b
    h = [[F(1), t], [t, F(-1)]]
    assert mm(mm(tr(s), K), s) == h
    rows.append((t, h, s))
checked = 0
false_fixed_k = 0
for t, h, s in rows:
    for _u, g, r in rows:
        c = mm(inv(s), r)
        ci = inv(c)
        k2 = mm(mm(tr(c), K), c)
        h2 = mm(mm(tr(c), h), c)
        w2 = mm(mm(ci, W), c)
        assert h2 == g
        signed = trace(mm(W, sub(mm(inv(K), h), I)))
        transported = trace(mm(w2, sub(mm(inv(k2), h2), I)))
        assert signed == transported == -2 * t
        # Replacing the transported independent K by its old components changes the tuple.
        false_fixed_k += int(k2 != K)
        checked += 1
result = {
    "pairs": checked,
    "non_K_unitary_coordinate_maps": false_fixed_k,
    "all_congruences_and_decorated_trace_preserved": True,
    "parameters": [str(t) for t, _, _ in rows],
    "scope": "Exact2D diagnostic; not physical modulus or128D source implementation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
