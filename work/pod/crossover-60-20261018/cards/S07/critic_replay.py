"""Consume exact geometry and mode receipts independently of producers."""

import copy
import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

PTH = Path(__file__).resolve().parent
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]


def consume(cert):
    try:
        assert [[F(x) for x in r] for r in cert["P"]] == P
        inv = [[F(x) for x in r] for r in cert["P_inverse"]]
        assert all(
            sum(P[i][k] * inv[k][j] for k in range(3)) == int(i == j)
            for i in range(3)
            for j in range(3)
        )
        for cov, record in zip([[-1, -3, -2], [1, 0, 0]], cert["residual_LDL"], strict=True):
            sigma = sum(F(cov[i]) * inv[i][j] * cov[j] for i in range(3) for j in range(3))
            L = [[F(x) for x in row] for row in record["L"]]
            D = list(map(F, record["D"]))
            assert all(d >= 0 for d in D)
            assert all(
                sum(L[i][k] * D[k] * L[j][k] for k in range(3)) == sigma * P[i][j] - cov[i] * cov[j]
                for i in range(3)
                for j in range(3)
            )
        return True
    except (AssertionError, KeyError, ValueError, IndexError):
        return False


c = json.loads((PTH / "domain_geometry.json").read_text())
assert consume(c)
neg = []
for kind in ["P", "L", "D", "omit"]:
    m = copy.deepcopy(c)
    if kind == "P":
        m["P"][0][1] = "0"
    if kind == "L":
        m["residual_LDL"][0]["L"][1][0] = "0"
    if kind == "D":
        m["residual_LDL"][1]["D"][0] = "-1"
    if kind == "omit":
        m["residual_LDL"].pop()
    assert not consume(m)
    neg.append(kind)
modes = json.loads((PTH / "inventor_modes.json").read_text())
values = []
energies = []
for signs in product([-1, 1], repeat=3):
    z = [
        F(0) + signs[0] * F(1, 200),
        F(1, 10) + signs[1] * F(1, 200),
        F(2, 5) + signs[2] * F(1, 200),
    ]
    en = sum(P[i][j] * z[i] * z[j] for i in range(3) for j in range(3))
    energies.append(en)
    assert en < 12
    request = -z[0] - 3 * z[1] - 2 * z[2]
    assert request < -1
    for w in [-F(1, 100), F(1, 100)]:
        # Apply k to actual held trajectory with arbitrary common exp symbol E.
        t = F(1, 10)
        u = -1 + w
        for E in [F(0), F(1, 2), F(1)]:
            x = z[0] + t * z[1] + u * t * t / 2 + (z[2] - u) * (t - 1 + E)
            v = z[1] + u * t + (z[2] - u) * (1 - E)
            a = u + (z[2] - u) * E
            req = -x - 3 * v - 2 * a
            assert req == request - t * (z[1] + z[2]) - u * (2 * t + t * t / 2)
        values.append(req)
        assert -1 < req < 1
assert [str(min(values)), str(max(values))] == modes["active_box"]["request_at_time_1_10_range"]
assert str(max(energies)) == modes["active_box"]["max_vertex_energy"]
(PTH / "critic_replay.json").write_text(
    json.dumps(
        {
            "geometry_certificates": 2,
            "negative_controls_rejected": neg,
            "mode_vertices": 16,
            "mode_range": list(map(str, [min(values), max(values)])),
            "maximum_box_energy": str(max(energies)),
            "scope": "LDL identities exact and complete; continuum box extension uses PSD convexity and affine request. Source held dynamics maintained.",
        },
        indent=2,
    )
    + "\n"
)
print("2 LDL certificates,4 semantic corruptions and16 mode vertices checked")
