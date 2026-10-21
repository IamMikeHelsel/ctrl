"""Coefficient certificate for the second-pose rank minor across the beta family."""

import json
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path


def add(*ps):
    out = [F(0)] * max(map(len, ps))
    for p in ps:
        for i, x in enumerate(p):
            out[i] += x
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale(p, k):
    return add([F(k) * x for x in p])


def mul(*ps):
    out = [F(1)]
    for p in ps:
        result = [F(0)] * (len(out) + len(p) - 1)
        for i, x in enumerate(out):
            for j, y in enumerate(p):
                result[i + j] += x * y
        out = add(result)
    return out


beta, denom, cn, sn = (
    list(map(F, [0, 1])),
    list(map(F, [4, 0, 1])),
    list(map(F, [4, 0, -1])),
    list(map(F, [0, 4])),
)
points = [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2)]
mat = []
for u, v in points:
    qn = add(mul(cn, add([u * u + 1], scale(beta, u))), mul(beta, sn), scale(denom, v * v))
    tn = add([2], scale(beta, -u))
    ty = add(scale(sn, -u * u), scale(mul(sn, beta), -u), mul(beta, cn), scale(sn, -1))
    tz = scale(add(scale(add(cn, scale(denom, -1)), u), sn, scale(mul(beta, denom), -1)), v)
    wx = add(mul(add([u], beta), tn, denom), scale(mul(beta, qn), -1))
    wy = scale(mul(tn, denom), v)
    wz = add(mul(tn, denom), scale(qn, -2))
    mat.append([ty, tz, wx, wy, wz])
actual = [F(0)]
for perm in permutations(range(5)):
    sign = (-1) ** sum(perm[i] > perm[j] for i in range(5) for j in range(i + 1, 5))
    actual = add(actual, scale(mul(*(mat[i][perm[i]] for i in range(5))), sign))
expected = scale(mul(beta, beta, beta, beta, add(beta, [2]), *([denom] * 5)), 2)
assert actual == expected
numeric = json.loads(Path(__file__).with_name("inventor_conditioning.json").read_text())
for row in numeric["family"]:
    b = F(row["beta"])
    matrix = [[sum(c * b**i for i, c in enumerate(p)) / (4 + b * b) for p in line] for line in mat]
    assert matrix == [[F(x) for x in line] for line in row["jacobian_B"]]
result = {
    "coefficient_order": "ascending powers of beta",
    "scaled_matrix_entries": [[[str(c) for c in p] for p in row] for row in mat],
    "actual_determinant_coefficients": [str(c) for c in actual],
    "numeric_matrix_binding_cases_checked": len(numeric["family"]),
    "factored_expected_coefficients": [str(c) for c in expected],
    "identity": "det((4+beta^2) J_B)=2 beta^4 (beta+2) (4+beta^2)^5; hence det(J_B)=2 beta^4 (beta+2).",
    "domain": "beta>0, rational Cayley rotation; denominator4+beta^2 nonzero, tx=beta gauge chart valid. Both hypotheses have full local rank5 throughout this positive-beta family.",
    "evidence": "Direct exact polynomial coefficient expansion, not Lean or a symbolic solver claim.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result["identity"])
