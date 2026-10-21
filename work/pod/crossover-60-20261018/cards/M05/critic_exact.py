"""Independent exact Fraction audit of fixed-pair compatibility; no Lean claim."""

import json
from fractions import Fraction as F
from pathlib import Path

N = 6


def zero(r=N, c=N):
    return [[F(0) for _ in range(c)] for _ in range(r)]


def transpose(a):
    return [list(x) for x in zip(*a, strict=True)]


def add(a, b, scale=F(1)):
    return [
        [x + scale * y for x, y in zip(ar, br, strict=True)] for ar, br in zip(a, b, strict=True)
    ]


def mul(a, b):
    return [
        [sum(x * y for x, y in zip(ar, bc, strict=True)) for bc in zip(*b, strict=True)] for ar in a
    ]


def eye(n=N):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def tr(a):
    return sum(a[i][i] for i in range(len(a)))


def rank(a):
    a = [row[:] for row in a]
    r = 0
    for c in range(len(a[0])):
        q = next((i for i in range(r, len(a)) if a[i][c]), None)
        if q is None:
            continue
        a[r], a[q] = a[q], a[r]
        d = a[r][c]
        a[r] = [x / d for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                d = a[i][c]
                a[i] = [x - d * y for x, y in zip(a[i], a[r], strict=True)]
        r += 1
        if r == len(a):
            break
    return r


def skew(weights):
    a = zero()
    for i, w in enumerate(weights):
        a[2 * i][2 * i + 1] = F(w)
        a[2 * i + 1][2 * i] = -F(w)
    return a


def sym_basis():
    result = []
    for i in range(N):
        for j in range(i, N):
            a = zero()
            a[i][j] = a[j][i] = F(1)
            result.append(a)
    return result


def upper(a):
    return [a[i][j] for i in range(N) for j in range(i + 1, N)]


def audit(k, y, kinv, name):
    ky, yk = mul(k, y), mul(y, k)
    yy, kk = mul(y, y), mul(k, k)
    rhs = add(mul(kk, k), add(mul(yy, k), mul(k, yy)), F(-1, 2))
    cols = [upper(add(mul(ky, h), mul(h, yk), -1)) for h in sym_basis()]
    phi = transpose(cols)
    augmented = [r + [v] for r, v in zip(phi, upper(rhs), strict=True)]
    defect = add(yy, kk, -1)
    moments = []
    power = eye()
    for _ in range(8):
        moments.append(tr(mul(power, defect)))
        power = mul(power, yk)
    ws = [kinv, y, mul(mul(y, k), y)]
    pairings = [-tr(mul(w, rhs)) for w in ws]
    annihilates = [
        all(tr(mul(w, add(mul(ky, h), mul(h, yk), -1))) == 0 for h in sym_basis()) for w in ws
    ]
    result = dict(
        name=name,
        rank_phi=rank(phi),
        rank_augmented=rank(augmented),
        cokernel_dimension=15 - rank(phi),
        symmetric_kernel_dimension=21 - rank(phi),
        moments=list(map(str, moments)),
        pairings=list(map(str, pairings)),
        three_witness_rank=rank([upper(w) for w in ws]),
        witnesses_annihilate_phi=annihilates,
        selfadjoint_K=mul(transpose(yk), k) == mul(k, yk),
        selfadjoint_Kinv=mul(transpose(yk), kinv) == mul(kinv, yk),
        rhs=[[str(v) for v in r] for r in rhs],
    )
    assert pairings == moments[:3]
    assert all(annihilates)
    assert result["selfadjoint_K"]
    return result


k = skew([1, 2, 3])
ki = skew([-1, F(-1, 2), F(-1, 3)])
assert mul(k, ki) == eye()
cases = [
    audit(k, k, ki, "distinct_calibration"),
    audit(k, skew([2, 1, 3]), ki, "semisimple_repeated_incompatible"),
]
y = skew([1, 2, 3])
y[0][2] = F(1)
y[2][0] = F(-1)
cases.append(audit(k, y, ki, "offblock_form_check"))
# Non-semisimple symplectically selfadjoint T: diag(Jordan3, Jordan3.T).
k2 = zero()
for i in range(3):
    k2[i][i + 3] = F(1)
    k2[i + 3][i] = F(-1)
t = eye()
t[0][1] = t[1][2] = t[4][3] = t[5][4] = F(1)
k2inv = [[-v for v in row] for row in k2]
y2 = mul(t, k2inv)
assert y2 == [[-v for v in row] for row in transpose(y2)]
cases.append(audit(k2, y2, k2inv, "nonsemisimple_single_eigenvalue"))
k3 = skew([1, 2, F(1, 2)])
y3 = skew([1, F(1, 2), 2])
ki3 = skew([-1, F(-1, 2), -2])
cases.append(audit(k3, y3, ki3, "scalar_product_incompatible"))
assert cases[-1]["rank_phi"] == 0 and cases[-1]["rank_augmented"] == 1
assert all(v == "0" for v in cases[-1]["moments"])
assert cases[0]["rank_phi"] == 12 and cases[0]["rank_augmented"] == 12
assert cases[1]["rank_phi"] == 8 and cases[1]["rank_augmented"] == 9
assert all(v == "0" for v in cases[1]["moments"])
assert not cases[2]["selfadjoint_Kinv"]
path = Path(__file__).with_name("critic_exact_results.json")
path.write_text(
    json.dumps({"arithmetic": "Python Fraction exact rational", "cases": cases}, indent=2) + "\n"
)
print(json.dumps([{k: v for k, v in row.items() if k != "rhs"} for row in cases], indent=2))
