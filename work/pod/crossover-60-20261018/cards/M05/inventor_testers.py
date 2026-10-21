"""Exact universal fixed-test and aggregate lower bounds at t=1/2."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import N, add, diagj, mul, zeros
from inventor_perturb import eye, solve, transpose


def nullspace(a):
    m = [row[:] for row in a]
    pivots = []
    rr = 0
    for j in range(len(m[0])):
        p = next((i for i in range(rr, len(m)) if m[i][j]), None)
        if p is None:
            continue
        m[rr], m[p] = m[p], m[rr]
        v = m[rr][j]
        m[rr] = [x / v for x in m[rr]]
        for i in range(len(m)):
            if i != rr:
                v = m[i][j]
                m[i] = [x - v * y for x, y in zip(m[i], m[rr], strict=True)]
        pivots.append(j)
        rr += 1
    result = []
    for j in range(len(m[0])):
        if j not in pivots:
            v = [F(0)] * len(m[0])
            v[j] = F(1)
            for i, p in enumerate(pivots):
                v[p] = -m[i][j]
            result.append(v)
    return result


def norm2(a):
    return sum(x * x for row in a for x in row)


def inner(a, b):
    return sum(
        x * y for row, srow in zip(a, b, strict=True) for x, y in zip(row, srow, strict=True)
    )


def lyap(a, s):
    return add(mul(a, s), mul(s, transpose(a)))


root = Path(__file__).parent
cert = json.loads((root / "inventor_minnorm.json").read_text())[0]
matrix = [[F(v) for v in row] for row in cert["M"]]
hc = list(map(F, cert["minimum_H_coefficients"]))
bases = []
for i in range(N):
    for j in range(i, N):
        h = zeros()
        h[i][j] = h[j][i] = F(1)
        bases.append(h)


def unvec(v):
    h = zeros()
    for coeff, basis in zip(v, bases, strict=True):
        h = add(h, basis, coeff)
    return h


q0 = zeros()
for i, j in enumerate([2, 3, 0, 1, 4, 5]):
    q0[i][j] = 1
u = eye()
u[0][0] = u[4][4] = F(3, 5)
u[0][4] = F(4, 5)
u[4][0] = F(-4, 5)
q = mul(mul(u, q0), transpose(u))
k = diagj([1, 2, 3])
y = mul(mul(q, k), q)
ki = diagj([-F(1), -F(1, 2), -F(1, 3)])
a0 = mul(add(unvec(hc), y, F(1, 2)), ki)
kernels = nullspace(matrix)
assert len(kernels) == 9
assert all(sum(x * v for x, v in zip(row, d, strict=True)) == 0 for row in matrix for d in kernels)
adirs = [mul(unvec(v), ki) for v in kernels]


def lower(tests):
    outs = [lyap(a0, s) for s, w in tests]
    dirs = [[lyap(a, s) for s, w in tests] for a in adirs]
    gram = [
        [
            sum(w * inner(di, dj) for di, dj, (_, w) in zip(ri, rj, tests, strict=True))
            for rj in dirs
        ]
        for ri in dirs
    ]
    linear = [
        sum(w * inner(di, o) for di, o, (_, w) in zip(row, outs, tests, strict=True))
        for row in dirs
    ]
    z = solve(gram, [-v for v in linear])
    aa = a0
    for a, v in zip(adirs, z, strict=True):
        aa = add(aa, a, v)
    result = sum(w * norm2(lyap(aa, s)) for s, w in tests)
    den = sum(w * norm2(s) for s, w in tests)
    assert result == sum(w * norm2(o) for o, (_, w) in zip(outs, tests, strict=True)) + sum(
        x * y for x, y in zip(linear, z, strict=True)
    )
    assert all(
        sum(x * v for x, v in zip(row, z, strict=True)) + ell == 0
        for row, ell in zip(gram, linear, strict=True)
    )
    assert add(add(mul(aa, k), mul(k, transpose(aa))), y, -1) == zeros()
    assert add(add(mul(transpose(aa), y), mul(y, aa)), k, -1) == zeros()
    return {
        "tests": [
            {"S": [[str(x) for x in row] for row in ss], "weight": str(w)} for ss, w in tests
        ],
        "normal_gram": [[str(x) for x in row] for row in gram],
        "linear": list(map(str, linear)),
        "optimizer_z": list(map(str, z)),
        "minimum_objective": str(result),
        "denominator": str(den),
        "minimizer_A": [[str(x) for x in row] for row in aa],
        "normal_stationarity_exact": True,
        "original_pair_equations_exact": True,
        "exact_s_squared_lower_bound": str(result / den),
        "approx": float(result / den),
        "excluding": result >= den,
    }


results = {"Q_universal": lower([(q, F(1))]), "I_universal": lower([(eye(), F(1))])}
for i in range(N):
    s = zeros()
    s[i][i] = 1
    results[f"e{i}_universal"] = lower([(s, F(1))])
    results[f"e{i}_particular"] = {
        "exact": str(norm2(lyap(a0, s))),
        "approx": float(norm2(lyap(a0, s))),
    }
alltests = [
    (s, F(1, 1 if i == j else 2))
    for (i, j), s in zip([(i, j) for i in range(N) for j in range(i, N)], bases, strict=True)
]
results["HS_universal"] = lower(alltests)
for weight in [1, 4, 16, 64]:
    results[f"HS_plus_Q_weight{weight}"] = lower(alltests + [(q, F(weight))])
results["kernel_H_coefficients"] = [list(map(str, v)) for v in kernels]
results["K"] = [[str(v) for v in row] for row in k]
results["Y"] = [[str(v) for v in row] for row in y]
results["particular_A_minH"] = [[str(v) for v in row] for row in a0]
(root / "inventor_testers.json").write_text(json.dumps(results, indent=2) + "\n")
print(
    json.dumps(
        {
            key: value["exact_s_squared_lower_bound"]
            for key, value in results.items()
            if isinstance(value, dict) and "exact_s_squared_lower_bound" in value
        },
        indent=2,
    )
)
