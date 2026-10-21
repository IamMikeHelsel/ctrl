"""Exact pointwise differential-curvature jet, not a global metric construction."""

import json
from itertools import product
from pathlib import Path

N = 14
s = [1] * 7 + [-1] * 7


def g(i, j):
    return s[i] if i == j else 0


def H(i, j, m):
    return int(i == j == m == 0)


def D(m, i, j, k, l):
    return H(i, k, m) * g(j, l) + H(j, l, m) * g(i, k) - H(i, l, m) * g(j, k) - H(j, k, m) * g(i, l)


algebraic = differential = 0
for m, i, j, k, l in product(range(N), repeat=5):
    r = D(m, i, j, k, l)
    assert r == -D(m, j, i, k, l) == -D(m, i, j, l, k) == D(m, k, l, i, j)
    assert r + D(m, i, k, l, j) + D(m, i, l, j, k) == 0
    algebraic += 1
    assert D(m, i, j, k, l) + D(i, j, m, k, l) + D(j, m, i, k, l) == 0
    differential += 1


def DR(m, i, l):
    return sum(s[j] * D(m, j, i, j, l) for j in range(N))


div = [sum(s[i] * DR(i, i, l) for i in range(N)) for l in range(N)]
dscalar = [sum(s[i] * DR(l, i, i) for i in range(N)) for l in range(N)]
assert div == [13] + [0] * 13
assert dscalar == [26] + [0] * 13
assert all(2 * a == b for a, b in zip(div, dscalar, strict=True))
out = {
    "algebraic_checks": algebraic,
    "differential_bianchi_checks": differential,
    "jet": "D_m R_ijkl = H_ikm g_jl+H_jlm g_ik-H_ilm g_jk-H_jkm g_il; H000=1, otherH0",
    "divergence_ricci": div,
    "scalar_gradient": dscalar,
    "E_beta_divergence": "26*(1-beta) in direction0; zero for this jet iff beta=1",
    "scope": "Exact finite algebraic and differential jet checks, not Lean theorem of general differential Bianchi nor constructed global metric. Normalization selection conditional on requiring divergence freedom on this admitted jet.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
