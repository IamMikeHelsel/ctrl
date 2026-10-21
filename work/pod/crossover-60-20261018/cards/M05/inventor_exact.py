"""Exact pair-compatibility checks; no numerical or norm-conjecture conclusion."""

import json
from fractions import Fraction as F
from pathlib import Path

N = 6


def zeros():
    return [[F(0) for _ in range(N)] for _ in range(N)]


def add(a, b, scale=1):
    return [[a[i][j] + scale * b[i][j] for j in range(N)] for i in range(N)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(N)) for j in range(N)] for i in range(N)]


def trace(a):
    return sum(a[i][i] for i in range(N))


def diagj(values):
    a = zeros()
    for i, v in enumerate(values):
        a[2 * i][2 * i + 1] = F(v)
        a[2 * i + 1][2 * i] = -F(v)
    return a


def rank(a):
    a = [list(r) for r in a]
    r = 0
    for j in range(len(a[0])):
        piv = next((i for i in range(r, len(a)) if a[i][j]), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        v = a[r][j]
        a[r] = [x / v for x in a[r]]
        for i in range(len(a)):
            if i != r:
                v = a[i][j]
                a[i] = [x - v * y for x, y in zip(a[i], a[r], strict=True)]
        r += 1
    return r


def run(kvals, yvals):
    k, y = diagj(kvals), diagj(yvals)
    k2, y2 = mul(k, k), mul(y, y)
    t = mul(y, k)
    rhs = add(mul(k2, k), add(mul(y2, k), mul(k, y2)), F(-1, 2))
    delta = add(y2, k2, -1)
    moments = [trace(delta), trace(mul(t, delta)), trace(mul(mul(t, t), delta))]
    cols = []
    for i in range(N):
        for j in range(i, N):
            h = zeros()
            h[i][j] = h[j][i] = F(1)
            phi = add(mul(mul(k, y), h), mul(h, t), -1)
            cols.append([phi[a][b] for a in range(N) for b in range(a + 1, N)])
    matrix = [list(r) for r in zip(*cols, strict=True)]
    right = [rhs[a][b] for a in range(N) for b in range(a + 1, N)]
    augmented = [r + [v] for r, v in zip(matrix, right, strict=True)]
    # W=diag(J,0,0) is an exact Frobenius cokernel witness in both diagonal cases.
    w = diagj([1, 0, 0])
    wvec = [w[a][b] for a in range(N) for b in range(a + 1, N)]
    annihilator = [sum(wvec[i] * col[i] for i in range(15)) for col in cols]
    pairing = -trace(mul(w, rhs))
    assert not any(annihilator)
    return {
        "K_blocks": kvals,
        "Y_blocks": yvals,
        "moments": list(map(str, moments)),
        "phi_rank": rank(matrix),
        "augmented_rank": rank(augmented),
        "cokernel_dimension": 15 - rank(matrix),
        "kernel_dimension": 21 - rank(matrix),
        "RHS_J_blocks": [str(rhs[2 * i][2 * i + 1]) for i in range(3)],
        "W_frobenius_RHS": str(pairing),
        "W_annihilates_all_21_columns": True,
    }


results = {
    "degenerate_inconsistent": run([1, 2, 3], [2, 1, 3]),
    "generic_compatible": run([1, 2, 3], [1, 2, 3]),
    "degenerate_compatible": run([1, 1, 1], [1, 1, 1]),
    "scope": "Exact rational computation about paired singular equations only; not a counterexample to the Sym-versus-Skew operator-norm conjecture.",
}
assert results["degenerate_inconsistent"]["moments"] == ["0", "0", "0"]
assert results["degenerate_inconsistent"]["phi_rank"] == 8
assert results["degenerate_inconsistent"]["augmented_rank"] == 9
assert results["degenerate_inconsistent"]["W_frobenius_RHS"] == "6"
assert results["generic_compatible"]["phi_rank"] == 12
assert results["generic_compatible"]["augmented_rank"] == 12
Path(__file__).with_name("inventor_exact.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
