"""Verify every coefficient of the exact symmetric-restriction Hilbert-Schmidt identity."""

import json
from fractions import Fraction as F
from pathlib import Path

N = 6


def mat():
    return [[0] * N for _ in range(N)]


def energy(a):
    total = F(0)
    for p in range(N):
        for q in range(p, N):
            s = mat()
            s[p][q] = s[q][p] = 1
            out = [
                [sum(a[i][k] * s[k][j] + s[i][k] * a[j][k] for k in range(N)) for j in range(N)]
                for i in range(N)
            ]
            total += F(sum(v * v for row in out for v in row), 1 if p == q else 2)
    return total


def formula(a):
    return 8 * sum(v * v for row in a for v in row) + sum(a[i][i] for i in range(N)) ** 2


basis = []
for i in range(N):
    for j in range(N):
        a = mat()
        a[i][j] = 1
        basis.append(a)
checks = 0
for i, a in enumerate(basis):
    assert energy(a) == formula(a)
    checks += 1
    for b in basis[i + 1 :]:
        c = [[a[r][s] + b[r][s] for s in range(N)] for r in range(N)]
        assert energy(c) == formula(c)
        checks += 1
result = {
    "dimension": 6,
    "coefficient_checks": checks,
    "identity": "||L_A restricted to Sym||_HS^2 = 8 ||A||_F^2 + (tr A)^2",
    "consequence": "s(A) >= sqrt(8/21) ||A||_F",
    "pair_norm_scaling": "K,Y need equal nonzero norms; singular value in paired equations remains 1 after common normalization",
    "safe_rational_exclusion": "If fixed K operator norm <=3, ||Y||_F/2=sqrt(7)<3, and an exact cokernel lower bound proves ||H||_F>9, then ||A||_F>2 and s(A)>sqrt(32/21)>1.",
}
Path(__file__).with_name("inventor_norm_gate.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

# Root/critic improvement, independently derived in inventor.md.
root = Path(__file__).parent
path_rows = json.loads((root / "inventor_perturb.json").read_text())
sharp = []
for row in path_rows[1:]:
    lower = F(row["H_frobenius_squared_lower_bound"])
    squared = F(1, 2) + lower / 14
    sharp.append(
        {
            "t": row["t"],
            "s_squared_lower_bound": str(squared),
            "approx": float(squared),
            "excludes_s_below_1": squared >= 1,
        }
    )
(root / "inventor_sharp_gate.json").write_text(json.dumps(sharp, indent=2) + "\n")
