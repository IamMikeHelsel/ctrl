"""Numerical dual proposal, then exact rational evaluation, on one thirteen-smooth leaf."""

import json
from fractions import Fraction as F
from itertools import product
from math import gcd, prod
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

HERE = Path(__file__).resolve().parent
source = Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json")
saved = json.loads(source.read_text())
P = saved["period"]
assigned = saved["worst_assignment"]
U = [x for x in range(P) if all(x % m != a for m, a in assigned)]
removed = {m for m, _ in assigned}
mass = {}
primes, caps = saved["primes"], saved["caps"]
for exponents in product(range(1, caps[0] + 1), *(range(c + 1) for c in caps[1:])):
    m = prod(p**e for p, e in zip(primes, exponents, strict=True))
    if m >= 4 and m not in removed and pow(2, m, m + 1) == pow(3, m, m + 1) == 1:
        g = gcd(P, m)
        mass[g] = mass.get(g, F()) + F(1, m)
tail = F(saved["tail"])
groups = sorted(mass)
n = len(U)
rows, cols, data, rhs = [], [], [], []
row = 0
for j, g in enumerate(groups):
    for a in range(g):
        matches = [i for i, x in enumerate(U) if x % g == a]
        if not matches:
            continue
        for i in matches:
            rows.append(row)
            cols.append(i)
            data.append(1.0)
        rows.append(row)
        cols.append(n + j)
        data.append(-1.0)
        rhs.append(0.0)
        row += 1
for i in range(n):
    rows.extend((row, row))
    cols.extend((i, n + len(groups)))
    data.extend((1.0, -1.0))
    rhs.append(0.0)
    row += 1
objective = np.zeros(n + len(groups) + 1)
objective[n : n + len(groups)] = [float(mass[g] * g) for g in groups]
objective[-1] = float(tail * P)
A = coo_matrix((data, (rows, cols)), shape=(row, len(objective))).tocsr()
equal = np.zeros((1, len(objective)))
equal[0, :n] = 1.0
sol = linprog(
    objective,
    A_ub=A,
    b_ub=rhs,
    A_eq=equal,
    b_eq=[1.0],
    bounds=(0, None),
    method="highs",
    options={"time_limit": 45},
)
result = {
    "success": bool(sol.success),
    "status": int(sol.status),
    "message": sol.message,
    "variables": len(objective),
    "constraints": row,
    "scope": "One fixed leaf; numerical optimizer only proposes weights; exact rational objective below checks feasible upper bound, not optimality.",
}
if sol.x is not None:
    w = [F(max(0, float(x))).limit_denominator(10**8) for x in sol.x[:n]]
    total = sum(w)
    w = [x / total for x in w]
    upper = tail * P * max(w)
    for g in groups:
        buckets = [F() for _ in range(g)]
        for x, v in zip(U, w, strict=True):
            buckets[x % g] += v
        upper += mass[g] * g * max(buckets)
    result.update(
        numeric_objective=float(sol.fun),
        exact_upper=str(upper),
        exact_excess=str(upper - 1),
        exact_excess_float=float(upper - 1),
        nonzero=sum(x > 0 for x in w),
        excludes=upper < 1,
    )
    (HERE / "pm_weighted_dual_weights.json").write_text(
        json.dumps({"residues": U, "weights": [str(x) for x in w]}, separators=(",", ":")) + "\n"
    )
(HERE / "pm_weighted_dual.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
# Exact weak-duality obstruction: no optimizer-optimality claim is needed.
if sol.success:
    y = [F(max(0.0, float(-x))).limit_denominator(10**9) for x in sol.ineqlin.marginals]
    row = 0
    coverage = [F() for _ in U]
    multipliers = {}
    for g in groups:
        ys = {}
        for a in range(g):
            indices = [i for i, x in enumerate(U) if x % g == a]
            if not indices:
                continue
            ys[a] = y[row]
            row += 1
        budget = mass[g] * g
        total_y = sum(ys.values())
        if total_y > budget:
            ys = {a: v * budget / total_y for a, v in ys.items()}
        assert sum(ys.values()) <= budget
        for i, x in enumerate(U):
            coverage[i] += ys[x % g]
        multipliers[g] = {a: str(v) for a, v in ys.items() if v}
    tail_y = y[row:]
    assert len(tail_y) == len(U)
    total_y = sum(tail_y)
    if total_y > tail * P:
        tail_y = [v * tail * P / total_y for v in tail_y]
    coverage = [a + b for a, b in zip(coverage, tail_y, strict=True)]
    minimum = min(coverage)
    cert = {
        "group_multipliers": multipliers,
        "tail_multipliers": [str(v) for v in tail_y],
        "residues": U,
        "claimed_minimum": str(minimum),
        "interpretation": "Fractional upper-bound relaxation only, NOT a congruence covering.",
    }
    (HERE / "pm_fractional_obstruction_certificate.json").write_text(
        json.dumps(cert, separators=(",", ":")) + "\n"
    )
    result.update(
        exact_fractional_minimum=str(minimum),
        exact_fractional_minimum_float=float(minimum),
        any_weighted_single_capacity_exclusion_impossible=minimum >= 1,
    )
    (HERE / "pm_weighted_dual.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Exact fractional lower bound:", float(minimum), ">=1:", minimum >= 1)
