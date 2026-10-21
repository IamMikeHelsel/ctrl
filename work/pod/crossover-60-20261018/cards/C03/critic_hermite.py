"""Independent polynomial/derivative and fixed-partition Bernstein checks."""

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

P = Path(__file__).resolve().parent
r = json.loads((P / "pm_hermite.json").read_text())
T = F(r["duration"])
c = list(map(F, r["coefficients"]))
start = list(map(F, r["source_execution_state"]))
target = [F(3, 5), F(0), F(0), F(0)]
checks = []
for order, (lo, hi) in enumerate(
    [(F(0), F(3, 5)), (F(0), F(1)), (F(-3), F(3)), (F(-10), F(10)), (F(-400), F(400))]
):
    physical = [x / T**order for x in c]
    if order < 4:
        assert physical[0] == start[order]
        assert sum(physical) == target[order]
    if order == 3:
        witness = sum(x * F(1, 4) ** i for i, x in enumerate(physical))
        assert witness == F(-951922405, 73188736) < -10
        checks.append({"order": order, "exact_quarter_witness": str(witness)})
    else:
        n = len(c) - 1
        mn = None
        mx = None
        for cell in range(64):
            left = F(cell, 64)
            width = F(1, 64)
            local = [
                sum(physical[k] * comb(k, j) * left ** (k - j) * width**j for k in range(j, n + 1))
                for j in range(n + 1)
            ]
            bern = [
                sum(local[j] * F(comb(i, j), comb(n, j)) for j in range(i + 1))
                for i in range(n + 1)
            ]
            assert min(bern) >= lo and max(bern) <= hi
            mn = min(bern) if mn is None else min(mn, min(bern))
            mx = max(bern) if mx is None else max(mx, max(bern))
        checks.append({"order": order, "64_cell_Bernstein_min": str(mn), "max": str(mx)})
    c = [i * x for i, x in enumerate(c)][1:]
(P / "critic_hermite.json").write_text(
    json.dumps(
        {
            "source_bound_endpoints": True,
            "checks": checks,
            "scope": "One polynomial fails jerk; original piecewise feasible task unchanged.",
        },
        indent=2,
    )
    + "\n"
)
print("Full state, four passing derivative/corridor bounds and exact jerk failure verified")
