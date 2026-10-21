"""Rational held-out checks for the general rectified reduction."""

import json
from fractions import Fraction as F
from pathlib import Path

cases = []
for disparity in [F(-1), F(0), F(1), F(3, 2)]:
    for vertical in [F(0), F(1, 2), F(-3, 4)]:
        for s in [F(1, 10), F(1), F(2)]:
            baseline = F(3, 2)
            u1, u2, v1, v2 = disparity, F(0), F(1, 3), F(1, 3) + vertical
            z = baseline / s
            x = z * (u1 + (s - disparity) / 2)
            y = z * (v1 + vertical / 2)
            residual1 = (x / z - u1, y / z - v1)
            residual2 = ((x - baseline) / z - u2, y / z - v2)
            reduced = ((s - disparity) ** 2 + vertical**2) / 4
            assert sum(r * r for r in residual1) == reduced
            assert sum(r * r for r in residual2) == reduced
            if disparity <= 0:
                assert reduced > (disparity**2 + vertical**2) / 4
            cases.append(
                {
                    "disparity": str(disparity),
                    "vertical": str(vertical),
                    "s": str(s),
                    "point": [str(x), str(y), str(z)],
                    "squared_error": str(reduced),
                }
            )
report = {
    "cases_checked": len(cases),
    "cases": cases,
    "scope": "Exact rational identity checks, not sampling evidence for global optimality; universal algebra in Lean separately.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(f"{len(cases)} exact rectified positive-depth realizations passed.")
