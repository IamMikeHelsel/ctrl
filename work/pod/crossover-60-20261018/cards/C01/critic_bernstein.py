"""Independent certificate consumer: expand Bernstein basis back to source jerk."""

import copy
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)
PHASES = json.loads(SOURCE.read_text())
CERT = json.loads((BASE / "inventor_tracking_bound.json").read_text())


def verify(cert):
    count = 0
    for phase in PHASES:
        polys = [F(c) for c in phase["position_coefficients_local_time"]]
        for _ in range(3):
            polys = [i * c for i, c in enumerate(polys)][1:] or [F(0)]
        certificates = [r for r in cert["subinterval_certificates"] if r["phase"] == phase["name"]]
        end = F(0)
        for row in certificates:
            left, width = F(row["local_left"]), F(row["width"])
            if left != end or width <= 0:
                raise ValueError("coverage")
            end = left + width
            bern = list(map(F, row["Bernstein_jerk_coefficients"]))
            n = len(bern) - 1
            coefficients = [F(0)] * max(len(polys), n + 1)
            for k, b in enumerate(bern):
                if abs(b) > 10:
                    raise ValueError("range")
                for j in range(n - k + 1):
                    coefficients[k + j] += b * comb(n, k) * comb(n - k, j) * (-1) ** j
            source = [F(0)] * len(coefficients)
            for degree, c in enumerate(polys):
                for j in range(degree + 1):
                    source[j] += c * comb(degree, j) * left ** (degree - j) * width**j
            if coefficients != source:
                raise ValueError("polynomial binding")
            count += 1
        if end != F(phase["end"]) - F(phase["start"]):
            raise ValueError("end coverage")
    return count


count = verify(CERT)
rejections = []
for kind in ["coefficient", "coverage", "bound"]:
    bad = copy.deepcopy(CERT)
    row = bad["subinterval_certificates"][0]
    if kind == "coefficient":
        row["Bernstein_jerk_coefficients"][0] = "9"
    elif kind == "coverage":
        row["local_left"] = "1/100"
    else:
        row["Bernstein_jerk_coefficients"][0] = "11"
    try:
        verify(bad)
    except ValueError as error:
        rejections.append(dict(mutation=kind, rejected=str(error)))
    else:
        raise ValueError("corruption accepted")
result = dict(
    subintervals_verified=count,
    negative_controls=rejections,
    scope="Exact polynomial binding and coverage plus standard Bernstein convex-hull argument; no Lean ODE proof",
)
(BASE / "critic_bernstein_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
