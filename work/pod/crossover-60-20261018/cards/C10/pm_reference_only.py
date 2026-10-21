"""Reference-only finite tube plus analytic post-horizon tail, fixed rate8."""

import json
from fractions import Fraction as F
from pathlib import Path

import domain_enclose as d

P = Path(__file__).resolve().parent
state = [d.point(0)] * 3 + [d.point(1), d.point(1)]
peak = 0
records = []
for idx in range(408):
    j = (10, -10, -10, 10)[idx // 2] if idx < 8 else 0
    A = d.matrix(F(8), F(0), F(j))
    A[2][3] = 0
    A[2][4] = -F(j)
    state, tube, n, pad = d.step(A, state)
    peak = max(peak, abs(tube[0][0]), abs(tube[0][1]))
    records.append(
        {
            "time": str((idx + 1) * d.DT),
            "position_tube": d.decimal_box(tube[0]),
            "degree": n,
            "tail_pad": str(pad),
        }
    )
upper = F(d.ceil(F(peak, d.SCALE) * 10**12), 10**12)
# For s>=4, f(s)=(1+8s+8s^2)e^(-4s) decreases: f'=4-16s-32s^2<0.
# exp(16)>=2^16, hence |h''(s)|<=161/65536. q' support[0,.08], integral D.
D = F(1, 6250)
tail = D * F(161, 65536)
disturbance = F(1, 2000) / 8
alltime = max(upper, tail) + disturbance
assert alltime < F(1, 5000)
result = {
    "fixed_rate": 8,
    "kappa": 0,
    "reference_only_continuous_bound_0_to_4_08_m": str(upper),
    "post4_08_reference_bound_m": str(tail),
    "arbitrary_disturbance_contribution_m": str(disturbance),
    "alltime_bound_m": str(alltime),
    "bound_mm": float(alltime * 1000),
    "passes_point2mm": True,
    "scope": "Exact finite enclosure plus hand-derived positive disturbance-kernel and monotone reference-velocity convolution bridge; full ODE/convolution bridge not Lean checked. Fixedr8 only, arbitrary bounded w subject trajectory existence.",
    "cells": records,
}
(P / "pm_reference_only.json").write_text(json.dumps(result, indent=2) + "\n")
print({k: v for k, v in result.items() if k != "cells"})
