"""Exact source-formula derivative scaling under a smooth affine phase clock."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
coeff = [1, -4, 6, -4, 1]


def f2(x):
    return sum(c * max(x - i, F(0)) ** 2 for i, c in enumerate(coeff)) / 2


h = F(1, 5)
events = [(F(11, 50), F(1, 50)), (F(31, 50), F(-1, 50))]
phase = F(41, 50)
s = F(10001, 10000)
physical_time = phase / s
A = sum(delta / h**2 * f2((phase - start) / h) for start, delta in events)
assert A == -F(1, 2)
physical_A = A * s * s
assert abs(physical_A) == F(100020001, 200000000) > F(1, 2)
T = F(17, 10)
uniform_bias = (s - 1) * T
assert uniform_bias == F(17, 100000) < F(1, 200)
out = {
    "source": "bundle-v4 FutureCommitFixtures.movingBase + pendingReturn, Kernel.F2",
    "events": events,
    "width": h,
    "phase": phase,
    "physical_time": physical_time,
    "clock_rate": s,
    "horizon": T,
    "uniform_bias_on_horizon": uniform_bias,
    "nominal_acceleration": A,
    "physical_reference_acceleration": physical_A,
    "excess_over_half": abs(physical_A) - F(1, 2),
    "scope": "Exact q(C(t)) reference derivative underC(t)=s*t, using chain rule and source polynomial at specified phase. Clock is smooth/strictly increasing and tiny-offset; physical robot dynamics unmodeled. No original ideal-clock theorem violation.",
}
(P / "pm_affine_clock.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps(out, default=str))
