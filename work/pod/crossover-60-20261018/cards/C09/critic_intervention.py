"""Independent exact reconstruction of intervention and measurement interfaces."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

P = Path(__file__).parent
producer = json.loads((P / "inventor_intervention.json").read_text())
# Integrate d(t)=1/2+((t-48)^2-48^2-W^2/12)/2000 over each centered window.
W = F(1, 2)


def primitive(t):
    return t / 2 + (t**3 / 3 - 48 * t * t - W * W * t / 12) / 2000


averages = []
for center in [F(0), F(32), F(64), F(96)]:
    averages.append((primitive(center + W / 2) - primitive(center - W / 2)) / W)
assert averages == [F(1, 2), F(-131, 250), F(-131, 250), F(1, 2)]
signs = [1, -1, -1, 1]
w = F(1, 2)
measurements = [sgn * w + d for sgn, d in zip(signs, averages, strict=True)]
estimate = sum(sgn * y for sgn, y in zip(signs, measurements, strict=True)) / 4
assert estimate == F(producer["phase_cycling"]["finite_window_false_estimate"]) == F(253, 250)
assert abs(estimate - 1) + F(1, 40) < F(1, 8) < abs(w - 1)
drift_budget = F(1, 40) + F(1, 1000) * 32**2 / 2
assert drift_budget == F(producer["phase_cycling"]["drift_aware_error_bound"]) == F(537, 1000)
# Direct homogeneous tail from retained x_T,z_T with z=v+a*x:
# x(T+s)=exp(-a*s)*(x_T+s*z_T). This uses actual f=0 after T.
e6_lower = sum(F(6**k, factorial(k)) for k in range(10))
assert e6_lower == F(producer["oscillator"]["e6_lower"])
tail = 28 / e6_lower
assert tail == F(producer["oscillator"]["s6_rational_upper"]) == F(196, 2587) < F(1, 10)
# Retaining nonzero forcing invalidates the zero-force termination: a1,f4,x4,v0
# is an exact equilibrium, never enters a 0.1 position band.
assert 0 + 2 * 1 * 0 + 1**2 * 4 == 4
assert F(4) > F(1, 10)
# Real-force image counterexample: T1, omega_w=pi/2, omega_d=5pi/2,w=d1/2.
# Intended analytic demod givesz=.5; doubled real demod yields.5-4i/(3pi).
# Thus frequency separation alone does not remove conjugate image terms.
image_error_lower = F(4, 3) / F(22, 7)
assert image_error_lower == F(14, 33) > F(1, 40)
# Unknown oscillator transfer: H_a(i*1)=1/(a+i)^2; at a1 H=-i/2,
# while a2 H=(3-4i)/25. Neither is unit gain.
assert (F(3, 25) ** 2 + F(-4, 25) ** 2) == F(1, 25)
report = {
    "status": "pass",
    "ABBA_exact_means": [str(x) for x in averages],
    "ABBA_wrong_estimate": str(estimate),
    "ABBA_drift_budget": str(drift_budget),
    "retained_state_tail_bound_at6": str(tail),
    "real_sensor_image_error_lower": str(image_error_lower),
    "new_negative_controls": [
        "complex analytic measurement is not real scalar demod",
        "unknown H_a cannot be replaced by gain1",
        "ending detune command does not remove forcing",
    ],
    "scope": "Independent finite exact algebra; invariant comparison, complex integration, and physical acquisition interfaces remain explicit analytic assumptions.",
}
(P / "critic_intervention.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
