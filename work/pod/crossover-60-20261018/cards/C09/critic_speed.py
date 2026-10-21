"""Independent prospective speed-scaled toy budget audit; no actuator realization."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

P = Path(__file__).parent
r = json.loads((P / "pm_speed_scaled.json").read_text())
eta = F(1, 100)
nu = F(1, 10) * (1 + eta)
gamma = (1 + nu / 10) ** 2
ell = gamma / 99
probe = 2 + 2 * gamma
B = (F(1, 40) + ell * F(3, 5)) / (1 - ell)
D = F(3, 5) + B
post = B + D
exp_lower = sum(F(6**k, factorial(k)) for k in range(21))
assert exp_lower > 400
x6 = post + (probe - post) * F(7, 400)
fields = {
    "force_gain_max": gamma,
    "leakage_bound_in_baseline_d_units": ell,
    "probe_force_bound": probe,
    "new_wheel_residual_bound": B,
    "baseline_nuisance_magnitude_bound": D,
    "post_correction_force_bound_any_nuisance_phase": post,
    "post_handoff_travel6_upper": x6,
    "exp6_lower_taylor20": exp_lower,
    "actual_relative_speed_bound": nu,
    "actual_relative_acceleration_bound": F(101, 10000),
}
for key, value in fields.items():
    assert F(r[key]) == value
assert probe < F(41, 10) and x6 < 1 and post < F(3, 4) and B < F(1, 8)
assert F(r["excitation_duration_upper_using_pi22over7"]) == 20 + 20 * F(22, 7) < 83
# The simpler unit-amplitude interface remains a separate valid contract.
i = json.loads((P / "inventor_closed_interface.json").read_text())
Fpost = F(1299, 1960)
e6 = sum(F(6**k, factorial(k)) for k in range(10))
assert F(i["x6_rational_upper"]) == Fpost + (4 - Fpost) * 7 / e6 == F(1840511, 2535260)
report = {
    "status": "pass",
    "checked_fields": {k: str(v) for k, v in fields.items()},
    "comparison": "For norms X,Z, Xdot<=-X+Z, Zdot<=-Z+Fpost; retained X0,Z0<=Fprobe. Variation-of-constants hand bridge, no kernel ODE claim.",
    "deadline_boundary": "83 bounds detune ramps, plateau and return. Correction-ramp duration is not bound by gamma in[0,1] alone.",
    "scope": "Prospective normalized toy with direct two-axis force sensor, constant a and declared exact speed gain; not physical actuator/sensor verification or historical predeclared limits.",
}
(P / "critic_speed.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"status": "pass", "probe": float(probe), "post": float(post), "x6": float(x6)}))
