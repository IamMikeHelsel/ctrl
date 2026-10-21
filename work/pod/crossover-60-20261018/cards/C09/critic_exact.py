"""Independent exact complex-action and measurement-interface controls."""

import json
from fractions import Fraction as F
from pathlib import Path


def norm2(z):
    return z[0] ** 2 + z[1] ** 2


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


eta = F(1, 100)
leakage = eta / (1 - eta)
wheel = F(1, 40) + 2 * leakage
assert wheel == F(179, 3960) < F(1, 8)
baseline_endpoint = F(1, 2) + F(1, 10)
closure = baseline_endpoint + F(22, 175)
assert closure == F(127, 175) < F(3, 4)
posterior_d = baseline_endpoint + wheel
arbitrary_phase = posterior_d + wheel
assert arbitrary_phase == F(1367, 1980) < F(3, 4)
assert F(3, 4) - arbitrary_phase == F(59, 990)
eta2 = F(1, 50)
wheel2 = F(1, 40) + 2 * eta2 / (1 - eta2)
assert baseline_endpoint + 2 * wheel2 == F(717, 980) < F(3, 4)
eta_max = F(1, 41)
assert baseline_endpoint + 2 * (F(1, 40) + 2 * eta_max / (1 - eta_max)) == F(3, 4)
# Positive rational phase representatives; universal guarantee is triangle inequality.
phases = [(F(1), F(0)), (F(-1), F(0)), (F(0), F(1)), (F(3, 5), F(4, 5))]
for phase in phases:
    assert norm2(phase) == 1
    r = (wheel, F(0))
    d = tuple(posterior_d * x for x in phase)
    assert norm2(add(r, d)) <= arbitrary_phase**2
# Countermodel to dropping quadrature from original real-only measurements.
w = (F(1, 2), F(1, 4))
d = (F(1, 2), F(-1, 4))
c = (F(-1, 2), F(0))
assert add(w, d) == (1, 0)
assert w[0] + F(1, 4) * d[0] == F(5, 8)
assert w[0] + F(1, 8) * d[0] == F(9, 16)
assert norm2(add(w, c)) == F(1, 16) > F(1, 8) ** 2
# Common measurement frame flip does not change a numerical difference bound.
true_w = true_d = (F(-1, 2), F(0))
measured_b = (F(1), F(0))
measured_z = (F(1, 2), F(0))
assert norm2(add(true_w, c)) == 1
assert measured_b[0] - measured_z[0] + F(1, 10) == F(3, 5)
# Post-acquisition wheel-source drift is outside the no-drift contract.
w_after = (F(7, 10), F(0))
assert norm2(add(w_after, c)) == F(1, 25) > F(1, 8) ** 2
assert F(1, 8) - wheel == F(79, 990)
# Simultaneous +1% frequency and window-duration errors create 2.01% detuning.
delta = F(101, 100) ** 2 - 1
# |sinc(pi*(1+delta))| >= delta/(1+delta)*(1-pi²delta²/6), using sin Taylor.
clock_lower = delta / (1 + delta) * (1 - F(10) * delta**2 / 6)
assert clock_lower > F(1, 99)
report = {
    "status": "pass",
    "wheel_bound": str(wheel),
    "phase_closure_bound": str(closure),
    "posterior_nuisance_amplitude": str(posterior_d),
    "arbitrary_nuisance_phase_bound": str(arbitrary_phase),
    "arbitrary_phase_slack": str(F(3, 4) - arbitrary_phase),
    "eta_002_mixed_bound": str(F(717, 980)),
    "sufficient_eta_threshold_arbitrary_phase": str(eta_max),
    "clock_error_effective_detuning": str(delta),
    "clock_leakage_lower": str(clock_lower),
    "negative_controls": [
        "discarded quadrature",
        "unbound common phase frame",
        "post-measurement source drift",
        "unbudgeted window duration error",
    ],
    "scope": "Static complex action gate with unchanged amplitudes/path and bound phase frame; dynamics and actuator realization separate. Clock lower bound uses elementary sine Taylor inequality, not Lean.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
