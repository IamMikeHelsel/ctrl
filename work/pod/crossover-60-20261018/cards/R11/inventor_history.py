"""Exact startup-history and target-revision diagnostics; no physical plant claim."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
H, eps, v0, gain = F(1, 50), F(1, 10000), -F(1, 1000), F(10)


def history(u):
    p = 2 * u**3 - 3 * u**2 + u
    return eps + v0 * H * p, v0 * (6 * u**2 - 6 * u + 1), v0 / H * (12 * u - 6)


assert history(F(0))[:2] == history(F(1))[:2] == (eps, v0)
# Two equal Hermite intervals join in x,v. At zero the first controller ramp
# has the same v0, but zero acceleration; acceleration jumps are allowed.
assert history(F(1))[2] == -F(3, 10)
assert history(F(0))[2] == F(3, 10)
rows = []
for i in range(101):
    u = F(i, 100)
    x, v, a = history(u)
    # Polynomial identities establish the continuum bounds in the supplement.
    assert 2 * u**3 - 3 * u**2 + u == u * (1 - u) * (1 - 2 * u)
    assert 6 * u**2 - 6 * u + 1 == 6 * (u - F(1, 2)) ** 2 - F(1, 2)
    assert abs(x - eps) <= abs(v0) * H / 4
    assert abs(v) <= abs(v0)
    assert abs(a) <= F(3, 10)
    rows.append([str(u), str(x), str(v), str(a)])
# The unchanged law operating before zero cannot generate this equal triple:
# its prior interval would carry constant v0, moving by -1/50000.
prior_controller_displacement = H * v0
assert prior_controller_displacement == -F(1, 50000) != 0
# A compatible law-generated continuation is available after two startup steps.
A = [[F(1), -F(1, 10), -F(1, 10)], [F(1), F(0), F(0)], [F(0), F(1), F(0)]]
X = [eps] * 3
for _ in range(2):
    X = [sum((a * b for a, b in zip(row, X, strict=True)), F(0)) for row in A]
assert X == [F(3, 50000), F(1, 12500), F(1, 10000)]
assert -gain * X[2] == v0
# Diagnostic target jump: absolute reference is retained, target moves by .1rad.
delta = F(1, 10)
raw_new_velocity = -gain * (eps - delta)
assert raw_new_velocity == F(999, 1000)
assert raw_new_velocity - v0 == 1
vmax, amax = F(1, 100), F(1)
limited_velocity = min(vmax, max(-vmax, raw_new_velocity))
limited_velocity = min(v0 + amax * H, max(v0 - amax * H, limited_velocity))
assert limited_velocity == F(1, 100)
ramp_accel = (limited_velocity - v0) / H
assert ramp_accel == F(11, 20) <= amax
ramp_displacement = H * (v0 + limited_velocity) / 2
assert ramp_displacement == F(9, 100000)
# Speed alone supplies a necessary arrival-time lower bound, not sufficiency.
necessary_arrival = (delta - eps) / vmax
assert necessary_arrival == F(999, 100)
out = {
    "scope": "Exact kinematic startup and changed-target diagnostics; not physical tracking proof.",
    "H": str(H),
    "initial_samples": [str(eps)] * 3,
    "retained_velocity": str(v0),
    "prehistory": "Two intervals x=eps+v0 H(2u^3-3u^2+u); optional earlier constant-velocity extension.",
    "continuum_bounds": {
        "speed": str(abs(v0)),
        "acceleration_ae": "3/10",
        "position_deviation": str(abs(v0) * H / 4),
    },
    "same_controller_prior_interval_displacement": str(prior_controller_displacement),
    "two_step_compatible_state": [str(x) for x in X],
    "target_revision": {
        "delta": str(delta),
        "raw_new_velocity": str(raw_new_velocity),
        "naive_rate_jump": "1",
        "limited_end_velocity": str(limited_velocity),
        "ramp_acceleration": str(ramp_accel),
        "ramp_displacement": str(ramp_displacement),
        "necessary_arrival_seconds_speed_only": str(necessary_arrival),
        "warning": "Retain actual velocity separately; old 3x3 recurrence is no longer its proof.",
    },
    "rational_probes": rows,
}
(HERE / "inventor_history.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "rational_probes"}, indent=2))
