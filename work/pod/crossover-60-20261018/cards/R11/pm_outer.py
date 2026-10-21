"""Exact finite recurrences for a declared sampled outer visual loop."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
H = F(1, 50)
INITIAL = F(1, 1000)
V_MAX = F(1, 10)


def energy(x, y, k):
    return x * x - x * y + k * y * y


def delayed(k, count):
    y = x = INITIAL
    initial_energy = energy(x, y, k)
    rows = []
    first_authority = None
    for n in range(count):
        v = -(k / H) * y
        if abs(v) > V_MAX and first_authority is None:
            first_authority = n
        assert energy(x, y, k) == k**n * initial_energy
        rows.append(
            {
                "n": n,
                "time": str(n * H),
                "error": str(x),
                "speed_command": str(v),
                "energy": str(energy(x, y, k)),
            }
        )
        y, x = x, x - k * y
    return rows, first_authority


unstable, first_bad = delayed(F(6, 5), 100)
stable, stable_bad = delayed(F(1, 2), 100)
assert first_bad is not None and stable_bad is None
assert abs(F(unstable[0]["speed_command"])) <= V_MAX
# A command beyond the admitted bound means the physical linear toy cannot simply
# be extrapolated as a certified plant if the actual device clips or changes law.
assert all(abs(F(r["speed_command"])) <= V_MAX for r in unstable[:first_bad])
assert abs(F(unstable[first_bad]["speed_command"])) > V_MAX
assert all(abs(F(r["speed_command"])) <= F(1, 40) for r in stable)
# Zero-age law has exactly the opposite verdict at the same dimensionless gain.
undelayed = [INITIAL * (1 - F(6, 5)) ** n for n in range(100)]
assert all(undelayed[n + 1] ** 2 == undelayed[n] ** 2 / 25 for n in range(99))
# If a consumer resets the retained delayed sample to zero at every update,
# it silently stops applying the declared delayed feedback and hides growth.
reset_history = INITIAL
for _ in range(100):
    reset_history = reset_history - F(6, 5) * 0
assert reset_history == INITIAL
# State perturbation is not reset away: each homogeneous recurrence energy scales.
for x, y in [(F(a, 10000), F(b, 10000)) for a in range(-3, 4) for b in range(-3, 4)]:
    k = F(1, 2)
    assert energy(x - k * y, x, k) == k * energy(x, y, k)
    assert F(1, 8) * (x * x + y * y) <= energy(x, y, k) <= F(3, 2) * (x * x + y * y)

out = {
    "model": "Matched first-order inner servo, current base/derivative, continuous rdot=v_k held forH, initial innererror0. Then exact outerrecurrence; finiteacceleration notmodeled.",
    "H": str(H),
    "initial_error": str(INITIAL),
    "speed_contract": str(V_MAX),
    "unstable_gain": "6/5",
    "stable_gain": "1/2",
    "unstable_first_speed_violation": unstable[first_bad],
    "unstable_prefix_steps_within_speed": first_bad,
    "stable_speed_100steps_max": str(max(abs(F(r["speed_command"])) for r in stable)),
    "stable_energy_100step_ratio": str(F(1, 2) ** 100),
    "perturbed_state_checks": 49,
    "undelayed_gain_6_5_square_ratio": "1/25",
    "reset_history_false_model": "error remains1/1000 instead of declared delayed recurrence",
    "unstable_trace": unstable,
    "stable_trace": stable,
    "scope": "Exact recurrence. ODE sampled-flow composition handderived; authorityviolations delimit validity. No arbitrary delay/actuator/motion/physical guarantee.",
}
(HERE / "pm_outer.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if not k.endswith("_trace")}))
