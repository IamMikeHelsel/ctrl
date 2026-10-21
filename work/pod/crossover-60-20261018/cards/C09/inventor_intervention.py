"""Exact algebraic checks for declared active-experiment and oscillator contracts."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions are required")

s = [1, -1, -1, 1]
times = list(range(4))
assert sum(s) == 0 and sum(a * b for a, b in zip(s, times, strict=True)) == 0
assert sum(a * a for a in s) == 4


def estimate(values):
    return sum(a * b for a, b in zip(s, values, strict=True)) / 4


w, d0, drift, eps = F(1, 2), F(1, 2), F(1, 10), F(1, 40)
z = [sign * w + d0 + drift * t for sign, t in zip(s, times, strict=True)]
assert estimate(z) == w
errors = [eps * sign for sign in s]
assert estimate([a + b for a, b in zip(z, errors, strict=True)]) == w + eps
assert eps > eps / 2  # no deterministic averaging gain
# Sharp quadratic-drift bias: d(t)=t²/10, |d''|=1/5, spacing1.
nuisance = [F(t * t, 10) for t in times]
assert max(nuisance) <= 2
quadratic_bias = estimate(nuisance)
assert quadratic_bias == F(1, 10) == F(1, 5) / 2
# Without a drift bound, nuisance alone imitates a unit wheel contribution.
assert estimate([F(sign) for sign in s]) == 1
assert all(abs(F(sign)) <= 2 for sign in s)

# Finite equal windows of width1/2, centers0,32,64,96. Gap31.5 permits
# a pi phase flip at relative phase-rate <=.1, since pi<22/7.
spacing, width = F(32), F(1, 2)
assert spacing - width > 10 * F(22, 7)
curvature = F(1, 1000)


def slowly_drifting_nuisance(t):
    return F(1, 2) + ((t - 48) ** 2 - 48**2 - width**2 / 12) / 2000


# Exact average of this quadratic on a centered width-W window adds W²/24000.
averages = [slowly_drifting_nuisance(spacing * k) + width**2 / 24000 for k in range(4)]
assert averages == [F(1, 2), F(-131, 250), F(-131, 250), F(1, 2)]
assert slowly_drifting_nuisance(F(48)) > -2
assert slowly_drifting_nuisance(-width / 2) < 2
assert slowly_drifting_nuisance(3 * spacing + width / 2) < 2
cycle_values = [sign * w + d for sign, d in zip(s, averages, strict=True)]
assert cycle_values[0] == 1  # original baseline retained as a window average
false_estimate = estimate(cycle_values)
assert false_estimate == F(253, 250)
assert false_estimate - w == curvature * spacing**2 / 2 == F(64, 125)
assert abs(false_estimate - 1) + eps < F(1, 8)  # naive unchanged-nuisance acceptance
assert abs(w - 1) > F(1, 8)  # actual wheel criterion fails for correction-1
assert eps + curvature * spacing**2 / 2 > F(1, 8)  # sound drift-aware rule refuses

# State y=v+a*x gives x'=y-a*x, y'=-a*y+f, constant a in[1,2].
# Boundary inequalities for rectangle |x|<=4/a², |y|<=4/a under |f|<=4.
# These symbolic cancellations hold for every positive a; rational probes check
# sign and initial-box inclusion, not the continuous invariance theorem itself.
probes = [F(1), F(5, 4), F(3, 2), F(7, 4), F(2)]
for a in probes:
    xmax, ymax = 4 / (a * a), 4 / a
    assert ymax - a * xmax == 0
    assert -a * ymax + 4 == 0
    assert xmax >= 1 and ymax >= 1
    assert xmax <= 4 and ymax + a * xmax <= 8
# After both sources truly stop at timeToff, retain the state. For s>=0:
# |x(Toff+s)| <=(4/a²+4*s/a)e^(-a*s) <=4(1+s)e^(-s).
# At s6, exponential Taylor lower bound establishes 28/e6<1/10 exactly.
e6_lower = sum(F(6**k, factorial(k)) for k in range(10))
assert e6_lower > 280
terminal_bound = 28 / e6_lower
assert terminal_bound < F(1, 10)
# The envelope's derivative is -4*s*exp(-s)<=0 for s>=0, so the tail remains safe.

# Necessary failure examples use a DIFFERENT, undamped diagnostic oscillator:
# x''+x=cos(t), rest initial; x=t sin(t)/2. At3pi/2: |x|=3pi/4>9/4.
# A complete integer-period windowT=2pi hasx(T)=0 butv(T)=pi;
# switching forcing off then gives x(T+s)=pi*sin(s), violating |x|<=1.
pi_lower, pi_upper = F(3), F(22, 7)
assert F(3, 4) * pi_lower > 1
assert pi_lower > 1
# Relative-speed authority Delta<=1/10, one-turn cancellationT=2pi/Delta,
# entails T>=20pi>60. A shorter protocol cannot use that exact null condition.
assert 20 * pi_lower == 60
out = {
    "status": "pass",
    "phase_cycling": {
        "schedule": s,
        "affine_drift_result": str(estimate(z)),
        "worst_deterministic_error": str(eps),
        "quadratic_drift_bias": str(quadratic_bias),
        "unbounded_drift_false_wheel": "1",
        "finite_window_width": str(width),
        "finite_window_spacing": str(spacing),
        "nuisance_second_derivative_bound": str(curvature),
        "finite_window_false_estimate": str(false_estimate),
        "actual_wheel": str(w),
        "drift_aware_error_bound": str(eps + curvature * spacing**2 / 2),
    },
    "oscillator": {
        "model": "x''+2a*x'+a²*x=f, constant a in[1,2], |f|<=4",
        "initial": "|x0|<=1, |v0+a*x0|<=1; retained, not reset",
        "invariant": "|x|<=4/a², |v+a*x|<=4/a",
        "support_unknown": "Only constant critically damped family; not arbitrary damping/stiffness",
        "after_actual_force_removal": "|x(Toff+s)|<=4(1+s)exp(-s)",
        "s6_rational_upper": str(terminal_bound),
        "e6_lower": str(e6_lower),
    },
    "negative_controls": [
        "Undamped resonant source violates displacement before a long window ends",
        "Zero terminal displacement does not imply zero velocity or safe ringdown",
        "Frequency authority Delta<=.1 requires T>60 for one-turn null",
        "Phase-pattern nuisance drift can imitate wheel forcing",
    ],
    "boundary": "Exact rational checks plus explicit ODE comparison and trigonometric "
    "derivations; no kernel proof, measured plant, actuator model, or hardware validation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
