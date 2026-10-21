"""Exact source four-box FIR diagnostics; no physical-state reset or robot simulation."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

WIDTH = F(1, 5)
OLD = ((F(11, 50), F(1, 50)),)
RETURN = (F(31, 50), F(-1, 50))
COEFFICIENTS = (1, -4, 6, -4, 1)


def kernel(order, z):
    n = 4 - order
    return sum(c * max(z - k, 0) ** n for k, c in enumerate(COEFFICIENTS)) / factorial(n)


def jet(t, history=OLD):
    return tuple(
        sum(delta * kernel(k, (t - stamp) / WIDTH) / WIDTH**k for stamp, delta in history)
        for k in range(4)
    )


def bias_clock(t):
    a, c, b = F(101, 200), F(103, 200), F(105, 200)
    if t <= a or t >= b:
        return t
    if t <= c:
        return F(3, 2) * t - a / 2
    return t / 2 + b / 2


# A naïve clock-label check permits a return event to arrive after its actual start.
estimated_commit, estimated_execution = F(123, 200), F(5, 8)
actual_commit, actual_execution = F(31, 50), F(31, 50)
epsilon, dispatch = F(1, 200), F(1, 100)
assert abs(estimated_commit - actual_commit) <= epsilon
assert abs(estimated_execution - actual_execution) <= epsilon
assert estimated_commit + dispatch <= estimated_execution
assert not estimated_commit + epsilon + dispatch <= estimated_execution - epsilon
arrival = actual_commit + dispatch
assert arrival == F(63, 100) > actual_execution
old_at_arrival, proposed_at_arrival = jet(arrival), jet(arrival, OLD + (RETURN,))
late_jumps = tuple(b - a for a, b in zip(old_at_arrival, proposed_at_arrival, strict=True))
assert late_jumps == (F(-1, 192000000), F(-1, 480000), F(-1, 1600), F(-1, 8))
retimed = jet(arrival, OLD + ((arrival, RETURN[1]),))
assert retimed == old_at_arrival  # All four reference components match at event age zero.
assert jet(F(7, 10), OLD + ((arrival, RETURN[1]),)) != jet(F(7, 10), OLD + (RETURN,))
assert arrival + 4 * WIDTH == F(143, 100) < F(17, 10)

# Bounded clock error + strict monotonicity still does not preserve reference C1 continuity.
a, center, b = F(101, 200), F(103, 200), F(105, 200)
assert bias_clock(a) == a and bias_clock(b) == b
assert bias_clock(center) == F(13, 25)
assert bias_clock(center) - center == epsilon
nominal = jet(bias_clock(center))
assert nominal[1] == F(23, 480)
left = tuple(nominal[k] * F(3, 2) ** k for k in range(4))
right = tuple(nominal[k] * F(1, 2) ** k for k in range(4))
assert left[0] == right[0]
assert left[1] == F(23, 320) and right[1] == F(23, 960)
assert right[1] - left[1] == F(-23, 480)
for k in range(41):
    t = a + (b - a) * F(k, 40)
    assert 0 <= bias_clock(t) - t <= epsilon
    assert 1 < (bias_clock(t) - OLD[0][0]) / WIDTH < 2

# Shift the same correction after the saved on-time commit.57/dispatch.01.
# Event installation at.58 is timely; clock-as-phase evaluation still breaks the reference.
post_center = center+F(1, 10)
post_phase = bias_clock(post_center-F(1, 10))+F(1, 10)
assert post_phase == RETURN[0]
post_nominal = jet(post_phase, OLD+(RETURN,))
assert post_nominal[1] == F(1, 15)
post_left_v, post_right_v = post_nominal[1]*F(3, 2), post_nominal[1]/2
assert post_right_v-post_left_v == F(-1, 15)
probe = post_center-F(1, 1000)
probe_phase = bias_clock(probe-F(1, 10))+F(1, 10)
probe_jerk = jet(probe_phase, OLD+(RETURN,))[3]*F(3, 2)**3
assert F(57, 100)+F(1, 100) < post_center-F(1, 100)
assert abs(probe_jerk) > F(15, 2)

# A common unknown offset can cancel from ordering; independent-error inflation is conservative.
clock_gap, rho, dispatch_bound = F(1, 20), F(1, 1000), F(1, 100)
minimum_physical_gap = clock_gap / (1 + rho)
assert minimum_physical_gap > dispatch_bound
assert clock_gap < 2 * F(1, 10) + dispatch_bound
for alpha in [1 - rho, 1 + rho]:
    for beta in [F(-9, 100), F(9, 100)]:
        tc, te = F(1, 2), F(1, 2) + clock_gap / alpha
        assert 0 <= tc < te <= 1
        cc, ce = alpha * tc + beta, alpha * te + beta
        assert ce - cc == clock_gap
        assert abs(cc - tc) <= F(1, 10) and abs(ce - te) <= F(1, 10)

result = {
    "source": "bundle-v4 Kernel.lean F0..F3 and Reference.lean response/jet",
    "history": OLD,
    "width": WIDTH,
    "return_event": RETURN,
    "late_install": {
        "estimated_commit": estimated_commit,
        "estimated_execution": estimated_execution,
        "actual_commit": actual_commit,
        "actual_execution": actual_execution,
        "clock_error_bound": epsilon,
        "dispatch": dispatch,
        "arrival": arrival,
        "naive_order_accepts": True,
        "robust_order_accepts": False,
        "reference_jet_jump": late_jumps,
        "retimed_final_settling": arrival + 4 * WIDTH,
        "original_deadline": F(17, 10),
        "retiming_claim": "Different event history requires revalidation; no deadline miss claimed.",
    },
    "clock_as_phase": {
        "physical_knots": [a, center, b],
        "local_clock_slopes": [1, F(3, 2), F(1, 2), 1],
        "uniform_clock_bias_bound": epsilon,
        "phase_at_center": bias_clock(center),
        "source_jet_at_phase": nominal,
        "left_polynomial_jet": left,
        "right_polynomial_jet": right,
        "velocity_jump": right[1] - left[1],
        "reference_position_difference_from_ideal_clock": nominal[0] - jet(center)[0],
        "scope": "q(C(t)) loses C1; physical robot state is neither simulated nor reset.",
    },
    "shared_affine_clock": {
        "observed_gap": clock_gap,
        "relative_rate_error_bound": rho,
        "minimum_physical_gap": minimum_physical_gap,
        "dispatch_bound": dispatch_bound,
        "offset": "arbitrary common constant cancels; this is an extra clock model",
        "truthful_independent_bound_fixture": "beta in[-.09,.09], physical horizon[0,1], errors<=.1",
    },
    "post_commit_timewarp": {
        "saved_commit": F(57, 100), "dispatch": F(1, 100),
        "installation": F(58, 100), "clock_correction_start": F(121, 200),
        "physical_center": post_center, "phase_at_center": post_phase,
        "nominal_velocity": post_nominal[1], "left_velocity": post_left_v,
        "right_velocity": post_right_v, "velocity_jump": post_right_v-post_left_v,
        "physical_probe_time": probe, "probe_phase": probe_phase,
        "physical_time_reference_jerk": probe_jerk, "source_jerk_limit": F(15, 2),
        "scope": "Timely installation does not repair a later clock-as-phase correction.",
    },
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print("PASS: retained FIR late-install jump, retiming change, bounded monotone-clock C1 failure")
