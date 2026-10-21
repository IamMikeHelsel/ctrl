"""Exact negative controls for generic width, timing and history shortcuts."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def derivative(events, t, k):
    return sum(
        (
            delta * c * max(t - tau - i * h, F(0)) ** (4 - k) / F(factorial(4 - k)) / h**4
            for tau, delta, h in events
            for i, c in enumerate([1, -4, 6, -4, 1])
        ),
        F(0),
    )


def jerk_peak(events):
    knots = {tau + i * h for tau, _, h in events for i in range(5)}
    return max(abs(derivative(events, t, 3)) for t in knots)


old = (F(11, 50), F(1, 50), F(1, 5))
# Distinct causal event times; wider new event can weaken useful cancellation.
short = [old, (F(23, 100), -F(1, 50), F(1, 5))]
wide = [old, (F(23, 100), -F(1, 50), F(2, 5))]
assert jerk_peak(wide) > jerk_peak(short)
# Incorrect global rescaling changes reference already executed before revision .52.
mutated_old = (old[0], old[1], F(1, 4))
t = F(1, 2)
old_prefix = [derivative([old], t, k) for k in range(4)]
mutated_prefix = [derivative([mutated_old], t, k) for k in range(4)]
assert old_prefix[:3] != mutated_prefix[:3]
# Completed-tail deadline test is sufficient, not necessary for tolerances.
return_h30 = [old, (F(13, 25), -F(1, 50), F(3, 10))]
deadline = F(17, 10)
state = [derivative(return_h30, deadline, k) for k in range(4)]
assert F(13, 25) + 4 * F(3, 10) > deadline
assert abs(state[0]) < F(1, 5000) and abs(state[1]) < F(1, 1000) and abs(state[2]) < F(1, 50)
# This is only a reference endpoint check: the physical task still needs its bridge.
result = {
    "nonmonotone_superposed_jerk": {
        "same_width_peak": str(jerk_peak(short)),
        "wider_new_event_peak": str(jerk_peak(wide)),
        "scope": "Distinct-time cancellation fixture, not the frozen .52s reversal case.",
    },
    "global_rescaling_violates_old_prefix": {
        "time": str(t),
        "old_q_v_a_j": list(map(str, old_prefix)),
        "rescaled_old_q_v_a_j": list(map(str, mutated_prefix)),
    },
    "tail_gate_not_necessary": {
        "new_width": "3/10",
        "deadline": str(deadline),
        "tail": "43/25",
        "reference_state_at_deadline": list(map(str, state)),
        "reference_tolerances_pass": True,
        "physical_task_verified": False,
    },
    "scope": "Exact reference-only falsifiers. No inference of physical endpoint acceptance, future extrema after deadline, or native planner superiority.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
