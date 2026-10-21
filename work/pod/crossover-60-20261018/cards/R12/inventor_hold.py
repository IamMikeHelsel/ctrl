"""Exact retained-history and queued-event derivative boundary audit."""

import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path


def kernel(t, derivative):
    h = F(1, 5)
    if t <= 0:
        return F(0)
    if t >= 4 * h:
        return F(int(derivative == 0))
    return sum((-1) ** k * comb(4, k) * max(t - k * h, 0) ** (4 - derivative) for k in range(5)) / (
        factorial(4 - derivative) * h**4
    )


def main():
    issue, arrival, execute = F(11, 20), F(61, 100), F(67, 100)
    rows = []
    for time in (issue, arrival, execute):
        old = tuple(F(1, 25) * kernel(time - F(11, 50), d) for d in range(4))
        added = tuple(F(-3, 50) * kernel(time - execute, d) for d in range(4))
        assert added == (0, 0, 0, 0)
        assert old[1] > 0
        rows.append({"time_s": time, "retained_old_q_v_a_j": old, "new_event_q_v_a_j": added})
    # Resetting the old event to a constant at arrival destroys its nonzero velocity.
    old_arrival_velocity = rows[1]["retained_old_q_v_a_j"][1]
    assert old_arrival_velocity != 0
    # Four derivatives of a newly started term: first four entries0 at commit;
    # fourth derivative (snap) has a nonzero right jump delta/h^4.
    right_snap_jump = F(-3, 50) / F(1, 5) ** 4
    assert right_snap_jump == F(-75, 2)
    result = {
        "queued_revision": rows,
        "reset_to_constant_negative_velocity_jump_rad_s": -old_arrival_velocity,
        "new_event_snap_right_jump_rad_s4": right_snap_jump,
        "causality": "New term and derivatives0..3 vanish through execution. Receipt does not change active reference; prior tails remain. Current analytic derivatives require only received history, not future packets or plant derivatives.",
        "source_boundary": "Source supplies derivatives0..3. Snap need not be continuous at commit. This rational audit does not execute the original floating implementation.",
    }
    output = json.dumps(result, default=str, indent=2)
    Path(__file__).with_suffix(".json").write_text(output + "\n")
    print(output)


if __name__ == "__main__":
    main()
