"""Exact declared two-joint constant-inertia model; no hardware claims."""

import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
A, V = Q(1, 10), Q(1, 5)


def stopped_position(q, delay):
    return q + V * delay + V * V / (2 * A)


def fixture(q, delay):
    final = stopped_position(q, delay)
    # q2=-q1 throughout; inertia diag(1,2), torque=(-.1,+.2).
    return {
        "q_initial": [str(q), str(-q)],
        "v_initial": [str(V), str(-V)],
        "delay": str(delay),
        "brake_torque": ["-1/10", "1/5"],
        "mass_matrix": [["1", "0"], ["0", "2"]],
        "stop_time": str(delay + V / A),
        "q_final": [str(final), str(-final)],
        "task_sum": "0",
        "configuration_obstacle": "q1-q2 <= 4/5",
        "final_constraint_excess": str(2 * final - Q(4, 5)),
        "joint_box": "[-1,1]^2",
        "torque_limits": ["1/10", "1/5"],
    }


if __name__ == "__main__":
    positive = fixture(Q(1, 5), Q(0))
    delayed = fixture(Q(1, 5), Q(1, 100))
    too_late = fixture(Q(3, 10), Q(0))
    assert Q(positive["final_constraint_excess"]) == 0
    assert Q(delayed["final_constraint_excess"]) == Q(1, 250)
    assert Q(too_late["final_constraint_excess"]) == Q(1, 5)
    # On 0<=t<=2: q1=q0+t/5-t²/20, derivative=(2-t)/10>=0.
    # Exact endpoint extrema apply to this monotone polynomial, not arbitrary paths.
    result = {
        "model": "q''=diag(1,1/2)*torque; no gravity, friction, Coriolis, delay except declared hold; normalized joint coordinates; task q1+q2=0 and configuration halfspace is an explicit obstacle surrogate, not an inferred Cartesian collision certificate.",
        "positive": positive,
        "delayed": delayed,
        "already_nonviable": too_late,
        "all_time_positive": "Brake immediately for2s, then torque0; q1 rises monotonically .2→.4 and q2=-q1. Task remains0, configuration bound and joint/torque limits hold. No return to q=(0,0) is required.",
        "necessity_bridge": "For any acceleration a1>=-.1 and initialv1=.2, q1(2)>=q1(0)+.2 by double integration. Thus q1(0)=.3 cannot remain in task0 and q1-q2<=.8 through2s. Differential comparison/integration not kernel-checked in this script.",
        "no_intervention_at_rest": "Any q=(r,-r), |r|<=.4, v0, torque0 stays task-satisfied and inside the declared halfspace/jointbox. Full joint regulation would unnecessarily change this declared task-equivalent state.",
    }
    (HERE / "pm_braking.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
