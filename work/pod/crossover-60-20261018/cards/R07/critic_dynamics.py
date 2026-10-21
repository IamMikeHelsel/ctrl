"""Independent exact countermodels for claims about redundancy and constraints."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def main():
    records = {}
    # Constant, positive definite inertia; no hidden Coriolis/gravity terms.
    tau = [F(1), F(-1)]
    masses = [F(1), F(2)]
    acc = [t / m for t, m in zip(tau, masses, strict=True)]
    assert sum(tau) == 0 and sum(acc) == F(1, 2)
    t = F(1, 2)
    q = [F(1, 5) + acc[0] * t * t / 2, -F(1, 5) + acc[1] * t * t / 2]
    assert sum(q) == F(1, 16)
    corrected_tau = [F(1, 2), F(-1)]
    assert sum(t / m for t, m in zip(corrected_tau, masses, strict=True)) == 0
    records["torque_kernel"] = {
        "M_diagonal": list(map(str, masses)),
        "torque": list(map(str, tau)),
        "J_tau": "0",
        "J_acceleration": "1/2",
        "task_error_at_t_half": "1/16",
        "corrected_feasible_torque": ["1/2", "-1"],
        "scope": "Exact toy constant-inertia dynamics; no actual-arm model.",
    }
    # Projection onto q1<=1 tangent halfspace after task-null projection.
    proposed = [F(1), F(-1)]
    clipped = [F(0), F(-1)]
    assert sum(proposed) == 0 and sum(clipped) == -1
    assert all(sum([a, -a]) == 0 and a <= 0 for a in [F(-1), F(-1, 2), F(0)])
    records["sequential_projection"] = {
        "state": ["1", "-1"],
        "task_null_velocity": ["1", "-1"],
        "clipped_velocity": ["0", "-1"],
        "task_derivative": "-1",
        "intersection": "v=(a,-a), a<=0; zero is feasible without posture recentering",
    }
    # Joint box is not a collision model; fiber and safe set can disconnect.
    samples = []
    for t in [F(0), F(1, 2), F(3, 4), F(1), F(3, 2), F(2)]:
        q = [1 - t, -1 + t]
        radius2 = sum(a * a for a in q)
        assert sum(q) == 0 and all(abs(a) <= 2 for a in q)
        samples.append(
            {
                "t": str(t),
                "q": list(map(str, q)),
                "configuration_radius_squared": str(radius2),
                "outside_abstract_obstacle": radius2 >= F(1, 4),
            }
        )
    assert samples[0]["outside_abstract_obstacle"] and not samples[3]["outside_abstract_obstacle"]
    records["configuration_obstacle"] = {
        "samples": samples,
        "scope": "Declared configuration-space forbidden disk, not a self-collision proof for a physical robot. Exact fiber q1+q2=0 minus disk has two components; endpoints cannot be joined within both constraints.",
    }
    # Singular task Jacobian can overestimate true finite freedom.
    q = [F(0), F(0)]
    v = [F(1), F(0)]
    t = F(1, 10)
    assert 2 * sum(a * b for a, b in zip(q, v, strict=True)) == 0
    assert sum((a + t * b) ** 2 for a, b in zip(q, v, strict=True)) == F(1, 100)
    records["singular_fiber"] = {
        "task": "q1^2+q2^2",
        "state": ["0", "0"],
        "Jacobian": [0, 0],
        "linearized_null_dimension": 2,
        "exact_zero_fiber_dimension": 0,
        "task_after_tenth": "1/100",
    }
    # Even a regular tangent fails under a straight finite step.
    q = [F(1), F(0)]
    v = [F(0), F(1)]
    t = F(1, 10)
    assert sum((a + t * b) ** 2 for a, b in zip(q, v, strict=True)) - 1 == F(1, 100)
    records["finite_step"] = {
        "task": "q1^2+q2^2",
        "initial_task": "1",
        "Jacobian_times_v": "0",
        "straight_step_task_error": "1/100",
        "needed_acceleration_at_start": ["-1", "0"],
        "reason": "Second derivative of task is2(v.v+q.a), so tangent acceleration alone fails.",
    }
    # Position-null retained velocity can already be unsafe, even with zero input.
    q = [F(9, 10), F(-9, 10)]
    v = [F(1), F(-1)]
    A = F(1)
    stop = q[0] + v[0] * v[0] / (2 * A)
    assert stop == F(7, 5) > 1
    records["retained_velocity"] = {
        "initial_task": "0",
        "task_velocity": "0",
        "q1": "9/10",
        "v1": "1",
        "maximum_braking_acceleration": "1",
        "best_stop_q1": "7/5",
        "scope": "Under the declared independent double-integrator acceleration bound, current task correctness and current joint-box membership do not imply viability.",
    }
    # Redundant displacement irrelevant to task need not be irrelevant to cost.
    d = F(1, 5)
    assert d + (-d) == 0 and d * d + (-d) * (-d) == F(2, 25)
    records["cost_scope"] = {
        "null_displacement": ["1/5", "-1/5"],
        "task_cost": "0",
        "joint_posture_cost": "2/25",
        "scope": "An extra posture/effort term changes preference on the fiber; do not infer it is physically task-irrelevant or free.",
    }
    (P / "critic_dynamics.json").write_text(json.dumps(records, indent=2) + "\n")
    print("Seven independent exact countermodel families passed")


if __name__ == "__main__":
    main()
