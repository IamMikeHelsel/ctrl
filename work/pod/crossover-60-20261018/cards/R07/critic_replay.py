"""Independent exact interval allocator and retained-state braking checks."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
H = [
    [F(1), F(0), F(1)],
    [-F(1), F(0), F(0)],
    [F(0), F(1), F(1)],
    [F(0), -F(1), F(0)],
    [F(1), -F(1), F(0)],
]


def interval(q, v, T, U, halfspaces):
    assert T > 0 and U >= 0
    rows = [(F(1), U - v / 2), (-F(1), U + v / 2), (-F(1), U - v / 2), (F(1), U + v / 2)]
    safe = all(a * q[0] + b * q[1] <= c for a, b, c in halfspaces)
    for a, b, c in halfspaces:
        rows.append((T * (a - b), c - a * q[0] - b * q[1] - T * v * (a + b) / 2))
    lo = max(B / A for A, B in rows if A < 0)
    hi = min(B / A for A, B in rows if A > 0)
    feasible = safe and lo <= hi and all(B >= 0 for A, B in rows if A == 0)
    return lo, hi, feasible


def main():
    data = json.loads((P / "domain_allocation.json").read_text())
    for case in data["cases"]:
        q = list(map(F, case["q"]))
        v = F(case["task_rate"])
        T = F(case["horizon"])
        U = F(case["input_limit"])
        halfspaces = [list(map(F, h)) for h in case["halfspaces"]]
        assert halfspaces == H
        lo, hi, feasible = interval(q, v, T, U, halfspaces)
        assert lo == F(case["lo"]) and hi == F(case["hi"]) and feasible == case["feasible"]
        if feasible:
            n0 = F(case["nominal_null_coordinate"])
            n = min(hi, max(lo, n0))
            u = [v / 2 + n, v / 2 - n]
            assert n == F(case["selected_null_coordinate"]) and u == list(
                map(F, case["selected_velocity"])
            )
            assert all(abs(x) <= U for x in u) and sum(u) == v
            assert sum((u[i] - (v / 2 + (n0 if i == 0 else -n0))) ** 2 for i in range(2)) == F(
                case["intervention_squared"]
            )
            for h in halfspaces:
                for t in [F(0), T]:
                    assert sum(h[i] * (q[i] + t * u[i]) for i in range(2)) <= h[2]
    # Task-normal halfspace cannot be repaired by ANY null coordinate.
    normal = H + [[F(1), F(1), F(11, 10)]]
    assert not interval([F(2, 5), F(3, 5)], F(1, 5), F(1), F(1), normal)[2]
    data2 = json.loads((P / "pm_braking.json").read_text())
    for name in ["positive", "delayed", "already_nonviable"]:
        row = data2[name]
        q = list(map(F, row["q_initial"]))
        vel = list(map(F, row["v_initial"]))
        delay = F(row["delay"])
        tau = list(map(F, row["brake_torque"]))
        acc = [tau[0], tau[1] / 2]
        T = -vel[0] / acc[0]
        assert T == 2 and sum(q) == sum(vel) == sum(acc) == 0
        final = [q[i] + vel[i] * (delay + T) + acc[i] * T * T / 2 for i in range(2)]
        assert final == list(map(F, row["q_final"])) and sum(final) == 0
        assert final[0] - final[1] - F(4, 5) == F(row["final_constraint_excess"])
        assert all(abs(tau[i]) <= F(row["torque_limits"][i]) for i in range(2))
    # Delayed branch crosses obstacle before it stops; retained velocity unchanged.
    absolute = F(181, 100)
    elapsed = absolute - F(1, 100)
    q1 = F(1, 5) + F(1, 5) * absolute - F(1, 20) * elapsed**2
    assert q1 == F(2, 5) and F(1, 5) - F(1, 10) * elapsed == F(1, 50) > 0
    (P / "critic_replay.json").write_text(
        json.dumps(
            {
                "allocation_cases_verified": len(data["cases"]),
                "zero_null_coefficient_impossible_halfspace_rejected": True,
                "braking_cases_verified": 3,
                "late_brake_first_obstacle_contact": "181/100",
                "late_brake_velocity_at_contact": "1/50",
                "scope": "Exact new toy-model certificates; continuum braking monotonicity and comparison described separately. No real-arm collision or uncertainty bound.",
            },
            indent=2,
        )
        + "\n"
    )
    print("Allocation and braking certificates independently verified")


if __name__ == "__main__":
    main()
