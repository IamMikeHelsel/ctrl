"""Exact rational toy fibers and path constraints; no physical arm model."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def task(q):
    return sum(x * x for x in q)


def cayley(t, side=1):
    return [side * (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)]


def velocity(t, duration, side=1):
    return [
        side * (-8 * t) / (duration * (1 + t * t) ** 2),
        4 * (1 - t * t) / (duration * (1 + t * t) ** 2),
    ]


def acceleration(t, duration, side=1):
    return [
        side * (-16 * (1 - 3 * t * t)) / (duration**2 * (1 + t * t) ** 3),
        -16 * t * (3 - t * t) / (duration**2 * (1 + t * t) ** 3),
    ]


nodes = [F(-1), F(-1, 2), F(0), F(1, 2), F(1)]
rows = []
for side in [-1, 1]:
    for t in nodes:
        q = cayley(t, side)
        v = velocity(t, F(4), side)
        a = acceleration(t, F(4), side)
        assert task(q) == 1
        assert task(v) == 16 / (F(4) ** 2 * (1 + t * t) ** 2)
        assert task(a) == 256 / (F(4) ** 4 * (1 + t * t) ** 3)
        assert sum(qi * vi for qi, vi in zip(q, v, strict=True)) == 0
        # The required acceleration has a nonzero normal component. Nullspace
        # acceleration alone cannot maintain the curved task at nonzero speed.
        assert sum(qi * ai for qi, ai in zip(q, a, strict=True)) == -task(v)
        rows.append(
            {
                "side": side,
                "t": t,
                "q": q,
                "task": task(q),
                "obstacle_q1_le_4_5": q[0] <= F(4, 5),
                "velocity_norm_squared_T4": task(v),
                "acceleration_norm_squared_T4": task(a),
            }
        )
assert cayley(F(-1), 1) == cayley(F(-1), -1) == [0, -1]
assert cayley(F(1), 1) == cayley(F(1), -1) == [0, 1]
assert cayley(F(0), 1)[0] > F(4, 5)
assert all(row["obstacle_q1_le_4_5"] for row in rows if row["side"] == -1)
assert task(velocity(F(0), F(3))) == F(16, 9) > 1

# Linearized nullspace does not describe finite fibers at a singular point.
origin, proposed_step = [F(0), F(0)], [F(1, 10), F(0)]
assert sum(2 * q * d for q, d in zip(origin, proposed_step, strict=True)) == 0
assert task(proposed_step) == F(1, 100) != task(origin)
# Even at a regular point, one Euler step in a tangent direction drifts.
q, u, dt = [F(1), F(0)], [F(0), F(1)], F(1, 10)
euler = [x + dt * v for x, v in zip(q, u, strict=True)]
assert task(euler) == F(101, 100)
# At q=(1,0),v=(0,1), q·a=0 gives f''=2, not zero. The required normal
# acceleration q·a=-1 is not a task-irrelevant correction.
assert 2 * task(u) + 2 * sum(qi * ai for qi, ai in zip(q, [0, 0], strict=True)) == 2

result = {
    "scope": "Explicit new two-coordinate toy; single-integrator path and declared ideal acceleration diagnostic",
    "task": "q1^2+q2^2=1",
    "joint_limits": "-1<=q_i<=1",
    "obstacle": "q1<=4/5",
    "kinematic_actuator": "||qdot||2<=1",
    "safe_route": "left semicircle; t=2s/T-1,0<=s<=T,T=4",
    "all_time_reason": "|t|<=1 givesleftq1<=0; speed^2=16/[T^2(1+t^2)^2]<=16/T^2",
    "right_route_endpoint_only_failure": True,
    "deadline_T3_fails_this_timing": F(16, 9),
    "endpoint_velocities_T4_left": [velocity(F(-1), F(4), -1), velocity(F(1), F(4), -1)],
    "rest_endpoint_warning": "T4 affineCayley has nonzero endpointvelocities; not rest-to-rest",
    "singular_linearized_step_task": task(proposed_step),
    "regular_Euler_task": task(euler),
    "rows": rows,
    "disconnected_safe_fiber": {
        "changed_obstacle": "|q2|<=3/5",
        "safe_endpoints": [[1, 0], [-1, 0]],
        "obstruction": "Any continuousconnectingpath crossesq1=0; taskthenforces|q2|=1>3/5",
        "task_semantics": "Taskf1alone neverrequiresconnectingthesepostures; holdingcurrentoneisvalid",
    },
}
rho, speed = F(1, 100), F(1, 5)
required_normal_acceleration = -speed * speed / rho
assert required_normal_acceleration == -4
assert -(F(1, 10) ** 2) / rho == -1
result["curvature_actuation_budget"] = {
    "changed_task_level": rho * rho,
    "q": [rho, 0],
    "v": [0, speed],
    "required_a1": required_normal_acceleration,
    "norm_limit": 1,
    "feasible": False,
    "boundary_speed_1_10_required_a1": -1,
    "principle": "Forqdot=v,qddot=a andconstant||q||2: qdotv=0,qdot a=-||v||2",
    "scope": "Ideal doubleintegrator diagnostic; no torque/inertia/friction model",
}
(HERE / "inventor_geometry.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(json.dumps(result, default=str, indent=2))
