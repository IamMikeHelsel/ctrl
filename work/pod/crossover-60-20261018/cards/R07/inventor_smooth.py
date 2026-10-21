"""Declared exact ideal-double-integrator path, not a physical arm result."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
T = F(12)


def phase(z):
    return 2 * (10 * z**3 - 15 * z**4 + 6 * z**5) - 1


def phase_velocity(z):
    return 60 * z**2 * (1 - z) ** 2 / T


def phase_acceleration(z):
    return 120 * z * (1 - z) * (1 - 2 * z) / T**2


def evaluate(z):
    t, td, tdd = phase(z), phase_velocity(z), phase_acceleration(z)
    den = 1 + t * t
    q = [-(1 - t * t) / den, 2 * t / den]
    qt = [4 * t / den**2, 2 * (1 - t * t) / den**2]
    qtt = [4 * (1 - 3 * t * t) / den**3, -4 * t * (3 - t * t) / den**3]
    v = [x * td for x in qt]
    a = [x * td * td + y * tdd for x, y in zip(qtt, qt, strict=True)]
    assert sum(x * x for x in q) == 1
    assert q[0] <= 0 and all(abs(x) <= 1 for x in q)
    assert sum(x * y for x, y in zip(q, v, strict=True)) == 0
    assert sum(x * y for x, y in zip(q, a, strict=True)) == -sum(x * x for x in v)
    assert sum(x * x for x in v) <= F(5, 8) ** 2
    assert sum(x * x for x in a) <= F(155, 192) ** 2
    return {"z": z, "phase": t, "q": q, "v": v, "a": a}


rows = [evaluate(F(k, 20)) for k in range(21)]
assert rows[0]["q"] == [0, -1] and rows[-1]["q"] == [0, 1]
assert rows[0]["v"] == rows[-1]["v"] == [0, 0]
assert rows[0]["a"] == rows[-1]["a"] == [0, 0]
assert F(15, 2) / T == F(5, 8)
assert F(465, 4) / T**2 == F(155, 192) < 1
# The path has no margin against arbitrary position-error balls at q1=-1.
eps = F(1, 1000)
perturbed = [-1 - eps, F(0)]
assert perturbed[0] < -1
assert sum(x * x for x in perturbed) - 1 == 2 * eps + eps * eps

result = {
    "contract": {
        "model": "qdot=v,vdot=u exact ideal doubleintegrator",
        "duration": T,
        "task": "||q||2^2=1",
        "obstacle": "q1<=4/5",
        "joints": "q_i in[-1,1]",
        "velocity_norm_limit": 1,
        "acceleration_norm_limit": 1,
        "initial": "q=(0,-1),v=0,u=0",
        "final": "q=(0,1),v=0,u=0",
    },
    "all_time_bounds": {
        "phase_velocity": F(15, 4) / T,
        "phase_acceleration": 30 / T**2,
        "velocity_norm": F(5, 8),
        "acceleration_norm": F(155, 192),
    },
    "proof_outline": "phase derivative nonnegative givesphase in[-1,1]; z(1-z)<=1/4;"
    " |1-2z|<=1; ||q_t||<=2,||q_tt||<=4; chainrule+triangleinequality",
    "rational_nodes_are_checks_not_alltime_proof": rows,
    "robust_tracking_negative": {
        "error_norm": eps,
        "actual": perturbed,
        "violated_joint_lower": -1,
        "task_error": 2 * eps + eps * eps,
    },
    "limits": "No uncertainty, inertia, torque, gravity, friction, collisiongeometry or hardware model",
}
outside_phase = phase(F(2))
outside_left_x = -(1 - outside_phase**2) / (1 + outside_phase**2)
assert outside_phase == 63
assert outside_left_x == F(1984, 1985) > F(4, 5)
result["unbounded_phase_clock_negative"] = {
    "z": 2,
    "phase": outside_phase,
    "q1": outside_left_x,
    "obstacle_violated": True,
    "interpretation": "Do not extend quintic beyond certified0<=s<=T;"
    " postdeadline hold requires a declared constant tail, matching endpointv/a0",
}
(HERE / "inventor_smooth.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    json.dumps(
        {
            "velocity_bound": "5/8",
            "acceleration_bound": "155/192",
            "node_checks": len(rows),
            "robust_tracking_negative": True,
        },
        indent=2,
    )
)
