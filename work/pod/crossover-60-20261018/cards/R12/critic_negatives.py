"""Semantic negative controls; declared model perturbations, not original trace failures."""

import json
from fractions import Fraction as F
from pathlib import Path

import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent
MODEL = "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie/franka_fr3/scene.xml"
m = mujoco.MjModel.from_xml_path(MODEL)
d = mujoco.MjData(m)
mujoco.mj_resetDataKeyframe(m, d, 0)
mujoco.mj_forward(m, d)
j = 1
bias = d.qfrc_bias.copy()
d.ctrl[j] = d.qpos[j] + np.sign(bias[j]) * 0.5
d.qfrc_applied[:] = bias
mujoco.mj_forward(m, d)
limit = m.jnt_actfrcrange[j, 1]
assert abs(d.actuator_force[j]) > limit
assert abs(d.qfrc_actuator[j]) == limit
assert abs(d.qfrc_actuator[j] + d.qfrc_applied[j]) > limit
clamp = {
    "changed_input": "Only joint2 command offset changed to -0.5rad at source home; not an original task or trace.",
    "raw_actuator_Nm": float(d.actuator_force[j]),
    "post_joint_clamp_Nm": float(d.qfrc_actuator[j]),
    "bias_Nm": float(bias[j]),
    "sum_Nm": float(d.qfrc_actuator[j] + bias[j]),
    "model_limit_Nm": float(limit),
}
# A different transmission invalidates direct componentwise raw-force addition.
m2 = mujoco.MjModel.from_xml_path(MODEL)
m2.actuator_gear[0, 0] = 2
e = mujoco.MjData(m2)
mujoco.mj_resetDataKeyframe(m2, e, 0)
e.ctrl[0] += 0.001
mujoco.mj_forward(m2, e)
assert abs(e.qfrc_actuator[0] - 2 * e.actuator_force[0]) < 1e-12
assert abs(e.qfrc_actuator[0] - e.actuator_force[0]) > 1
# SPD coupling alone invalidates seven independent scalar mass inverses.
M = ((F(1), F(1, 2)), (F(1, 2), F(1)))
acc = (F(4, 3), F(-2, 3))
u = (F(1), F(0))
assert all(sum(M[i][j] * acc[j] for j in range(2)) == u[i] for i in range(2))
assert acc[1] != 0


# Endpoint Jacobians cannot certify a segment Lipschitz constant: f(q)=q^3-3q.
def f(q):
    return q**3 - 3 * q


def jac(q):
    return 3 * q * q - 3


assert jac(-1) == jac(1) == 0 and abs(f(1) - f(-1)) == 4


# An unlogged between-sample bump can invalidate a claimed continuous tube.
def bump(t):
    return 16 * F(1, 1000) * t * t * (1 - t) * (1 - t)


assert bump(0) == bump(1) == 0 and bump(F(1, 2)) == F(1, 1000) > F(1, 5000)
result = {
    "changed_reference_force_bypass": clamp,
    "gear_mutation": {
        "gear": 2,
        "raw_force": float(e.actuator_force[0]),
        "generalized_force": float(e.qfrc_actuator[0]),
    },
    "coupled_SPD_example": {
        "M": [[str(x) for x in row] for row in M],
        "u": ["1", "0"],
        "acceleration": list(map(str, acc)),
    },
    "endpoint_Jacobian_counterexample": "f(q)=q^3-3q on [-1,1]: both endpoint derivatives0, displacement4. Need derivative bound over the complete segment.",
    "sampled_tube_counterexample": "Smooth quartic bump is0 at sample endpoints but1mm between them, above .2mm; no source dynamics claim.",
    "scope": "Negative controls distinguish model semantics and missing proof premises. Only first mutation uses pinned FR3 dynamics, and it changes the original reference.",
}
(HERE / "critic_negatives.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
