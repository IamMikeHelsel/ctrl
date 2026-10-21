"""Exact coordinate-type mutations: points, directions, planes and camera origins."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
# A passive translation changes point and camera-center coordinates together.
X = [F(1), F(0), F(1)]
C = [F(0)] * 3
b = [F(1), F(0), F(0)]
Xp = [x + z for x, z in zip(X, b, strict=True)]
Cp = [c + z for c, z in zip(C, b, strict=True)]
ray = [x - c for x, c in zip(X, C, strict=True)]
rayp = [x - c for x, c in zip(Xp, Cp, strict=True)]
assert ray == rayp
naive = [Xp[i] / Xp[2] for i in range(2)]
correct = [rayp[i] / rayp[2] for i in range(2)]
assert naive == [F(2), F(0)] and correct == [F(1), F(0)]
# A plane normal and offset must share scale, including negative gauge.
n = [F(0), F(0), F(1)]
d = F(2)
XX = [F(2), F(1), F(2)]
for beta in [F(-3), F(2, 5), F(7)]:
    np = [beta * z for z in n]
    dp = beta * d
    assert sum(a * x for a, x in zip(np, XX, strict=True)) == dp
    assert [z / dp for z in np] == [z / d for z in n]
# Counterexample: scale n alone, and the old scene point is no longer on that plane.
assert sum(3 * a * x for a, x in zip(n, XX, strict=True)) != d
out = {
    "passive_translation": {
        "point_before": X,
        "point_after": Xp,
        "center_after": Cp,
        "proper_ray": rayp,
        "naive_pixel": naive,
        "correct_pixel": correct,
    },
    "joint_plane_scales_tested": ["-3", "2/5", "7"],
    "scope": "Coordinate-type counterexamples. An affine translation acts on points and camera centers, not directly on ray directions; source plane formula remains a camera-coordinate formula.",
}
(P / "pm_frame_types.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps(out, default=str))
