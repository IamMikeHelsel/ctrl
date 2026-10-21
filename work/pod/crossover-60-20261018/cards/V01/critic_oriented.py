"""Read inventor exact receipt, independently recompute camera and frame relations."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
j = json.loads((P / "inventor_oriented.json").read_text())


def v(a):
    return [F(x) for x in a]


def m(a):
    return [v(r) for r in a]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(a, x):
    return [dot(r, x) for r in a]


def tr(a):
    return list(map(list, zip(*a, strict=True)))


def mm(a, b):
    return [[dot(r, c) for c in tr(b)] for r in a]


def add(a, b):
    return [x + y for x, y in zip(a, b, strict=True)]


def norm(a):
    return [x / a[2] for x in a]


I = [[F(i == k) for k in range(3)] for i in range(3)]
a = j["orientation"]
R = m(a["R"])
x = v(a["X"])
y = mv(R, x)
assert mm(tr(R), R) == I and y == v(a["RX"]) and y[2] < 0 and norm(y) == x
r = m(j["horizon_rotation"])
assert mm(tr(r), r) == I
for row in j["horizon_rows"]:
    y = mv(r, v(row["source"]))
    assert y == v(row["target_ray"])
    assert (y[2] > 0) == row["target_positive_depth"]
    if y[2]:
        assert norm(y) == v(row["standard_chart"])
p = j["passive_frame"]
q1, q2 = m(p["Q1"]), m(p["Q2"])
H = m(p["H"])
Hp = m(p["H_prime"])
assert mm(mm(q2, H), tr(q1)) == Hp
assert mv(q1, v(p["X"])) == v(p["X_prime"])
assert mv(q2, v(p["Y"])) == v(p["Y_prime"])
assert mv(Hp, v(p["X_prime"])) == v(p["Y_prime"])
assert dot(v(p["transported_optical_axis"]), v(p["X_prime"])) == F(p["physical_depth_unchanged"])
assert v(p["X_prime"])[2] < 0
# One changed-frame coordinate is not a physical rotation of the camera; the axis must move too.
assert mv(q1, v(p["n"])) == v(p["n_prime"])
assert dot(v(p["n_prime"]), v(p["X_prime"])) == F(p["d"])
wrong = add(mv(m(p["R_prime"]), v(p["X_prime"])), v(p["t_prime"]))
assert wrong == v(p["Y_prime"])
d = j["dual_transport"]
assert dot(v(d["correct_line"]), v(d["image_point"])) == 0
assert dot(v(d["wrong_point_rule_line"]), v(d["image_point"])) == 1
out = {
    "orientation_negative": True,
    "horizon_rows_checked": len(j["horizon_rows"]),
    "passive_frame_and_optical_axis": True,
    "dual_line_mutation": True,
    "scope": "Exact independent finite fixture reconstruction; no general differentiable or noisy-camera theorem.",
}
(P / "critic_oriented.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
