"""Independent consumer for rigid poses, local Jacobians and fixed-candidate error bounds."""

import copy
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
helpers = runpy.run_path(str(BASE / "critic_geometry.py"), run_name="critic_library")
rank = helpers["rank"]
mm = helpers["mm"]
mv = helpers["mv"]
dot = helpers["dot"]
transpose = helpers["transpose"]
det = helpers["det"]
skew = helpers["skew"]
I = [[F(i == j) for j in range(3)] for i in range(3)]
DATA = json.loads((BASE / "inventor_exact.json").read_text())


def cross(a, b):
    return [a[(i + 1) % 3] * b[(i + 2) % 3] - a[(i + 2) % 3] * b[(i + 1) % 3] for i in range(3)]


def matrix(a):
    return [list(map(F, row)) for row in a]


def verify(data):
    count = 0
    for pose, key in enumerate(["pose_A", "pose_B"]):
        R = matrix(data[key]["R"])
        t = list(map(F, data[key]["t"]))
        if mm(transpose(R), R) != I or det(R) != 1 or not any(t):
            raise ValueError("rigid pose")
        E = mm(skew(t), R)
        if E != matrix(data["essential_matrices"][pose]):
            raise ValueError("essential binding")
        full = []
        for entry in data["scene"]:
            x = list(map(F, entry["x1"]))
            y = list(map(F, entry["x2"]))
            depth = F(entry["depths_in_both_cameras"][pose])
            if depth <= 0 or [
                a + b for a, b in zip(mv(R, [depth * z for z in x]), t, strict=True)
            ] != [depth * z for z in y]:
                raise ValueError("cheirality reconstruction")
            rx = mv(R, x)
            row = [dot(y, cross(axis, rx)) for axis in I]
            row += [dot(y, cross(t, cross(axis, rx))) for axis in I]
            full.append(row)
            count += 1
        stored = data["jacobians"][pose]
        chart = [[r[3], r[4], r[5], r[1], r[2]] for r in full]
        if full != matrix(stored["full_six_matrix"]) or chart != matrix(stored["matrix"]):
            raise ValueError("differential binding")
        if rank(full) != 5 or rank(chart) != 5 or any(dot(row, t + [F(0)] * 3) for row in full):
            raise ValueError("rank or scale kernel")
    E = matrix(data["essential_matrices"][1])
    for test in data["noise_margin_tests"]:
        Z = F(test["Z"])
        eps = F(test["epsilon_each_coordinate"])
        x = [F(0), F(1, 3), F(1)]
        y = [1 / Z, F(1, 3), F(1)]
        residual = dot(y, mv(E, x))
        linear = sum(abs(z) for z in mv(E, x)[:2]) + sum(abs(z) for z in mv(transpose(E), y)[:2])
        quadratic = sum(abs(E[i][j]) for i in range(2) for j in range(2))
        bound = linear * eps + quadratic * eps**2
        if residual != F(test["candidate_B_residual"]) or bound != F(test["bilinear_error_bound"]):
            raise ValueError("bounded error expansion")
        if (abs(residual) > bound) != test["certified_reject"]:
            raise ValueError("rejection decision")
        if (abs(1 - y[0]) <= eps) != test["can_round_to_exact_planar_correspondence"]:
            raise ValueError("nearplane compatibility")
    return count


count = verify(DATA)
negatives = []
for kind in ["rotation", "depth", "jacobian", "error_bound"]:
    bad = copy.deepcopy(DATA)
    if kind == "rotation":
        bad["pose_B"]["R"][2][0] = "4/5"
    elif kind == "depth":
        bad["scene"][0]["depths_in_both_cameras"][1] = "-10"
    elif kind == "jacobian":
        bad["jacobians"][0]["full_six_matrix"][0][0] = "1"
    else:
        bad["noise_margin_tests"][0]["bilinear_error_bound"] = "0"
    try:
        verify(bad)
    except ValueError as error:
        negatives.append(dict(mutation=kind, rejection=str(error)))
    else:
        raise ValueError("bad fixture accepted")
result = dict(
    positive_depth_reconstructions_checked=count,
    rank_at_both_poses=5,
    negative_controls=negatives,
    scope="Exact rational differential/bounded-coordinate calculations; local rank is not global uniqueness; rejection applies to fixed E_B only, not every alternate pose or perturbed-pose region.",
)
(BASE / "critic_replay_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
