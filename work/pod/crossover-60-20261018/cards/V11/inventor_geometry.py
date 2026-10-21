"""Exact bounded-outlier geometric admission and additive-information candidates."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).parent
ROWS = [(F(1), F(0)), (F(0), F(1)), (F(1), F(1)), (F(1), F(2))]
Z = [F(1), F(0), F(0), F(0)]
EPS = F(1, 100)
PRIOR = [(F(1), F(0), F(1)), (-F(1), F(0), F(1)), (F(0), F(1), F(1)), (F(0), -F(1), F(1))]


def solve2(row1, row2):
    a, b, u = row1
    c, d, v = row2
    det = a * d - b * c
    return None if det == 0 else ((u * d - b * v) / det, (a * v - u * c) / det)


def branch(selected, epsilon=EPS):
    inequalities = list(PRIOR)
    for i in selected:
        a, b = ROWS[i]
        inequalities.extend([(a, b, Z[i] + epsilon), (-a, -b, -Z[i] + epsilon)])
    vertices = set()
    for p, q in itertools.combinations(inequalities, 2):
        x = solve2(p, q)
        if x is not None and all(a * x[0] + b * x[1] <= d for a, b, d in inequalities):
            vertices.add(x)
    return sorted(vertices)


def information(selected, weights):
    A, D = F(1), F(1)
    B, p, q = F(0), F(0), F(0)
    for i in selected:
        a, b = ROWS[i]
        w = weights[i]
        A += w * a * a
        B += w * a * b
        D += w * b * b
        p += w * a * Z[i]
        q += w * b * Z[i]
    det = A * D - B * B
    assert A > 0 and det > 0
    mean = ((D * p - B * q) / det, (A * q - B * p) / det)
    covariance = ((D / det, -B / det), (-B / det, A / det))
    assert A * covariance[0][0] + B * covariance[1][0] == 1
    assert A * covariance[0][1] + B * covariance[1][1] == 0
    assert B * covariance[0][0] + D * covariance[1][0] == 0
    assert B * covariance[0][1] + D * covariance[1][1] == 1
    return {"mean": mean, "information": ((A, B), (B, D)), "covariance": covariance}


def worst_error(candidate, vertices):
    return max(max(abs(x[i] - candidate[i]) for i in range(2)) for x in vertices)


cases = []
for n in [3, 4]:
    branches = [
        {"assumed_inliers": indices, "vertices": branch(indices)}
        for indices in itertools.combinations(range(n), n - 1)
    ]
    feasible = [b for b in branches if b["vertices"]]
    points = set(v for b in feasible for v in b["vertices"])
    assert feasible
    assert any(
        all(abs(ROWS[i][0] * 0 + ROWS[i][1] * 0 - Z[i]) <= EPS for i in b["assumed_inliers"])
        for b in feasible
    )
    candidate = information(range(n), [F(10000), F(1), F(1), F(1)])
    certified = set.intersection(*(set(b["assumed_inliers"]) for b in feasible))
    admitted = information(sorted(certified), [F(10000)] * 4)
    bounds = {
        "all_data_candidate": worst_error(candidate["mean"], points),
        "certified_inlier_candidate": worst_error(admitted["mean"], points),
    }
    worst_world = max(points, key=lambda x: max(abs(x[i] - candidate["mean"][i]) for i in range(2)))
    assert (
        sum(
            abs(a * worst_world[0] + b * worst_world[1] - z) > EPS
            for (a, b), z in zip(ROWS[:n], Z[:n], strict=True)
        )
        <= 1
    )
    cases.append(
        {
            "n": n,
            "fault_budget": 1,
            "branches": branches,
            "feasible_branch_count": len(feasible),
            "certified_inlier_rows": sorted(certified),
            "all_data_information_candidate": candidate,
            "certified_inlier_information_candidate": admitted,
            "actual_error_true_zero": max(map(abs, candidate["mean"])),
            "joint_set_worst_error_bounds": bounds,
            "admissible_worst_world": worst_world,
        }
    )
assert cases[0]["feasible_branch_count"] == 3
assert cases[0]["certified_inlier_rows"] == []
assert cases[1]["feasible_branch_count"] == 1
assert cases[1]["certified_inlier_rows"] == [1, 2, 3]
assert cases[1]["joint_set_worst_error_bounds"]["certified_inlier_candidate"] == F(1, 50)
assert cases[1]["joint_set_worst_error_bounds"]["all_data_candidate"] > 1
# Exact geometric redundancy check: every pair of distinct rows is independent.
assert all(a * d - b * c != 0 for (a, b), (c, d) in itertools.combinations(ROWS, 2))
# Therefore a nonzero delta can annihilate at most one of four rows.
# Three-row ambiguity at epsilon0, explicit worlds and one fault in each.
worlds = [(F(0), F(0)), (F(1), F(0)), (F(1), -F(1))]
assert all(
    sum(a * x + b * y != z for (a, b), z in zip(ROWS[:3], Z[:3], strict=True)) <= 1
    for x, y in worlds
)
threshold_checks = []
for epsilon in [F(1, 100), F(1, 5), F(249, 1000), F(1, 4), F(3, 10), F(1, 3)]:
    feasible = [
        indices for indices in itertools.combinations(range(4), 3) if branch(indices, epsilon)
    ]
    threshold_checks.append({"epsilon": epsilon, "feasible_inlier_subsets": feasible})
    if epsilon < F(1, 4):
        assert feasible == [(1, 2, 3)]
    else:
        assert len(feasible) > 1
result = {
    "measurement_rows": ROWS,
    "observations": Z,
    "noise_bound": EPS,
    "prior_box": "[-1,1]^2",
    "cases": cases,
    "three_row_noiseless_ambiguous_worlds": worlds,
    "admission_threshold_checks": threshold_checks,
    "scope": "Declared linear geometric localization model, deterministic bounded inlier noise, at most one faulty original observation, and true state in prior box. Exact rational polygon vertices and information inverses. No probability model, kernel certificate, nonlinear camera claim, or truth guarantee without these assumptions.",
}


def encode(v):
    if isinstance(v, F):
        return str(v)
    if isinstance(v, (tuple, list)):
        return [encode(x) for x in v]
    if isinstance(v, dict):
        return {k: encode(x) for k, x in v.items()}
    return v


(HERE / "inventor_geometry.json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(
    json.dumps(
        encode(
            [
                {
                    "n": r["n"],
                    "feasible_branches": r["feasible_branch_count"],
                    "certain_inliers": r["certified_inlier_rows"],
                    "bounds": r["joint_set_worst_error_bounds"],
                    "actual_error": r["actual_error_true_zero"],
                }
                for r in cases
            ]
        ),
        indent=2,
    )
)
