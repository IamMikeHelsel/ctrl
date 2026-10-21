"""Exact rational global certificate for a weighted inconsistent SO(2) cycle."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def rotation(c, s):
    return [[F(c), -F(s)], [F(s), F(c)]]


def transpose(a):
    return [list(row) for row in zip(*a, strict=True)]


def multiply(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def difference(a, b):
    return [[x - y for x, y in zip(ar, br, strict=True)] for ar, br in zip(a, b, strict=True)]


def norm2(a):
    return sum(x * x for row in a for x in row)


I = rotation(1, 0)
minus_I = rotation(-1, 0)


def proper(r):
    return multiply(transpose(r), r) == I and r[0][0] * r[1][1] - r[0][1] * r[1][0] == 1


def objective(edges, poses):
    return sum(w * norm2(difference(poses[j], multiply(poses[i], m))) for i, j, w, m in edges)


def data_matrix(edges):
    result = [[F(0) for _ in range(6)] for _ in range(6)]
    for i, j, w, m in edges:
        assert w > 0 and proper(m)
        for a in range(2):
            result[2 * i + a][2 * i + a] += w
            result[2 * j + a][2 * j + a] += w
            for b in range(2):
                result[2 * i + a][2 * j + b] -= w * m[a][b]
                result[2 * j + b][2 * i + a] -= w * m[a][b]
    return result


def verify(edges, poses, lambdas, factor):
    if poses[0] != I or not all(proper(r) for r in poses):
        return False, "gauge or SO(2) membership"
    slack = data_matrix(edges)
    for i, value in enumerate(lambdas):
        for a in range(2):
            slack[2 * i + a][2 * i + a] -= value
    if slack != multiply(transpose(factor), factor):
        return False, "slack factor does not bind graph/weights/directions"
    lower = 2 * sum(lambdas)
    if objective(edges, poses) != lower:
        return False, "primal-dual gap"
    return True, str(lower)


poses = [I, rotation(F(-3, 5), F(4, 5)), rotation(F(-4, 5), F(-3, 5))]
edges = [(0, 1, F(15), minus_I), (1, 2, F(12), minus_I), (0, 2, F(20), minus_I)]
amplitudes = [F(5), F(3), F(4)]
lambdas = [F(10), F(18), F(16)]
factor = [[amplitudes[j // 2] * I[i][j % 2] for j in range(6)] for i in range(2)]
assert verify(edges, poses, lambdas, factor) == (True, "88")
mirror = [transpose(r) for r in poses]
assert mirror != poses and verify(edges, mirror, lambdas, factor)[0]
assert multiply(multiply(minus_I, minus_I), transpose(minus_I)) == minus_I

# Same cycle holonomy, different confidence weight: the former optimum is not
# even stationary. A rational half-angle perturbation improves its cost.
changed = [(i, j, F(13) if (i, j) == (1, 2) else w, m) for i, j, w, m in edges]
t = F(-1, 100)
perturbation = rotation((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
better = [poses[0], multiply(poses[1], perturbation), poses[2]]
assert objective(changed, poses) == 92
assert objective(changed, poses) - objective(changed, better) == F(728, 10001)
assert not verify(changed, poses, lambdas, factor)[0]

# A local-frame change preserves the objective but creates non-self-transpose
# edge rotations, making a wrong edge reversal detectable.
frames = [I, rotation(F(5, 13), F(12, 13)), rotation(F(3, 5), F(4, 5))]
framed_poses = [multiply(r, q) for r, q in zip(poses, frames, strict=True)]
framed_edges = [
    (i, j, w, multiply(multiply(transpose(frames[i]), m), frames[j])) for i, j, w, m in edges
]
framed_factor = [
    [amplitudes[j // 2] * frames[j // 2][i][j % 2] for j in range(6)] for i in range(2)
]
assert verify(framed_edges, framed_poses, lambdas, framed_factor)[0]
reversed_edges = [(j, i, w, transpose(m)) for i, j, w, m in framed_edges]
assert verify(reversed_edges, framed_poses, lambdas, framed_factor)[0]
wrong_reverse = [(j, i, w, m) for i, j, w, m in framed_edges]
assert not verify(wrong_reverse, framed_poses, lambdas, framed_factor)[0]

reflection = [[F(1), F(0)], [F(0), F(-1)]]
wrong_orientation = [I, multiply(poses[1], reflection), poses[2]]
assert not verify(edges, wrong_orientation, lambdas, factor)[0]
identity_poses = [I, I, I]
assert objective(edges, identity_poses) == 376
assert not verify(edges, identity_poses, lambdas, factor)[0]

result = {
    "scope": "Exact rational certificate for SO(2) rotation-only pose graph, no translations",
    "objective": "sum directed edges once w_ij ||R_j-R_i M_ij||_F^2",
    "edges": edges,
    "candidate": poses,
    "other_gauge_fixed_optimum": mirror,
    "dual_lambdas": lambdas,
    "slack_factor": factor,
    "optimum": 88,
    "holonomy": minus_I,
    "weight_mutation": {
        "candidate_cost": 92,
        "better_cost": objective(changed, better),
        "strict_improvement": F(728, 10001),
        "rejection": verify(changed, poses, lambdas, factor),
    },
    "frame_change": {
        "edges": framed_edges,
        "poses": framed_poses,
        "factor": framed_factor,
        "correct_reverse": verify(reversed_edges, framed_poses, lambdas, framed_factor),
        "wrong_reverse": verify(wrong_reverse, framed_poses, lambdas, framed_factor),
        "wrong_reverse_candidate_cost": objective(wrong_reverse, framed_poses),
    },
    "reflection_rejection": verify(edges, wrong_orientation, lambdas, factor),
    "stationary_identity_cost": 376,
    "stationary_identity_rejection": verify(edges, identity_poses, lambdas, factor),
}
(HERE / "inventor_cycle.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(json.dumps(result, default=str, indent=2))
