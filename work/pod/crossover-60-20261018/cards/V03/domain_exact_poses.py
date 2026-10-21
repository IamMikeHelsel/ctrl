"""Exact calibrated planar ambiguity with positive depths, no numeric solver."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def dot(a, b):
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def transpose(a):
    return list(map(list, zip(*a, strict=True)))


def multiply(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def mv(a, x):
    return [dot(row, x) for row in a]


def skew(t):
    x, y, z = t
    return [[F(0), -z, y], [z, F(0), -x], [-y, x, F(0)]]


def determinant(a):
    return sum(
        (
            a[0][i]
            * (a[1][(i + 1) % 3] * a[2][(i + 2) % 3] - a[1][(i + 2) % 3] * a[2][(i + 1) % 3])
            for i in range(3)
        ),
        F(0),
    )


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    identity = [[F(int(i == j)) for j in range(3)] for i in range(3)]
    ra = identity
    ta = list(map(F, [1, 0, 0]))
    rb = [[F(3, 5), F(0), F(4, 5)], [F(0), F(1), F(0)], [F(-4, 5), F(0), F(3, 5)]]
    tb = [F(1, 5), F(0), F(2, 5)]
    normal = list(map(F, [2, 0, 1]))
    h = [[F(1), F(0), F(1)], [F(0), F(1), F(0)], [F(0), F(0), F(1)]]
    assert multiply(transpose(rb), rb) == identity and determinant(rb) == 1
    assert [[rb[i][j] + tb[i] * normal[j] for j in range(3)] for i in range(3)] == h
    ea, eb = multiply(skew(ta), ra), multiply(skew(tb), rb)
    assert ea[0][1] == 0 and eb[0][1] != 0
    assert dot(ta, ta) > 0 and dot(tb, tb) > 0
    bad = multiply(skew(list(map(F, [0, 1, 0]))), h)

    def essential_cubic(matrix):
        gram = multiply(matrix, transpose(matrix))
        product = multiply(gram, matrix)
        trace = sum((gram[i][i] for i in range(3)), F(0))
        return [[2 * product[i][j] - trace * matrix[i][j] for j in range(3)] for i in range(3)]

    zero = [[F(0)] * 3 for _ in range(3)]
    assert essential_cubic(ea) == zero and essential_cubic(eb) == zero
    assert determinant(bad) == 0 and essential_cubic(bad) != zero
    points = []
    for u in [F(0), F(1, 2), F(1)]:
        for v in [F(0), F(1, 2), F(1)]:
            x = [u, v, F(1)]
            y = [u + 1, v, F(1)]
            da, db = F(1), 1 / (2 * u + 1)
            assert da > 0 and db > 0
            for rotation, translation, depth in [(ra, ta, da), (rb, tb, db)]:
                world = [depth * a for a in x]
                moved = [a + b for a, b in zip(mv(rotation, world), translation, strict=True)]
                assert moved == [depth * a for a in y]
                assert world[2] > 0 and moved[2] > 0
            assert dot(normal, [db * a for a in x]) == 1
            assert dot(y, mv(ea, x)) == 0 and dot(y, mv(eb, x)) == 0
            assert dot(y, mv(bad, x)) == 0
            points.append(
                {
                    "ray1": list(map(str, x)),
                    "ray2": list(map(str, y)),
                    "depth_pose_a_both_cameras": str(da),
                    "depth_pose_b_both_cameras": str(db),
                }
            )
    # Same exact image observations; distinct scene planes and relative rotations.
    out = {
        "evidence": "exact Fraction checks; physical validity means ideal pinhole model only",
        "rotation_a": ra,
        "translation_a": ta,
        "rotation_b": rb,
        "translation_b": tb,
        "plane_a": "Z=1",
        "plane_b": "2X+Z=1",
        "homography": h,
        "essential_a": ea,
        "essential_b": eb,
        "nonessential_projective_fit": bad,
        "nonessential_cubic_residual": essential_cubic(bad),
        "correspondences": points,
        "scale_gauge_distinguished": "rotation differs and translation directions differ",
        "scope": "unknown planar scene, calibrated normalized rays; not a known metric target",
    }
    (HERE / "domain_exact_poses_results.json").write_text(
        json.dumps(out, default=str, indent=2) + "\n"
    )
    print("PASS: 9 correspondences, 2 proper calibrated poses, positive depths in both cameras")
    print("E_A=", ea, "E_B=", eb)


if __name__ == "__main__":
    main()
