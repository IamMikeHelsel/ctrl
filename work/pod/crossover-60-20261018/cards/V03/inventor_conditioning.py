"""Fixed-gauge local-rank minors and vanishing-parallax family; exact arithmetic."""

import json
from fractions import Fraction as F
from itertools import permutations
from math import prod
from pathlib import Path

from inventor_exact import I, add, det, dot, encode, mul, mv, skew, transpose


def determinant(a):
    a = [list(map(F, row)) for row in a]
    out = F(1)
    for col in range(len(a)):
        pivot = next((j for j in range(col, len(a)) if a[j][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            out = -out
        diagonal = a[col][col]
        out *= diagonal
        a[col] = [x / diagonal for x in a[col]]
        for j in range(col + 1, len(a)):
            factor = a[j][col]
            a[j] = [x - factor * y for x, y in zip(a[j], a[col], strict=True)]
    return out


def determinant_leibniz(a):
    total = F(0)
    for permutation in permutations(range(len(a))):
        inversions = sum(
            permutation[i] > permutation[j] for i in range(len(a)) for j in range(i + 1, len(a))
        )
        total += (-1) ** inversions * prod(
            (a[i][permutation[i]] for i in range(len(a))), start=F(1)
        )
    return total


points = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(1), F(1)), (F(0), F(2))]
tA = [F(1), F(0), F(0)]
rows = []
for beta in [F(1), F(1, 2), F(1, 10), F(1, 100)]:
    denom = 4 + beta * beta
    c, s = (4 - beta * beta) / denom, 4 * beta / denom
    RB = [[c, F(0), s], [F(0), F(1), F(0)], [-s, F(0), c]]
    tB = [beta, F(0), F(2)]
    mB = [2 * beta / denom, F(0), beta * beta / denom]
    H = [[F(1), F(0), beta], [F(0), F(1), F(0)], [F(0), F(0), F(1)]]
    assert mul(transpose(RB), RB) == I and det(RB) == 1
    assert add(RB, [[a * b for b in mB] for a in tB]) == H
    matrices = []
    depth_records = []
    for ri, ti in [(I, tA), (RB, tB)]:
        dEs = [mul(skew(axis), ri) for axis in I[1:]]
        dEs += [mul(mul(skew(ti), skew(axis)), ri) for axis in I]
        matrix = []
        for u, v in points:
            x, y = [u, v, F(1)], [u + beta, v, F(1)]
            matrix.append([dot(y, mv(de, x)) for de in dEs])
            depth = 1 / beta if ri == I else 1 / dot(mB, x)
            assert depth > 0
            assert [depth * z for z in y] == [
                a + b for a, b in zip(mv(ri, [depth * z for z in x]), ti, strict=True)
            ]
            depth_records.append(depth)
        matrices.append(matrix)
    expected = [[beta, -beta * v, -(v * v + 1), u * v, u] for u, v in points]
    assert matrices[0] == expected
    detA, detB = map(determinant, matrices)
    assert [detA, detB] == list(map(determinant_leibniz, matrices))
    assert detA == 2 * beta * beta
    assert detB != 0
    translation_column_sq = sum(row[0] ** 2 for row in matrices[0])
    rotation_column_sq = sum(row[2] ** 2 for row in matrices[0])
    assert translation_column_sq == 5 * beta * beta
    assert rotation_column_sq == 35
    rows.append(
        {
            "beta": beta,
            "plane_depth_A": 1 / beta,
            "R_B": RB,
            "t_B": tB,
            "inverse_plane_B": mB,
            "jacobian_A": matrices[0],
            "jacobian_B": matrices[1],
            "det_A": detA,
            "det_B": detB,
            "all_reconstruction_depths_positive": True,
            "sigma_min_squared_upper_bound_A": translation_column_sq,
            "sigma_max_squared_lower_bound_A": rotation_column_sq,
            "condition_number_squared_lower_bound_A": 7 / (beta * beta),
        }
    )

branch_checks = []
for a in map(F, range(-2, 3)):
    for c in map(F, range(-4, 5)):
        fm = [[F(0), -c, F(0)], [c, F(0), c - a], [F(0), a, F(0)]]
        gram = mul(fm, transpose(fm))
        assert gram == [[c * c, 0, -a * c], [0, c * c + (c - a) ** 2, 0], [-a * c, 0, a * a]]
        first, second = c * c + a * a, c * c + (c - a) ** 2
        assert first - second == c * (2 * a - c)
        nonzero_equal = first > 0 and first == second
        assert nonzero_equal == (a != 0 and (c == 0 or c == 2 * a))
        if nonzero_equal:
            branch_checks.append({"a": a, "c": c, "branch": "EA" if c == 0 else "EB"})

interpolation_points = [
    (F(0), F(0)),
    (F(1, 4), F(0)),
    (F(1, 2), F(0)),
    (F(0), F(-1, 3)),
    (F(0), F(1, 3)),
    (F(1, 4), F(1, 3)),
]
interpolation = [[u * u, u * v, v * v, u, v, F(1)] for u, v in interpolation_points]
interpolation_det = determinant(interpolation)
assert interpolation_det != 0
assert interpolation_det == determinant_leibniz(interpolation) == F(1, 5184)
for i in range(3):
    for j in range(3):
        fm = [[F(int((a, b) == (i, j))) for b in range(3)] for a in range(3)]
        coefficients = [
            fm[0][0],
            fm[0][1] + fm[1][0],
            fm[1][1],
            fm[0][0] + fm[0][2] + fm[2][0],
            fm[0][1] + fm[1][2] + fm[2][1],
            fm[0][2] + fm[2][2],
        ]
        for (u, v), monomials in zip(interpolation_points, interpolation, strict=True):
            assert dot([u + 1, v, F(1)], mv(fm, [u, v, F(1)])) == dot(coefficients, monomials)

result = {
    "columns": ["ty", "tz", "omega_x", "omega_y", "omega_z"],
    "five_first_image_points": [list(p) for p in points],
    "algorithm_crosscheck": "All eight5x5 minors and the6x6 interpolation determinant agree between rational Gaussian elimination and direct permutation-sum determinants. Same agent, independent algorithms; not independent human or kernel verification.",
    "family": rows,
    "critical_nonzero_essential_class_checks": branch_checks,
    "planar_polynomial_certificate": {
        "six_points": [list(p) for p in interpolation_points],
        "monomial_columns": ["u^2", "uv", "v^2", "u", "v", "1"],
        "evaluation_matrix": interpolation,
        "determinant": interpolation_det,
        "coefficient_map": ["f00", "f01+f10", "f11", "f00+f02+f20", "f01+f12+f21", "f02+f22"],
        "consequence": "Any F satisfying these six planar correspondences has all six polynomial coefficients zero, hence F=[(a,b,c)]cross H with a=f21,b=f02,c=-f01. This is a finite exact interpolation certificate for matrix-family completeness.",
    },
    "branch_derivation": "For b=0, F=[e]H has Gram eigenvalues0,a^2+c^2,c^2+(c-a)^2. Equality of the nonzero values is c(2a-c)=0. Excluding(a,c)=(0,0), the only projective essential classes are EA(c=0) and EB(c=2a), both already realized by explicitSO(3)poses. This classifies matrices for this exact fixture, not their complete pose decompositions.",
    "gauge": "PoseA has fixed unittranslatione1; translation-direction tangent and rotation-angle coordinates are fixed. Rays have lastcoordinate1. Global E rescaling does not alter the condition-number ratio, but arbitrary state/row reweighting changes conditioning semantics.",
    "interpretation": "Rank5 at every tested nonzerobeta and symbolic determinant2beta^2; sigma_min^2<=5beta^2 and sigma_max^2>=35 imply no uniform lower observability margin in this chart. Beta->0 takes finite nonzero translation with scene depth->infinity; it is not itself a finite zero-baseline scene.",
    "scope": "Exact small-matrix certificates and rational cheiral family, no complete global enumeration, kernel proof or hardware result.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(
    json.dumps(
        encode(
            [
                {
                    key: row[key]
                    for key in ["beta", "det_A", "det_B", "condition_number_squared_lower_bound_A"]
                }
                for row in rows
            ]
        ),
        indent=2,
    )
)
