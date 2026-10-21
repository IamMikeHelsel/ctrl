"""One concrete rational projective-boundary witness; not a full column."""

import json
from fractions import Fraction as F
from math import gcd, isqrt, lcm
from pathlib import Path

HERE = Path(__file__).parent
source = json.loads((HERE / "inventor_elliptic.json").read_text())
A = [F(4 * n) for n in source["original_Ns"]]
a2 = sum(A[:3])
a4 = A[0] * A[1] + A[0] * A[2] + A[1] * A[2]
a6 = A[0] * A[1] * A[2]
p = 197


def square_root(value):
    n, d = isqrt(value.numerator), isqrt(value.denominator)
    return F(n, d) if n * n == value.numerator and d * d == value.denominator else None


def valuation(n):
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def lift_add(P, Q):
    x, y, roots = P
    z, v, other = Q
    assert x != z or y == v != 0
    m = (3 * x * x + 2 * a2 * x + a4) / (2 * y) if (x, y) == (z, v) else (v - y) / (z - x)
    b = y - m * x
    X = m * m - a2 - x - z
    Y = -y + m * (x - X)
    assert X + x + z == m * m - a2
    assert x * z + X * x + X * z == a4 - 2 * m * b
    assert X * x * z == b * b - a6
    lifted = [(b - m * ai) / (si * sj) for ai, si, sj in zip(A[:3], roots, other, strict=True)]
    assert all(r * r == X + ai for r, ai in zip(lifted, A[:3], strict=True))
    assert Y * Y == (X + A[0]) * (X + A[1]) * (X + A[2])
    return (X, Y, lifted), {"slope": m, "intercept": b, "point": [X, Y], "roots": lifted}


known = [
    (F(row["point"][0]), F(row["point"][1]), list(map(F, row["roots"][:3])))
    for row in source["known_column_lifts"]
]
q2, step1 = lift_add(known[1], known[1])
q3, step2 = lift_add(q2, known[3])
negative_P3 = (known[2][0], -known[2][1], known[2][2])
point, step3 = lift_add(q3, negative_P3)
x, y, roots = point
D = lcm(x.denominator, y.denominator)
projective = [x.numerator * (D // x.denominator), y.numerator * (D // y.denominator), D]
g = gcd(gcd(abs(projective[0]), abs(projective[1])), projective[2])
projective = [v // g for v in projective]
reduced = [v % p for v in projective]
assert reduced[0] == reduced[2] == 0 and reduced[1] != 0
assert x.denominator % p == y.denominator % p == 0
assert all(valuation(r.denominator) == 1 for r in roots)
assert valuation(x.denominator) == 2 and valuation(y.denominator) == 3
assert (2 + 39 - 41) % 51 == 0
assert square_root(x) is None
assert square_root(x + A[3]) is None and square_root(x + A[4]) is None
# A naive affine reduction cannot invert these denominators.
try:
    pow(x.denominator, -1, p)
except ValueError:
    naive_affine_inverse_failed = True
else:
    raise AssertionError("expected noninvertible denominator")
# The exact numerator square gap rejects this point as a full column.
k = isqrt(x.numerator)
assert k * k < x.numerator < (k + 1) * (k + 1)
assert isqrt(x.denominator) ** 2 == x.denominator
result = {
    "combination": "Q=2P2+P4-P3",
    "mod197_coefficient": 0,
    "finite_over_Q": True,
    "point": [x, y],
    "first_three_roots": roots,
    "chord_steps": [step1, step2, step3],
    "primitive_projective_coordinates": projective,
    "projective_reduction": reduced,
    "normalized_projective_reduction": [0, 1, 0],
    "denominator_valuations_at197": {
        "X": valuation(x.denominator),
        "Y": valuation(y.denominator),
        "roots": [valuation(r.denominator) for r in roots],
    },
    "coordinate_bit_lengths": [
        [v.numerator.bit_length(), v.denominator.bit_length()] for v in [x, y]
    ],
    "naive_affine_inverse_failed": naive_affine_inverse_failed,
    "X_numerator_nonsquare_gap": [k * k, x.numerator, (k + 1) * (k + 1)],
    "full_column": False,
    "scope": "Actual rational point with three row-root certificates reducing to infinity. It is not a full lift: X and rows4,5 fail. Shows that affine-only handling loses valid quotient/partial-lift points, not that this point is a missed full solution.",
}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, list):
        return [encode(v) for v in value]
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    return value


(HERE / "inventor_infinity.json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(
    json.dumps(
        {
            k: encode(result[k])
            for k in [
                "combination",
                "point",
                "projective_reduction",
                "denominator_valuations_at197",
                "full_column",
            ]
        },
        indent=2,
    )
)
