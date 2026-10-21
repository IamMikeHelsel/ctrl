"""Exact Q(sqrt(3)) candidate and rational PSD/negative certificates; no solver."""

import json
from fractions import Fraction as F
from pathlib import Path


class Q3:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, other):
        o = other if isinstance(other, Q3) else Q3(other)
        return Q3(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        o = other if isinstance(other, Q3) else Q3(other)
        return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __eq__(self, other):
        o = other if isinstance(other, Q3) else Q3(other)
        return self.a == o.a and self.b == o.b

    def out(self):
        return [str(self.a), str(self.b)]


def rot(c, s):
    return [[c, -s], [s, c]]


def add(A, B):
    return [[x + y for x, y in zip(a, b, strict=True)] for a, b in zip(A, B, strict=True)]


def scale(c, A):
    return [[c * x for x in row] for row in A]


def transpose(A):
    return [list(x) for x in zip(*A, strict=True)]


def mm(A, B):
    return [[sum(x * y for x, y in zip(a, b, strict=True)) for b in transpose(B)] for a in A]


def frob(A):
    return sum(x * x for row in A for x in row)


I = [[Q3(1), Q3()], [Q3(), Q3(1)]]
R1 = rot(Q3(F(1, 2)), Q3(0, F(1, 2)))
R2 = rot(Q3(F(-1, 2)), Q3(0, F(1, 2)))
for R in [I, R1, R2]:
    assert mm(transpose(R), R) == I
    assert R[0][0] * R[1][1] - R[0][1] * R[1][0] == 1
costs = [frob(add(R1, scale(-1, I))), frob(add(R2, scale(-1, R1))), frob(add(R2, I))]
assert costs == [Q3(2)] * 3
assert add(add(I, scale(-1, R1)), R2) == [[Q3(), Q3()], [Q3(), Q3()]]
# Scalar connection Laplacian and rank-one dual PSD factor.
L = [[2, -1, 1], [-1, 2, -1], [1, -1, 2]]
b = [1, -1, 1]
S = [[L[i][j] - (1 if i == j else 0) for j in range(3)] for i in range(3)]
assert S == [[x * y for y in b] for x in b]
# Both signs of sqrt3 give the same rational dual certificate and objective.
R1minus = rot(Q3(F(1, 2)), Q3(0, F(-1, 2)))
R2minus = rot(Q3(F(-1, 2)), Q3(0, F(-1, 2)))
assert R1minus != R1
assert (
    frob(add(R1minus, scale(-1, I)))
    + frob(add(R2minus, scale(-1, R1minus)))
    + frob(add(R2minus, I))
    == 6
)
# All-identity point: first-order multiplier condition holds but PSD fails.
lam_bad = [2, 0, 2]
Sbad = [[L[i][j] - (lam_bad[i] if i == j else 0) for j in range(3)] for i in range(3)]
assert all(sum(row) == 0 for row in Sbad)
v = [1, 0, -1]
negative = sum(v[i] * Sbad[i][j] * v[j] for i in range(3) for j in range(3))
assert negative == -2
result = {
    "graph": {
        "nodes": [0, 1, 2],
        "edges": [[0, 1, "I", 1], [1, 2, "I", 1], [0, 2, "-I", 1]],
        "gauge": "R0=I",
    },
    "coefficient_field": "[a,b] denotes a+b*sqrt(3)",
    "candidate_rotations": [[[x.out() for x in row] for row in R] for R in [I, R1, R2]],
    "edge_Frobenius_squared_costs": [x.out() for x in costs],
    "objective": 6,
    "connection_Laplacian_scalar": L,
    "dual_multipliers_scalar": [1, 1, 1],
    "dual_slack_scalar": S,
    "PSD_factor_b": b,
    "full_real_slack": "S tensor I2, rank2 and nullity4; block-diagonal multiplier I2 at eachnode",
    "negative_stationary_candidate": {
        "rotations": "allI",
        "objective": 8,
        "multipliers_scalar": lam_bad,
        "slack": Sbad,
        "direction": v,
        "quadratic_form": negative,
    },
    "scope": "Connected inconsistent SO2 triangle; exact tight certificate and two distinct gauge-fixed optima. No general relaxation-tightness or physical-truth claim.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(
    "Exact SO2 candidate objective6, rationalPSD factor, conjugate secondoptimum, stationaryPSDfailure checked."
)
