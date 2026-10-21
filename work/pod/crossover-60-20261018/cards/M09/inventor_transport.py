"""Exact 2x2 diagnostic: full-field transport, connection terms, and fixed volume."""

import json
from fractions import Fraction as F
from pathlib import Path


def mat(rows):
    return [[F(x) for x in row] for row in rows]


def add(a, b):
    return [[x + y for x, y in zip(u, v, strict=True)] for u, v in zip(a, b, strict=True)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in zip(*b, strict=True)]
        for row in a
    ]


def tr(a):
    return list(map(list, zip(*a, strict=True)))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def quadratic(p, h):
    return mul(mul(tr(p), h), p)[0][0]


I, K, W = mat([[1, 0], [0, 1]]), mat([[1, 0], [0, -1]]), mat([[0, 1], [-1, 0]])
assert mul(W, W) == scale(-1, I)
assert mul(tr(W), K) == mul(K, W)
a, b = F(5, 4), F(3, 4)
t, q = 2 * a * b, a * a + b * b
S = add(scale(a, I), scale(b, W))
Si = scale(1 / q, add(scale(a, I), scale(-b, W)))
H = mul(K, add(I, scale(t, W)))
assert mul(S, Si) == I and mul(mul(tr(S), K), S) == H
assert H != K
# The chosen gamma has + K-adjoint. This is a diagnostic, not the source Clifford-bar convention.
gamma = K
gamma_new = mul(mul(Si, gamma), S)
assert mul(gamma_new, gamma_new) == I
assert mul(tr(gamma_new), H) == mul(H, gamma_new)
assert mul(tr(gamma), H) != mul(H, gamma)
psi = mat([[2], [1]])
psi_new = mul(Si, psi)
assert quadratic(psi_new, H) == quadratic(psi, K) == 3
assert quadratic(psi_new, mul(H, gamma_new)) == quadratic(psi, mul(K, gamma)) == 5
naive_value = quadratic(psi_new, mul(H, gamma))
assert naive_value == F(40, 17) != 5
# Sign sufficiency in this toy: K itself is K-unitary and reverses W.
assert mul(mul(tr(K), K), K) == K
assert mul(mul(tr(K), H), K) == mul(K, add(I, scale(-t, W)))
# Moving z-coordinate: a=(1+z²)/(1-z²), b=2z/(1-z²), evaluated at z=1/3.
z = F(1, 3)
assert a == (1 + z * z) / (1 - z * z) and b == 2 * z / (1 - z * z)
ap, bp = 4 * z / (1 - z * z) ** 2, 2 * (1 + z * z) / (1 - z * z) ** 2
Sp = add(scale(ap, I), scale(bp, W))
A = mul(Si, Sp)
assert A == add(scale(F(135, 68), I), scale(F(18, 17), W))
Hp = add(mul(mul(tr(Sp), K), S), mul(mul(tr(S), K), Sp))
assert Hp == add(mul(tr(A), H), mul(H, A))
assert add(mul(tr(A), K), mul(K, A)) != scale(0, I)
# For a constant old field, new-field derivative plus connection term cancels exactly.
e1 = mat([[1], [0]])
field_new = mul(Si, e1)
field_derivative = scale(-1, mul(mul(mul(Si, Sp), Si), e1))
assert field_derivative != mat([[0], [0]])
assert add(field_derivative, mul(A, field_new)) == mat([[0], [0]])
# Independent symplectic/volume convention, not asserted to be GU's extra structure.
assert mul(mul(tr(S), W), S) == scale(q, W)
assert det(S) == q == F(17, 8) != 1
assert det(H) == -(1 + t * t) != det(K)
result = {
    "K": K,
    "W": W,
    "a": a,
    "b": b,
    "t": t,
    "S": S,
    "S_inverse": Si,
    "H": H,
    "old_gamma": gamma,
    "new_gamma": gamma_new,
    "old_field": psi,
    "new_field": psi_new,
    "transported_quadratic": 3,
    "transported_observable": 5,
    "frozen_observable_value": naive_value,
    "moving_coordinate": z,
    "S_derivative": Sp,
    "induced_connection": A,
    "H_derivative": Hp,
    "new_constant_field_derivative": field_derivative,
    "fixed_K_metric_defect": add(mul(tr(A), K), mul(K, A)),
    "symplectic_multiplier": q,
    "H_determinant": det(H),
    "limits": [
        "2x2 real diagnostic embedded in complex matrices, not actual 128-spinor representation.",
        "Gamma uses positive K-adjoint, not asserted source Clifford-bar convention.",
        "Symplectic restriction is an additional diagnostic convention, not identified GU structure.",
        "S is not K-unitary; induced A is not fixed-K anti-adjoint. Passive transport is not an allowed fixed-K gauge action.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    {
        "t": str(t),
        "transported_observable": 5,
        "frozen_observable": str(naive_value),
        "connection_I": "135/68",
        "connection_W": "18/17",
        "symplectic_multiplier": str(q),
    }
)
