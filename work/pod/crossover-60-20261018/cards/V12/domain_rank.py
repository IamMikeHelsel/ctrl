"""Exact pinhole calibration fixtures and independently replayable row certificates."""

import json
from fractions import Fraction as F
from pathlib import Path


def mat(rows):
    return [[F(v) for v in row] for row in rows]


def mul(A, B):
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in zip(*B, strict=True)]
        for row in A
    ]


def det3(A):
    return sum(
        A[0][j] * (A[1][(j + 1) % 3] * A[2][(j + 2) % 3] - A[1][(j + 2) % 3] * A[2][(j + 1) % 3])
        for j in range(3)
    )


def transpose(A):
    return list(map(list, zip(*A, strict=True)))


def rref(A):
    A = [row[:] for row in A]
    m, n = len(A), len(A[0])
    U = [[F(i == j) for j in range(m)] for i in range(m)]
    piv = []
    r = 0
    for c in range(n):
        q = next((i for i in range(r, m) if A[i][c]), None)
        if q is None:
            continue
        A[r], A[q] = A[q], A[r]
        U[r], U[q] = U[q], U[r]
        d = A[r][c]
        A[r] = [v / d for v in A[r]]
        U[r] = [v / d for v in U[r]]
        for i in range(m):
            if i != r:
                d = A[i][c]
                A[i] = [v - d * w for v, w in zip(A[i], A[r], strict=True)]
                U[i] = [v - d * w for v, w in zip(U[i], U[r], strict=True)]
        piv.append(c)
        r += 1
        if r == m:
            break
    return A, U, piv


def vij(a, b):
    return [
        a[0] * b[0],
        a[0] * b[1] + a[1] * b[0],
        a[1] * b[1],
        a[2] * b[0] + a[0] * b[2],
        a[2] * b[1] + a[1] * b[2],
        a[2] * b[2],
    ]


def constraints(H):
    a, b = transpose(H)[:2]
    return [vij(a, b), [x - y for x, y in zip(vij(a, a), vij(b, b), strict=True)]]


K = mat([[2, F(1, 2), 1], [0, 3, -1], [0, 0, 1]])
Ki = mat([[F(1, 2), F(-1, 12), F(-7, 12)], [0, F(1, 3), F(1, 3)], [0, 0, 1]])
assert mul(K, Ki) == mat([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
B = mul(transpose(Ki), Ki)
b = [4 * B[i][j] for i, j in [(0, 0), (0, 1), (1, 1), (0, 2), (1, 2), (2, 2)]]
I = mat([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
Rx = mat([[1, 0, 0], [0, F(3, 5), F(-4, 5)], [0, F(4, 5), F(3, 5)]])
Ry = mat([[F(5, 13), 0, F(12, 13)], [0, 1, 0], [F(-12, 13), 0, F(5, 13)]])
Rz = mat([[F(3, 5), F(-4, 5), 0], [F(4, 5), F(3, 5), 0], [0, 0, 1]])
rows = []
for label, Rs in [
    ("frontoparallel", [I, Rz, mul(Rz, Rz)]),
    ("two_tilts", [Rx, Ry]),
    ("three_views", [I, Rx, Ry]),
]:
    Hs = []
    for j, R in enumerate(Rs):
        assert mul(transpose(R), R) == I
        assert det3(R) == 1
        t = [F(j, 4), F(-j, 3), F(4 + j)]
        H = mul(K, [[R[i][0], R[i][1], t[i]] for i in range(3)])
        # Board square [-1,1]^2 stays in front of the camera.
        assert all(R[2][0] * x + R[2][1] * y + t[2] > 0 for x in [-1, 1] for y in [-1, 1])
        assert det3(H) != 0
        Hs.append(H)
    A = [row for H in Hs for row in constraints(H)]
    rr, U, piv = rref(A)
    assert mul(U, A) == rr
    identity, Uinv, upiv = rref(U)
    assert identity == [[F(i == j) for j in range(len(U))] for i in range(len(U))]
    assert mul(Uinv, U) == identity == mul(U, Uinv)
    assert all(sum(x * y for x, y in zip(row, b, strict=True)) == 0 for row in A)
    rank = len(piv)
    assert rank == {"frontoparallel": 2, "two_tilts": 4, "three_views": 5}[label]
    rows.append(
        {
            "label": label,
            "H": Hs,
            "A": A,
            "rref": rr,
            "row_certificate": U,
            "row_certificate_inverse": Uinv,
            "rank": rank,
            "pivots": piv,
        }
    )
result = {
    "K": K,
    "K_inverse": Ki,
    "B": B,
    "normalized_b_B11_1": b,
    "cases": rows,
    "coordinate_order": ["B11", "B12", "B22", "B13", "B23", "B33"],
    "scope": "Exact undistorted pinhole metric-plane homographies; no image/noise calibration guarantee.",
}
path = Path(__file__)
path.with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print({"b": list(map(str, b)), "ranks": [(r["label"], r["rank"]) for r in rows]})
# Frozen concrete linear uniqueness proof, over arbitrary reals.
A = rows[-1]["A"]
variables = ["b11", "b12", "b22", "b13", "b23", "b33"]


def term(q, v):
    return f"({q.numerator}/{q.denominator}:ℝ)*{v}"


lines = [
    "import Mathlib.Tactic",
    "namespace V12Domain",
    "theorem concrete_unique (" + " ".join(variables) + " : ℝ)",
]
for j, row in enumerate(A):
    lines.append(
        f"    (h{j} : "
        + " + ".join(term(q, v) for q, v in zip(row, variables, strict=True))
        + " = 0)"
    )
lines += [
    "    (hg : b11=1) : "
    + " ∧ ".join(
        f"{v}=({q.numerator}/{q.denominator}:ℝ)" for v, q in zip(variables, b, strict=True)
    )
    + " := by",
    "  refine ⟨by simpa using hg, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith",
    "end V12Domain",
    "#print axioms V12Domain.concrete_unique",
]
path.with_name("domain_rank.lean").write_text("\n".join(lines) + "\n")
