"""Rows valid on columns {C1, C2, 0} via pairings of linear factors.

C = c * l1 l2 l3 l4 (linear forms, possibly constant = root at infinity).  Pairing k gives
C = c P_k Q_k.  A quadratic a is a row for C (a^2 + C square) iff a = xP + yQ with xy = -c/4.
For pairings k (of C1) and k' (of C2): line L = span(P1,Q1) cap span(P2,Q2) spanned by
a_L = x1 P1 + y1 Q1 = x2 P2 + y2 Q2; a row exists iff rho = x1 y1 / (x2 y2) = c1/c2, and it is
rational iff -c1 / (4 x1 y1) is a rational square.
Linear forms are pairs (alpha, beta) meaning alpha*x + beta.
"""
from fractions import Fraction as F
from itertools import combinations

PAIRINGS = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def mul(l, m):
    """(a x + b)(c x + d) -> coefficient vector [x^2, x, 1]."""
    return (l[0] * m[0], l[0] * m[1] + l[1] * m[0], l[1] * m[1])


def det3(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def planes(L):
    return [(mul(L[i], L[j]), mul(L[k], L[l])) for (i, j), (k, l) in PAIRINGS]


def line_coeffs(P1, Q1, P2, Q2):
    """Solve x1 P1 + y1 Q1 - x2 P2 - y2 Q2 = 0 (3 eqs, 4 unknowns) via 3x3 minors (Cramer)."""
    cols = [P1, Q1, tuple(-v for v in P2), tuple(-v for v in Q2)]
    # kernel vector components: (-1)^i det(cols without i)
    k = []
    for i in range(4):
        rest = [cols[j] for j in range(4) if j != i]
        # columns -> need det of 3x3 matrix with these as columns
        M = [[rest[c][r] for c in range(3)] for r in range(3)]
        d = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
             + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
        k.append((-1) ** i * d)
    return k  # x1, y1, x2, y2


def ratios(L1, L2):
    """dict (k,k') -> rho (Fraction) or None if degenerate."""
    out = {}
    for k, (P1, Q1) in enumerate(planes(L1)):
        for kk, (P2, Q2) in enumerate(planes(L2)):
            x1, y1, x2, y2 = line_coeffs(P1, Q1, P2, Q2)
            if x1 * y1 == 0 or x2 * y2 == 0:
                out[(k, kk)] = None
                continue
            out[(k, kk)] = (F(x1 * y1, x2 * y2), (x1, y1, x2, y2))
    return out


def rows_for(L1, c1, L2, c2):
    """explicit rows (coefficient triples of a, possibly over sqrt) for given constants."""
    res = []
    for (k, kk), v in ratios(L1, L2).items():
        if v is None:
            continue
        rho, (x1, y1, x2, y2) = v
        if rho == F(c1) / F(c2):
            lam2 = F(-c1) / (4 * x1 * y1)
            P1, Q1 = planes(L1)[k]
            aL = tuple(x1 * P1[i] + y1 * Q1[i] for i in range(3))
            res.append(((k, kk), lam2, aL))
    return res
