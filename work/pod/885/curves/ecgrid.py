"""Elliptic-curve tools for grids U+V in squares.

For columns v1,v2,v3 the admissible rows are x(2P), P in E(Q), where
E: Y^2 = (X+v1)(X+v2)(X+v3).  Halving: if X+v_i = s_i^2 then
x(P) = X + s1 s2 + s1 s3 + s2 s3 has 2P = (X, *).
"""
from fractions import Fraction as F
from itertools import combinations, product
import cypari2

from known import is_sq, sqrtq, KNOWN

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)
pari.set_real_precision(60)


def frac(g):
    return F(int(pari.numerator(g)), int(pari.denominator(g)))


def curve(v1, v2, v3):
    v1, v2, v3 = map(F, (v1, v2, v3))
    a2 = v1 + v2 + v3
    a4 = v1 * v2 + v1 * v3 + v2 * v3
    a6 = v1 * v2 * v3
    return pari.ellinit([0, str(a2), 0, str(a4), str(a6)])


def half(X, vs):
    s = [sqrtq(F(X) + v) for v in vs]
    x = F(X) + s[0] * s[1] + s[0] * s[2] + s[1] * s[2]
    y2 = (x + vs[0]) * (x + vs[1]) * (x + vs[2])
    y = sqrtq(y2) if y2 >= 0 else None
    assert y is not None and y * y == y2
    return [str(x), str(y)]


def mw_basis(E, effort=None):
    r = pari.ellrank(E) if effort is None else pari.ellrank(E, effort)
    lo, hi, gens = int(r[0]), int(r[1]), r[3]
    if len(gens):
        gens = pari.ellsaturation(E, gens, 100)
    return lo, hi, gens


def coords(E, gens, P):
    """Real coefficients of P (mod torsion) in the basis gens via height pairing."""
    n = len(gens)
    if n == 0:
        return []
    G = pari.matrix(n, n, [pari.ellheight(E, gens[i], gens[j]) for i in range(n) for j in range(n)])
    b = pari.matrix(n, 1, [pari.ellheight(E, gens[i], P) for i in range(n)])
    sol = pari.matsolve(G, b)
    return [float(sol[i, 0]) for i in range(n)]


def analyse(name, U, V):
    U = [F(u) for u in U]
    V = [F(v) for v in V]
    print(f"== {name}: {len(U)}x{len(V)}")
    for T in combinations(range(len(V)), 3):
        vs = [V[i] for i in T]
        E = curve(*vs)
        lo, hi, gens = mw_basis(E)
        tors = pari.elltors(E)
        rows = []
        for u in U:
            P = half(u, vs)
            rows.append([round(c, 3) for c in coords(E, gens, P)])
        print(f" cols {T} rank [{lo},{hi}] tors {tors[1]} cond~{int(pari.ellglobalred(E)[0]).bit_length()}b")
        for u, c in zip(U, rows):
            print(f"    row {u}: {c}")


if __name__ == "__main__":
    import sys
    names = sys.argv[1:] or list(KNOWN)
    for k in names:
        analyse(k, *KNOWN[k])
