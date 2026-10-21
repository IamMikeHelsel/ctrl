"""Numeric extension of an explicit grid U x V by group-law combinations of halved known points.

New rows: for each column triple T, P = sum n_i half_T(u_i) on E_T, row x(2P); keep if valid
for all columns.  New columns: same with roles swapped.  Then look for compatible
(new row, new column) pairs and pairs of new rows/cols.
"""
from fractions import Fraction as F
from itertools import combinations, product
from ecgrid import pari, curve, half
from ext import is_sq, pt2frac


def extend_side(U, V, N=1, maxterms=None):
    """Rows valid for all of V obtained from box combos on triple curves of V."""
    found = {}
    for T in combinations(range(len(V)), 3):
        vs = [V[i] for i in T]
        rest = [V[i] for i in range(len(V)) if i not in T]
        E = curve(*vs)
        H = [pari(half(u, vs)) for u in U]
        for n in product(range(-N, N + 1), repeat=len(U)):
            nz = [c for c in n if c]
            if len(nz) < 2 or nz[0] < 0 or (maxterms and len(nz) > maxterms):
                continue
            P = [0]
            for c, h in zip(n, H):
                if c:
                    P = pari.elladd(E, P, pari.ellmul(E, h, c))
            if len(P) == 1:
                continue
            P2 = pari.ellmul(E, P, 2)
            if len(P2) == 1:
                continue
            X = pt2frac(P2[0])
            if X in U or X in found:
                continue
            if all(is_sq(X + v) for v in rest):
                found[X] = (T, n)
    return found


def extend(U, V, N=1, maxterms=None):
    U = [F(u) for u in U]
    V = [F(v) for v in V]
    R = extend_side(U, V, N, maxterms)
    C = extend_side(V, U, N, maxterms)
    out = {"rows": R, "cols": C, "grids": []}
    Rl, Cl = list(R), list(C)
    for r in Rl:
        for c in Cl:
            if is_sq(r + c):
                out["grids"].append(("+1row+1col", [r], [c]))
    if len(Rl) >= 2:
        out["grids"] += [("+rows", Rl, [])]
    if len(Cl) >= 2:
        out["grids"] += [("+cols", [], Cl)]
    return out
