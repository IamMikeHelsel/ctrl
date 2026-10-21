"""Find small integer relations among halved points (mod torsion) on all triple curves, both orientations."""
import sys
from fractions import Fraction as F
from itertools import combinations, product
from ecgrid import pari, curve, half, mw_basis, coords
from known import KNOWN


def rels(pts_coords, maxc=2, maxterms=4):
    n = len(pts_coords)
    out = []
    rng = [c for c in range(-maxc, maxc + 1)]
    for k in range(2, maxterms + 1):
        for S in combinations(range(n), k):
            for cs in product([c for c in rng if c > 0], *[[c for c in rng if c != 0]] * (k - 1)):
                v = [sum(c * pts_coords[i][t] for c, i in zip(cs, S)) for t in range(len(pts_coords[0]))]
                if all(abs(x) < 1e-6 for x in v):
                    out.append(tuple(zip(cs, S)))
    return out


def side(U, V, label):
    res = {}
    for T in combinations(range(len(V)), 3):
        vs = [F(V[i]) for i in T]
        E = curve(*vs)
        lo, hi, gens = mw_basis(E)
        C = [coords(E, gens, half(F(u), vs)) for u in U]
        r = rels(C)
        # keep only minimal relations (no sub-relation)
        sets = [frozenset(i for _, i in x) for x in r]
        mins = [x for x, s in zip(r, sets) if not any(s2 < s for s2 in sets)]
        res[T] = (lo, mins)
        print(f"  {label} cols{T} rank {lo}: {mins}")
    return res


if __name__ == "__main__":
    for k in sys.argv[1:] or list(KNOWN):
        U, V = KNOWN[k]
        print("==", k)
        side(U, V, "rows-on")
        if len(U) >= 3:
            side(V, U, "cols-on")
