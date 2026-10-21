"""Is a numeric grid (or a sub-grid) a specialisation of a polynomial row/col set R(x), C(x)?

Affine equivalence (u,v) -> (c u + s, c v - s), plus transposition.  For an ordered row pair
(i0,i1) of the numeric grid and an ordered pair (a,b) of polynomial rows, the invariant
rho = (u_i1-u_i0)/(v_j1-v_j0) gives an equation in x; each rational root is tested by mapping
all of R(x), C(x) and counting how many numeric rows/cols are hit.
usage: member.py closure.json grid.json [grid.json ...]
"""
import json, sys
from fractions import Fraction as F
from itertools import permutations
import cypari2

pari = cypari2.Pari()
pari.allocatemem(10**9)


def fr(g):
    return F(int(pari.numerator(g)), int(pari.denominator(g)))


def load_grid(path):
    d = json.load(open(path))
    return [F(x) for x in d["U"]], [F(x) for x in d["V"]]


def match(R, C, U, V, label):
    R = [pari(r) for r in R]
    C = [pari(c) for c in C]
    best = (0, None)
    i0, i1 = 0, 1
    j0, j1 = 0, 1
    rho = (U[i1] - U[i0]) / (V[j1] - V[j0])
    seen = set()
    for a, b in permutations(range(len(R)), 2):
        for c, d in permutations(range(len(C)), 2):
            num = (R[b] - R[a]) - pari(str(rho)) * (C[d] - C[c])
            if num == 0:
                continue
            for f in pari.factor(num)[0]:
                if int(pari.poldegree(f)) != 1:
                    continue
                t = -pari.polcoef(f, 0) / pari.polcoef(f, 1)
                if (str(t), a, c) in seen:
                    continue
                seen.add((str(t), a, c))
                try:
                    Rt = [fr(pari.subst(r, "x", t)) for r in R]
                    Ct = [fr(pari.subst(q, "x", t)) for q in C]
                except Exception:
                    continue
                if Rt[b] == Rt[a]:
                    continue
                sc = (U[i1] - U[i0]) / (Rt[b] - Rt[a])
                s = U[i0] - sc * Rt[a]
                Rs = {sc * r + s for r in Rt}
                Cs = {sc * q - s for q in Ct}
                hr = sum(u in Rs for u in U)
                hc = sum(v in Cs for v in V)
                if hr + hc > best[0]:
                    best = (hr + hc, (label, str(t), hr, hc))
    return best


def main():
    cl = json.load(open(sys.argv[1]))
    R, C = cl["R"], cl["C"]
    for g in sys.argv[2:]:
        U, V = load_grid(g)
        res = []
        A, B = (U, V) if len(U) >= len(V) else (V, U)   # A = long side; B fully in the subgrid
        from itertools import combinations
        for p in combinations(range(len(A)), 2):
            A2 = [A[p[0]], A[p[1]]] + [A[i] for i in range(len(A)) if i not in p]
            res.append(match(R, C, A2, B, "long=rows"))
            res.append(match(R, C, B, A2, "long=cols"))
        res.sort(key=lambda r: -r[0])
        print(g, "best", res[0], flush=True)


if __name__ == "__main__":
    main()
