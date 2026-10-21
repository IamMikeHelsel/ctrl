"""Exact second-order obstruction for deformations of a polynomial grid pattern.

F(z0+t) = J t + Q(t) (F is quadratic, F(z0)=0).  A first-order t in ker J extends to second
order iff L Q(t) = 0 for the left kernel L of J.  We compute the 6-dim kernel (4 GL2 + 2 new),
and the quadratic forms c -> L Q(sum c_a k_a).
"""
import json, sys
from famext import pari

msq = pari("msq")
d = json.load(open("poly77_lagrange.json"))
R = [pari(r) for r in d["R"]]
C = [pari(c) for c in d["C"]]
ZERO = 3
X = pari("x")


def setup(rows, cols):
    inc = sorted((i, j) for i in rows for j in cols if pari.issquare(R[i] + C[j]))
    var = [("a", i, k) for i in rows for k in range(3)]
    var += [("C", j, k) for j in cols if j != ZERO for k in range(5)]
    var += [("b", e, k) for e in inc for k in range(3)]
    idx = {v: n for n, v in enumerate(var)}
    A = {i: msq(R[i]) for i in rows}
    B = {e: (msq(R[e[0]] + C[e[1]]) if R[e[0]] + C[e[1]] != 0 else pari(0)) for e in inc}
    rowsJ = []
    for (i, j) in inc:
        blk = [[pari(0)] * len(var) for _ in range(5)]
        for k in range(3):
            for m in range(5):
                blk[m][idx[("a", i, k)]] += pari.polcoef(2 * A[i] * X ** k, m)
                blk[m][idx[("b", (i, j), k)]] += pari.polcoef(-2 * B[(i, j)] * X ** k, m)
        if j != ZERO:
            for k in range(5):
                blk[k][idx[("C", j, k)]] += 1
        rowsJ += blk
    Jm = pari.matrix(len(rowsJ), len(var), [c for r in rowsJ for c in r])
    return inc, var, idx, Jm


def poly_of(t, idx, key, n):
    return sum(t[idx[(key[0], key[1], k)]] * X ** k for k in range(n))


def Qbil(s, t, inc, idx):
    out = []
    for (i, j) in inc:
        p = poly_of(s, idx, ("a", i), 3) * poly_of(t, idx, ("a", i), 3) - poly_of(s, idx, ("b", (i, j)), 3) * poly_of(t, idx, ("b", (i, j)), 3)
        out += [pari.polcoef(p, m) for m in range(5)]
    return out


def main(rows, cols):
    inc, var, idx, Jm = setup(rows, cols)
    K = pari.matker(Jm)
    nk = len(K)
    L = pari.matker(pari.mattranspose(Jm))
    print("entries", len(inc), "vars", len(var), "kernel", nk, "coker", len(L))
    ks = [[K[a][r] for r in range(len(var))] for a in range(nk)]
    Lt = pari.mattranspose(L)
    forms = {}
    for a in range(nk):
        for b in range(a, nk):
            q = Qbil(ks[a], ks[b], inc, idx)
            forms[(a, b)] = Lt * pari.matrix(len(q), 1, q)
    # quadratic forms in c_0..c_{nk-1}
    cs = [pari(f"c{a}") for a in range(nk)]
    polys = []
    for r in range(len(L)):
        p = sum((1 if a == b else 2) * forms[(a, b)][r, 0] * cs[a] * cs[b] for (a, b) in forms)
        polys.append(p)
    nz = [p for p in polys if p != 0]
    print("nonzero obstruction forms:", len(nz))
    # rank of the space of quadrics
    mons = [(a, b) for a in range(nk) for b in range(a, nk)]
    M = pari.matrix(len(L), len(mons), [(1 if a == b else 2) * forms[(a, b)][r, 0] for r in range(len(L)) for (a, b) in mons])
    print("rank of obstruction quadrics:", pari.matrank(M))
    return nz, K


if __name__ == "__main__":
    pats = {"lagrange4x4": ([0, 1, 2, 3], [0, 1, 2, 3]), "full7x7": (list(range(7)), list(range(7))),
            "3x7": ([0, 2, 3], list(range(7)))}
    for k in (sys.argv[1:] or pats):
        print("==", k)
        nz, K = main(*pats[k])
        for p in nz[:6]:
            print("  ", p)
