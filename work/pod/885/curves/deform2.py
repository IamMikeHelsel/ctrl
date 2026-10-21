"""Newton on the full 7x7 Lagrange pattern with an arbitrary set of fixed coordinates.

fixed: dict var -> value (var = ("a",i,k) | ("C",j,k) | ("b",(i,j),k)); column ZERO is 0.
"""
import os
from obstr import setup, pari, R, C, ZERO, X

pari.set_real_precision(int(os.environ.get("PREC", "150")))
ROWS = list(range(7)); COLS = list(range(7))
INC, VAR, IDX, _ = setup(ROWS, COLS)
msq = pari("msq")
Z0 = {}
for i in ROWS:
    a = msq(R[i])
    for k in range(3):
        Z0[("a", i, k)] = pari.polcoef(a, k)
for j in COLS:
    if j != ZERO:
        for k in range(5):
            Z0[("C", j, k)] = pari.polcoef(C[j], k)
for e in INC:
    b = msq(R[e[0]] + C[e[1]]) if R[e[0]] + C[e[1]] != 0 else pari(0)
    for k in range(3):
        Z0[("b", e, k)] = pari.polcoef(b, k)


def polys(z):
    P = {}
    for i in ROWS:
        P[("a", i)] = sum(z[("a", i, k)] * X ** k for k in range(3))
    for e in INC:
        P[("b", e)] = sum(z[("b", e, k)] * X ** k for k in range(3))
    P[("C", ZERO)] = pari(0)
    for j in COLS:
        if j != ZERO:
            P[("C", j)] = sum(z[("C", j, k)] * X ** k for k in range(5))
    return P


def solve(fixed, z=None, its=60, tol=None):
    free = [v for v in VAR if v not in fixed]
    fidx = {v: n for n, v in enumerate(free)}
    if z is None:
        z = {k: pari(v) * pari("1.0") for k, v in Z0.items()}
    for k, v in fixed.items():
        z[k] = pari(v)
    tol = tol or pari("1e-" + str(int(pari.default("realprecision")) - 20))
    res = None
    for it in range(its):
        P = polys(z)
        Fv, Jr = [], []
        for (i, j) in INC:
            f = P[("a", i)] ** 2 + P[("C", j)] - P[("b", (i, j))] ** 2
            blk = [[pari(0)] * len(free) for _ in range(5)]
            for k in range(3):
                pa = 2 * P[("a", i)] * X ** k
                pb = -2 * P[("b", (i, j))] * X ** k
                for m in range(5):
                    if ("a", i, k) in fidx:
                        blk[m][fidx[("a", i, k)]] += pari.polcoef(pa, m)
                    if ("b", (i, j), k) in fidx:
                        blk[m][fidx[("b", (i, j), k)]] += pari.polcoef(pb, m)
            if j != ZERO:
                for k in range(5):
                    if ("C", j, k) in fidx:
                        blk[k][fidx[("C", j, k)]] += 1
            Fv += [pari.polcoef(f, m) for m in range(5)]
            Jr += blk
        res = max(abs(f) for f in Fv)
        if res < tol:
            break
        Jm = pari.matrix(len(Jr), len(free), [c for row in Jr for c in row])
        Jt = pari.mattranspose(Jm)
        dz = pari.matsolve(Jt * Jm, -(Jt * pari.matrix(len(Fv), 1, Fv)))
        for v, n in fidx.items():
            z[v] = z[v] + dz[n, 0]
    return z, res, it


def rationalise(z, bound=10**15, eps="1e-80"):
    out, bad = {}, 0
    for k, v in z.items():
        q = pari.bestappr(v, bound)
        if abs(q - v) > pari(eps) * (1 + abs(v)):
            bad += 1
        out[k] = q
    return out, bad
