"""High-precision Newton for deformations of the full 7x7 Lagrange polynomial pattern.

Gauge+moduli fixed by: C1 = c (x-4)(x+1)(x+4)(x-r) (Lagrange: r=-19/11) and C2(0) = s.
Solve for everything else; then test rationality of the solution (bestappr).
usage: deform_newton.py r s
"""
import sys
from obstr import setup, pari, R, C, ZERO, X

pari.set_real_precision(int(__import__("os").environ.get("PREC","120")))
rows = list(range(7)); cols = list(range(7))
inc, var, idx, _ = setup(rows, cols)
msq = pari("msq")
z0 = {}
for i in rows:
    a = msq(R[i])
    for k in range(3):
        z0[("a", i, k)] = pari.polcoef(a, k)
for j in cols:
    if j != ZERO:
        for k in range(5):
            z0[("C", j, k)] = pari.polcoef(C[j], k)
for e in inc:
    b = msq(R[e[0]] + C[e[1]]) if R[e[0]] + C[e[1]] != 0 else pari(0)
    for k in range(3):
        z0[("b", e, k)] = pari.polcoef(b, k)
lc1 = pari.pollead(C[1])
free = [v for v in var if not (v[0] == "C" and v[1] == 1) and v != ("C", 2, 0)]
fidx = {v: n for n, v in enumerate(free)}


def polys(z, r, s):
    P = {}
    for i in rows:
        P[("a", i)] = sum(z[("a", i, k)] * X ** k for k in range(3))
    for e in inc:
        P[("b", e)] = sum(z[("b", e, k)] * X ** k for k in range(3))
    P[("C", ZERO)] = pari(0)
    for j in cols:
        if j not in (ZERO, 1):
            P[("C", j)] = sum(z[("C", j, k)] * X ** k for k in range(5))
    P[("C", 1)] = lc1 * (X - 4) * (X + 1) * (X + 4) * (X - r)
    P[("C", 2)] = P[("C", 2)] - pari.polcoef(P[("C", 2)], 0) + s
    return P


def FJ(z, r, s):
    P = polys(z, r, s)
    Fv, Jrows = [], []
    for (i, j) in inc:
        f = P[("a", i)] ** 2 + P[("C", j)] - P[("b", (i, j))] ** 2
        blk = [[pari(0)] * len(free) for _ in range(5)]
        for k in range(3):
            pa = 2 * P[("a", i)] * X ** k
            pb = -2 * P[("b", (i, j))] * X ** k
            for m in range(5):
                blk[m][fidx[("a", i, k)]] += pari.polcoef(pa, m)
                blk[m][fidx[("b", (i, j), k)]] += pari.polcoef(pb, m)
        if j not in (ZERO, 1):
            for k in range(5):
                if (("C", j, k)) in fidx:
                    blk[k][fidx[("C", j, k)]] += 1
        Fv += [pari.polcoef(f, m) for m in range(5)]
        Jrows += blk
    return Fv, Jrows


def solve(r, s, its=40, verbose=True):
    z = {k: pari(v) * pari("1.0") for k, v in z0.items()}
    for it in range(its):
        Fv, Jr = FJ(z, r, s)
        res = max(abs(f) for f in Fv)
        if verbose:
            print(f"  it {it} res {pari.precision(res,10) if res else 0}", flush=True)
        if res < pari("1e-" + str(int(pari.default("realprecision")) - 20)):
            break
        Jm = pari.matrix(len(Jr), len(free), [c for row in Jr for c in row])
        Jt = pari.mattranspose(Jm)
        rhs = pari.matrix(len(Fv), 1, Fv)
        dz = pari.matsolve(Jt * Jm, -(Jt * rhs))
        for v, n in fidx.items():
            z[v] = z[v] + dz[n, 0]
    return z, res


def rationalise(z, bound=10**12):
    out, ok = {}, True
    for k, v in z.items():
        q = pari.bestappr(v, bound)
        if abs(q - v) > pari("1e-60"):
            ok = False
        out[k] = q
    return out, ok


if __name__ == "__main__":
    r = pari(sys.argv[1]) if len(sys.argv) > 1 else pari("-19/11")
    s = pari(sys.argv[2]) if len(sys.argv) > 2 else pari.polcoef(C[2], 0)
    print("Lagrange s0 =", pari.polcoef(C[2], 0))
    z, res = solve(r, s)
    q, ok = rationalise(z)
    print("residual", res, "rational:", ok)
    if ok:
        P = polys(q, r, s)
        for j in cols:
            print("C", j, pari.factor(P[("C", j)]) if P[("C", j)] != 0 else 0)
        for i in rows:
            print("a", i, P[("a", i)])
