"""Two-sided group-law extension search.

Fix columns V = (v1,v2,v3).  Rows = x(2P), P in a coefficient box on E_V.
For a triple S of rows, columns = x(2Q), Q in a box spanned by the halves of
v1,v2,v3 on E_S (plus optional extra generators).  A column c is then tested
against every row; hits >= 5 gives a 5x4 grid, >= 6 a 6x4 grid; two columns
sharing >= 5 rows give a 5x5 grid.
"""
from fractions import Fraction as F
from itertools import product, combinations
import numpy as np
import sys, time, json
import gmpy2

from ecgrid import pari, curve, half, mw_basis

PRIMES = [p for p in range(3, 400) if all(p % q for q in range(2, int(p**0.5) + 1))][:40]
QR = {p: np.zeros(p, dtype=bool) for p in PRIMES}
for p in PRIMES:
    for x in range(p):
        QR[p][x * x % p] = True
    QR[p][0] = True
OFF = np.cumsum([0] + PRIMES[:-1])
QRFLAT = np.concatenate([QR[p] for p in PRIMES])
PR = np.array(PRIMES, dtype=np.int64)


def residues(q):
    """q mod each prime, or -1 when the prime divides the denominator."""
    n, d = q.numerator, q.denominator
    out = np.empty(len(PRIMES), dtype=np.int64)
    for k, p in enumerate(PRIMES):
        dm = d % p
        out[k] = -1 if dm == 0 else (n % p) * pow(dm, -1, p) % p
    return out


def is_sq(q):
    if q < 0:
        return False
    return gmpy2.is_square(q.numerator) and gmpy2.is_square(q.denominator)


def pt2frac(g):
    return F(int(pari.numerator(g)), int(pari.denominator(g)))


def box_points(E, base, N, maxterms=None):
    """Yield (coeffs, x(2P)) for P = sum n_i base_i, n in [-N,N]^k, first nonzero > 0."""
    k = len(base)
    seen = set()
    for n in product(range(-N, N + 1), repeat=k):
        nz = [c for c in n if c]
        if not nz or nz[0] < 0:
            continue
        if maxterms and len(nz) > maxterms:
            continue
        P = [0]
        for c, B in zip(n, base):
            if c:
                P = pari.elladd(E, P, pari.ellmul(E, B, c))
        if P == [0] or len(P) == 1:
            continue
        P2 = pari.ellmul(E, P, 2)
        if len(P2) == 1:
            continue
        X = pt2frac(P2[0])
        if X in seen:
            continue
        seen.add(X)
        yield n, X


class RowSet:
    def __init__(self, rows):
        self.rows = list(rows)
        self.res = np.array([residues(r) for r in self.rows]) if self.rows else np.zeros((0, len(PRIMES)), dtype=np.int64)

    def hits(self, c):
        cr = residues(c)
        S = self.res + cr[None, :]
        bad = (self.res < 0) | (cr[None, :] < 0)
        S = np.where(bad, 0, S % PR[None, :])
        ok = QRFLAT[S + OFF[None, :]].all(axis=1)
        idx = np.nonzero(ok)[0]
        return [int(i) for i in idx if is_sq(self.rows[i] + c)]


def search_curve(V, Nrow=2, K=14, Ncol=2, extra_rows=(), log=print, rank_effort=None):
    V = [F(v) for v in V]
    E = curve(*V)
    lo, hi, gens = mw_basis(E, rank_effort)
    gens = list(gens)
    rows = {}
    for n, X in box_points(E, gens, Nrow):
        if any(X == -v for v in V):
            continue
        rows[X] = n
    for X in extra_rows:
        rows.setdefault(F(X), "known")
    rowlist = sorted(rows, key=lambda x: (len(str(x)), x))
    RS = RowSet(rowlist)
    log(f"# V={[str(v) for v in V]} rank={lo}..{hi} rows={len(rowlist)}")
    best = []
    colhits = {}
    small = rowlist[:K]
    for S in combinations(range(len(small)), 3):
        Xs = [small[i] for i in S]
        if len(set(Xs)) < 3:
            continue
        ES = curve(*Xs)
        base = [half(v, Xs) for v in V]
        for n, c in box_points(ES, base, Ncol):
            if c in V or c in colhits:
                continue
            h = RS.hits(c)
            colhits[c] = h
            if len(h) >= 5:
                rec = dict(V=[str(v) for v in V], c=str(c), rows=[str(rowlist[i]) for i in h], S=S, n=n)
                log(f"HIT{len(h)}x4 " + json.dumps(rec))
                best.append(rec)
    # 5x5 check: pairs of columns sharing >= 5 rows
    big = [(c, set(h)) for c, h in colhits.items() if len(h) >= 4]
    for (c1, h1), (c2, h2) in combinations(big, 2):
        common = h1 & h2
        if len(common) >= 4:
            tag = "HIT5x5" if len(common) >= 5 else "near5x5(4x5)"
            log(f"{tag} " + json.dumps(dict(V=[str(v) for v in V], c1=str(c1), c2=str(c2), rows=[str(rowlist[i]) for i in common])))
    hist = {}
    for h in colhits.values():
        hist[len(h)] = hist.get(len(h), 0) + 1
    log(f"# hist {sorted(hist.items())}")
    return best, hist


if __name__ == "__main__":
    from known import KNOWN
    name = sys.argv[1]
    U, V = KNOWN[name]
    cols = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [0, 1, 2]
    t = time.time()
    search_curve([V[i] for i in cols], extra_rows=U, K=int(sys.argv[3]) if len(sys.argv) > 3 else 10)
    print("time", time.time() - t)
