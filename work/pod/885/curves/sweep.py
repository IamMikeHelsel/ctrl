"""Sweep curves E_{0,a,b}: y^2 = x(x+a)(x+b) over coprime a<b, keep rank >= RMIN, run the
two-sided extension search.  Usage: sweep.py AMAX RMIN WORKER NWORKERS [Nrow K Ncol]"""
import sys, time
from math import gcd
from fractions import Fraction as F
from ext import search_curve, pari
from ecgrid import curve

AMAX, RMIN, W, NW = map(int, sys.argv[1:5])
Nrow, K, Ncol = (map(int, sys.argv[5:8]) if len(sys.argv) > 7 else (2, 12, 2))
log = open(f"logs/sweep_A{AMAX}_R{RMIN}_w{W}.log", "a")


def L(s):
    log.write(s + "\n")
    log.flush()


def squarefree_ok(a, b):
    g = gcd(a, b)
    # skip if a common square factor (equivalent curve after scaling)
    for p in range(2, int(g**0.5) + 1):
        if g % (p * p) == 0:
            return False
    return True


pairs = []
for b in range(2, AMAX + 1):
    for a in range(1, b):
        if squarefree_ok(a, b):
            pairs.append((a, b))
# also negative a: columns {0, -a, b} (x+a with a<0) give other curves
pairs += [(-a, b) for (a, b) in list(pairs)]
pairs = pairs[W::NW]
L(f"# worker {W}/{NW}: {len(pairs)} pairs")
for a, b in pairs:
    E = curve(0, a, b)
    try:
        r = pari.ellrank(E)
    except Exception as e:
        continue
    lo = int(r[0])
    if lo < RMIN:
        continue
    t = time.time()
    L(f"## a={a} b={b} rank>={lo}")
    try:
        search_curve([0, a, b], Nrow=Nrow, K=K, Ncol=Ncol, log=L)
    except Exception as e:
        L(f"# error {e!r}")
    L(f"## time {time.time()-t:.1f}")
