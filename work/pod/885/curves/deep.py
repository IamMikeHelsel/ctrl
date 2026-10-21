"""Deep extension search on one explicit grid: for every triple curve (both orientations) use
the halves of known points plus an ellrank Mordell-Weil basis, box coefficients up to N,
and test the remaining lines.  usage: deep.py grid.json N [effort]"""
import sys, json, time
from fractions import Fraction as F
from itertools import combinations, product
from ecgrid import pari, curve, half, mw_basis
from ext import is_sq, pt2frac

g = json.load(open(sys.argv[1]))
N = int(sys.argv[2])
U = [F(x) for x in g["U"]]
V = [F(x) for x in g["V"]]
out = open(sys.argv[1].replace(".json", f".deep{N}.log"), "a")


def L(s):
    print(s, flush=True)
    out.write(s + "\n")
    out.flush()


def side(A, B, label):
    found = {}
    for T in combinations(range(len(B)), 3):
        vs = [B[i] for i in T]
        rest = [B[i] for i in range(len(B)) if i not in T]
        E = curve(*vs)
        t = time.time()
        try:
            lo, hi, gens = mw_basis(E)
            gens = list(gens)
        except Exception as e:
            lo, hi, gens = -1, -1, []
        base = gens if gens else [pari(half(a, vs)) for a in A]
        L(f"# {label} T={T} rank {lo}..{hi} base={len(base)} ({time.time()-t:.1f}s)")
        cnt = 0
        for n in product(range(-N, N + 1), repeat=len(base)):
            nz = [c for c in n if c]
            if not nz or nz[0] < 0:
                continue
            P = [0]
            for c, h in zip(n, base):
                if c:
                    P = pari.elladd(E, P, pari.ellmul(E, h, c))
            if len(P) == 1:
                continue
            P2 = pari.ellmul(E, P, 2)
            if len(P2) == 1:
                continue
            X = pt2frac(P2[0])
            cnt += 1
            if X in A or X in found:
                continue
            k = sum(is_sq(X + b) for b in rest)
            if k == len(rest):
                found[X] = (T, n)
                L(f"NEW {label} T={T} n={n} X={X}")
            elif k >= len(rest) - 1 and len(rest) >= 2:
                L(f"near {label} T={T} n={n} misses 1 of {len(rest)}")
        L(f"#   tested {cnt}")
    return found


R = side(U, V, "row")
C = side(V, U, "col")
for r in R:
    for c in C:
        if is_sq(r + c):
            L(f"EXT +row+col: r={r} c={c}")
L(f"# done: {len(R)} new rows, {len(C)} new cols")
