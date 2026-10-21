"""Experiment: do collinear 3x3 bases extend more often?

For curves E_{0,a,b} of rank >= 2, rows R(n) = x(2 sum n_i G_i), n in box.
For every row triple among the first K rows, classify collinear (n_a +- n_b +- n_c = 0)
and count columns (box on E_S) that hit >= 4 rows.
"""
import sys, json
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd
from ext import pari, box_points, RowSet, curve, half, mw_basis

AMAX = int(sys.argv[1]); W = int(sys.argv[2]); NW = int(sys.argv[3])
K = 14
out = open(f"logs/collin_w{W}.log", "a")


def collinear(n1, n2, n3):
    for s2, s3 in product((1, -1), repeat=2):
        if all(a + s2 * b + s3 * c == 0 for a, b, c in zip(n1, n2, n3)):
            return True
    return False


stats = {"col": [0, 0, 0], "non": [0, 0, 0]}  # triples, columns, hits>=4
pairs = [(a, b) for b in range(2, AMAX) for a in range(-b + 1, b) if a and gcd(a, b) == 1][W::NW]
for a, b in pairs:
    V = [F(0), F(a), F(b)]
    E = curve(*V)
    lo, hi, gens = mw_basis(E)
    if lo < 2:
        continue
    gens = list(gens)
    rows = {}
    for n, X in box_points(E, gens, 2):
        if X not in V and -X not in V:
            rows.setdefault(X, n)
    rl = sorted(rows, key=lambda x: (len(str(x)), x))
    RS = RowSet(rl)
    small = rl[:K]
    for S in combinations(range(len(small)), 3):
        Xs = [small[i] for i in S]
        kind = "col" if collinear(*[rows[x] for x in Xs]) else "non"
        stats[kind][0] += 1
        ES = curve(*Xs)
        base = [half(v, Xs) for v in V]
        for n, c in box_points(ES, base, 2):
            if c in V:
                continue
            h = RS.hits(c)
            stats[kind][1] += 1
            if len(h) >= 4:
                stats[kind][2] += 1
                out.write(json.dumps(dict(a=a, b=b, kind=kind, S=[str(x) for x in Xs], nS=[rows[x] for x in Xs], c=str(c), ncol=n, hits=[str(rl[i]) for i in h], nh=[rows[rl[i]] for i in h])) + "\n")
                out.flush()
    out.write(f"# a={a} b={b} r={lo} stats={stats}\n")
    out.flush()
