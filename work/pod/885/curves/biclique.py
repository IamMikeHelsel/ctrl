"""Maximal bicliques (identically square in Q[x]) of a polynomial row/col structure, and
near-bicliques (few missing entries, each giving a square condition in x).
usage: biclique.py closure.json maxrows
"""
import sys, json
from itertools import combinations
from families import pari

P = json.load(open(sys.argv[1]))
maxr = int(sys.argv[2]) if len(sys.argv) > 2 else 7
R = [pari(s) for s in P["R"]]
C = [pari(s) for s in P["C"]]
inc = [[bool(pari.issquare(r + c)) for c in C] for r in R]
nR, nC = len(R), len(C)
colsets = [frozenset(j for j in range(nC) if inc[i][j]) for i in range(nR)]
best = {}
for m in range(2, maxr + 1):
    any_ = False
    for rows in combinations(range(nR), m):
        common = frozenset.intersection(*[colsets[i] for i in rows])
        n = len(common)
        if n >= 3:
            any_ = True
            key = (m, n)
            best.setdefault(key, []).append((rows, sorted(common)))
    if not any_:
        break
shapes = sorted(best, key=lambda k: (-min(k), -max(k)))
print(f"{nR} rows x {nC} cols; polynomial biclique shapes (rows x cols): count")
for k in sorted(best):
    if k[0] >= 3 and k[1] >= 3:
        print(f"  {k[0]}x{k[1]}: {len(best[k])}  e.g. {best[k][0]}")
