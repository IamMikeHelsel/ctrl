"""Dual criterion: Gram matrix on the row-triple K3 E_A (columns as sections), for a poly77 JSON.
Picks a row triple contained in the most columns; shifts so that one row becomes 0.
usage: t_k3dual.py poly77_X.json"""
import json, sys
from itertools import combinations
from k3height import K3, pari

d = json.load(open(sys.argv[1]))
R = [pari(r) for r in d["R"]]
C = [pari(c) for c in d["C"]]
inc = lambda i, j: bool(pari.issquare(R[i] + C[j]))
best = max(combinations(range(len(R)), 3), key=lambda T: sum(all(inc(i, j) for i in T) for j in range(len(C))))
from polyrows import poly_rows
allc = [Xc for _, (Xc, sset) in poly_rows([R[i] for i in best], 2).items() if len(sset) == 3]
print("row triple", best, "complete column count", len(allc))
s = R[best[0]]
E = K3([R[i] - s for i in best])
Ps = [E.half(c + s) for c in allc]
cols = allc
G = E.gram(Ps)
for row in G:
    print([str(g) for g in row])
n = len(cols)
print("rank", pari.matrank(pari.matrix(n, n, [str(g) for row in G for g in row])))
