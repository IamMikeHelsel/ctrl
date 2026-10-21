"""Near-bicliques: for target shapes, subgrids with the fewest missing entries; list the missing
entries with the degree of their square-free condition.  usage: nearbic.py closure.json"""
import sys, json
from itertools import combinations
from families import pari
from famext import gp_sqfree

P = json.load(open(sys.argv[1]))
R = [pari(s) for s in P["R"]]
C = [pari(s) for s in P["C"]]
inc = [[bool(pari.issquare(r + c)) for c in C] for r in R]
nR, nC = len(R), len(C)
targets = [(5, 5), (6, 4), (4, 6), (6, 5), (5, 6), (7, 4), (4, 7), (7, 5)]
res = {}
for m in range(4, 8):
    for rows in combinations(range(nR), m):
        mpc = sorted((sum(not inc[i][j] for i in rows), j) for j in range(nC))
        for (tm, tn) in targets:
            if tm != m:
                continue
            tot = sum(c for c, j in mpc[:tn])
            cols = tuple(sorted(j for c, j in mpc[:tn]))
            cur = res.get((tm, tn))
            if cur is None or tot < cur[0]:
                res[(tm, tn)] = (tot, [(rows, cols)])
            elif tot == cur[0] and len(cur[1]) < 200:
                cur[1].append((rows, cols))
deg = {}
for k in targets:
    if k not in res:
        continue
    tot, lst = res[k]
    print(f"{k[0]}x{k[1]}: min missing {tot}, {len(lst)} subgrids")
    for rows, cols in lst[:6]:
        miss = [(i, j) for i in rows for j in cols if not inc[i][j]]
        ds = []
        for (i, j) in miss:
            if (i, j) not in deg:
                c0, F = gp_sqfree(R[i] + C[j])
                deg[(i, j)] = int(pari.poldegree(F))
            ds.append(deg[(i, j)])
        print(f"    rows {rows} cols {cols} missing {miss} degs {ds}")
json.dump({f"{k[0]}x{k[1]}": [res[k][0], res[k][1]] for k in res}, open(sys.argv[1].replace(".json", "_near.json"), "w"))
