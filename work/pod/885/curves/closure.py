"""Polynomial closure: alternately add all degree<=4 polynomial rows valid for >=3 current
columns and columns valid for >=3 current rows; print the incidence and the best
biclique shapes with their number of missing (genus-1) conditions.
usage: closure.py FAMILY subs [iters]
"""
import sys, json
from itertools import combinations
from families import pari, load
from polyrows import poly_rows
from famext import gp_sqfree

fam = sys.argv[1]
subs = dict(kv.split("=") for kv in sys.argv[2].split(","))
iters = int(sys.argv[3]) if len(sys.argv) > 3 else 3
U, V = load(fam, subs)
R = {str(u): u for u in U}
C = {str(v): v for v in V}
for it in range(iters):
    nr = {k: X for k, (X, s) in poly_rows(list(C.values()), 2).items()}
    nc = {k: X for k, (X, s) in poly_rows(list(R.values()), 2).items()}
    added = len(set(nr) - set(R)) + len(set(nc) - set(C))
    R.update(nr)
    C.update(nc)
    print(f"iter {it}: rows {len(R)} cols {len(C)} (+{added})", flush=True)
    json.dump(dict(R=list(R), C=list(C)), open(f"closure_{fam}_it{it}.json", "w"))
    if not added:
        break
Rl, Cl = list(R.values()), list(C.values())
inc = [[bool(pari.issquare(r + c)) for c in Cl] for r in Rl]
for i, row in enumerate(inc):
    print(f"r{i:02d} " + "".join("#" if b else "." for b in row))
json.dump(dict(R=[str(x) for x in Rl], C=[str(x) for x in Cl]), open(f"closure_{fam}.json", "w"))
