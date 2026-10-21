"""Convert vinv.py closure JSON (miss as list) into grid77.py's poly77_<fam>.json format."""
import sys, json
from families import pari
from famext import gp_sqfree
d = json.load(open(sys.argv[1]))
R = [pari(s) for s in d["R"]]
C = [pari(s) for s in d["C"]]
miss = {}
for i, r in enumerate(R):
    for j, c in enumerate(C):
        if not pari.issquare(r + c):
            c0, F = gp_sqfree(r + c)
            miss[f"{i},{j}"] = str(c0 * F)
            print(i, j, pari.factor(c0 * F))
json.dump(dict(R=d["R"], C=d["C"], miss=miss), open(sys.argv[2], "w"))
