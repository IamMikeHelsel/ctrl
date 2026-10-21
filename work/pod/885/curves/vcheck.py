"""Verify V-configurations from vsearch.py and look for polynomial 4x4 / 5x4 extensions.

For each CFG: columns C1, C2, 0; complete row set R (polyrows, degree<=4); then all columns X
valid on >= 3 rows of R (polyrows on the transposed problem).  Reports the best new column
(number of rows hit) - a column hitting k rows gives a polynomial k x 4 grid.
usage: vcheck.py logfile [maxcfg]
"""
import sys, json, re
from families import pari
from polyrows import poly_rows

X = pari("x")


def cols_of(d, u, c1, c2):
    d, u, c1, c2 = map(pari, (d, u, c1, c2))
    C1 = c1 * (X ** 2 - 1) * (X ** 2 - d ** 2)
    C2 = c2 * (X ** 2 - u ** 2) * (X ** 2 - d ** 2 / u ** 2)
    return C1, C2


def analyse(C1, C2):
    V = [C1, C2, pari(0)]
    R = poly_rows(V, 2)
    rows = [Xr for k, (Xr, s) in R.items() if len(s) == 3]
    out = {"nrows": len(rows), "rows": [str(r) for r in rows]}
    if len(rows) < 3:
        return out
    Cc = poly_rows(rows, 2)
    known = {str(C1), str(C2), "0"}
    best = []
    for k, (Xc, s) in Cc.items():
        if str(Xc) in known:
            continue
        best.append((len(s), str(Xc), sorted(s)))
    best.sort(key=lambda t: -t[0])
    from itertools import combinations
    tri = {}
    for (n_, xc, ss) in best:
        for T in combinations(ss, 3):
            tri[T] = tri.get(T, 0) + 1
    out["maxtriple"] = 3 + max(tri.values()) if tri else 3
    out["newcols"] = best[:5]
    out["maxhit"] = best[0][0] if best else 0
    return out


if __name__ == "__main__":
    lines = [l for l in open(sys.argv[1]) if l.startswith("CFG")]
    maxc = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    seen = set()
    res = []
    for l in lines[:maxc]:
        if "o1=" in l:
            kv = dict(re.findall(r"(\w+)=(\S+)", re.sub(r"\[.*?\]", "", l)))
            o1 = re.search(r"o1=\[(.*?)\]", l).group(1).replace("'", "").split(", ")
            o2 = re.search(r"o2=\[(.*?)\]", l).group(1).replace("'", "").split(", ")
            C1 = pari(kv["c1"]) * pari.prod if False else pari(kv["c1"])
            for r in o1: C1 = C1 * (X - pari(r))
            C2 = pari(kv["c2"])
            for r in o2: C2 = C2 * (X - pari(r))
            kv["d"] = kv.get("a"); kv["u"] = "|".join(o1) + "/" + "|".join(o2)
        else:
            kv = dict(re.findall(r"(\w+)=(\S+)", l))
            C1, C2 = cols_of(kv["d"], kv["u"], kv["c1"], kv["c2"])
        key = (str(C1), str(C2))
        if key in seen:
            continue
        seen.add(key)
        try:
            o = analyse(C1, C2)
        except Exception as e:
            print("ERR", l.strip(), str(e)[:80], flush=True)
            continue
        o.update(kv)
        res.append(o)
        tag = "  <<< 5x4!" if o.get("maxhit", 0) >= 5 else ("  <4x4>" if o.get("maxhit", 0) >= 4 else "")
        print(f"d={kv['d']} u={kv['u']} c1={kv['c1']} c2={kv['c2']}: rows {o['nrows']} maxhit {o.get('maxhit')} cols-on-best-triple {o.get('maxtriple')}{tag}", flush=True)
    json.dump(res, open(sys.argv[1] + ".check.json", "w"))
