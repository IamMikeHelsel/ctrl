"""Moebius-invariant fingerprint of a polynomial grid: multiset of j-invariants of the genus-1
curves y^2 = C_i - C_j (column pairs) and y^2 = R_i - R_j (row pairs, R = a^2).
Also writes the full polynomial closure (rows over {0,C1,C2}, columns with >= 4 hits) as JSON.
usage: vinv.py poly77_lagrange.json | vinv.py CFGLOG LINENO OUT.json
"""
import sys, json, re
from itertools import combinations
from families import pari
from polyrows import poly_rows

X = pari("x")


def closure(C1, C2):
    R = poly_rows([C1, C2, pari(0)], 2)
    rows = [Xr for _, (Xr, s) in R.items() if len(s) == 3]
    Cc = poly_rows(rows, 2)
    cols = [pari(0), C1, C2]
    for _, (Xc, s) in Cc.items():
        if len(s) >= 4 and all(Xc != c for c in cols):
            cols.append(Xc)
    return rows, cols


def jinv(f):
    a, b, c, d, e = [pari.polcoef(f, k) for k in (4, 3, 2, 1, 0)]
    I = 12 * a * e - 3 * b * d + c * c
    J = 72 * a * c * e + 9 * b * c * d - 27 * a * d * d - 27 * e * b * b - 2 * c ** 3
    A, B = -27 * I, -27 * J
    den = 4 * A ** 3 + 27 * B ** 2
    return "sing" if den == 0 else str(1728 * 4 * A ** 3 / den)


def fingerprint(R, C):
    jc = sorted(jinv(a - b) for a, b in combinations(C, 2))
    jr = sorted(jinv(a - b) for a, b in combinations(R, 2))
    return jc, jr


if __name__ == "__main__":
    if sys.argv[1].endswith(".json"):
        d = json.load(open(sys.argv[1]))
        R = [pari(r) for r in d["R"]]
        C = [pari(c) for c in d["C"]]
    else:
        l = [l for l in open(sys.argv[1]) if l.startswith("CFG")][int(sys.argv[2])]
        kv = dict(re.findall(r"(\w+)=(\S+)", re.sub(r"\[.*?\]", "", l)))
        o1 = re.search(r"o1=\[(.*?)\]", l).group(1).replace("'", "").split(", ")
        o2 = re.search(r"o2=\[(.*?)\]", l).group(1).replace("'", "").split(", ")
        C1, C2 = pari(kv["c1"]), pari(kv["c2"])
        for r in o1:
            C1 = C1 * (X - pari(r))
        for r in o2:
            C2 = C2 * (X - pari(r))
        R, C = closure(C1, C2)
        miss = [[i, j] for i, r in enumerate(R) for j, c in enumerate(C)
                if not pari.issquare(r + c)]
        json.dump({"R": [str(r) for r in R], "C": [str(c) for c in C], "miss": miss},
                  open(sys.argv[3], "w"), indent=1)
        print("closure", len(R), "x", len(C), "missing incidences", len(miss))
    jc, jr = fingerprint(R, C)
    print("cols j:", jc)
    print("rows j:", jr)
