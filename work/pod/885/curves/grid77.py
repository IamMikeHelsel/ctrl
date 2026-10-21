"""Scan x for the polynomial 7x7 Lagrange incidence.

poly77_<fam>.json: 7 polynomial rows R, 7 polynomial cols C, and the quartics of the 15 missing
entries.  Each worker takes some missing entries, generates x with that quartic square
(hyperellratpoints up to H, plus group-law box N on its Weierstrass model), evaluates all
15 conditions at x, and reports the largest nondegenerate subgrids (exactly verified).
usage: grid77.py fam worker nworkers H N
"""
import sys, json
from fractions import Fraction as Fr
from itertools import combinations, product
from families import pari
from known import is_sq
from verify_grid import check_grid, integer_form
from ellquartic import weier

fam, W, NW, H, NB = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
P = json.load(open(f"poly77_{fam}.json"))
R = [pari(s) for s in P["R"]]
C = [pari(s) for s in P["C"]]
MISS = {tuple(map(int, k.split(","))): pari(v) for k, v in P["miss"].items()}
keys = sorted(MISS)
mine = keys[W::NW]
log = open(f"logs/grid77_{fam}_w{W}_H{H}_N{NB}.log", "a")


def L(s):
    log.write(s + "\n")
    log.flush()


def fr(g):
    return Fr(int(pari.numerator(g)), int(pari.denominator(g)))


def ev(g, x):
    return fr(pari.subst(g, "x", pari(f"{x.numerator}/{x.denominator}")))


BEST = {}


def analyse(x):
    xp = pari(f"{x.numerator}/{x.denominator}")
    sat = {k for k in keys if pari.issquare(pari.subst(MISS[k], "x", xp))}
    if len(sat) < 2:
        return
    Rx = [ev(g, x) for g in R]
    Cx = [ev(g, x) for g in C]
    ok = lambda i, j: (i, j) not in MISS or (i, j) in sat
    found = []
    for rs in range(7, 3, -1):
        for rows in combinations(range(7), rs):
            cols = [j for j in range(7) if all(ok(i, j) for i in rows)]
            if len(cols) < 4:
                continue
            for cs in range(len(cols), 3, -1):
                done = False
                for csub in combinations(cols, cs):
                    UU = [Rx[i] for i in rows]
                    VV = [Cx[j] for j in csub]
                    try:
                        check_grid(UU, VV); integer_form(UU, VV); integer_form(VV, UU)
                    except (AssertionError, ZeroDivisionError):
                        continue
                    found.append((rs, cs, rows, csub, UU, VV))
                    done = True
                    break
                if done:
                    break
    if not found:
        return
    shapes = sorted({(max(a, b), min(a, b)) for a, b, *_ in found}, reverse=True)
    top = [f for f in found if (max(f[0], f[1]), min(f[0], f[1])) in shapes[:3]]
    for rs, cs, rows, csub, UU, VV in top:
        if rs * cs >= 24 or (rs >= 5 and cs >= 5):
            L(f"GRID {rs}x{cs} x={x} rows={rows} cols={csub} " + json.dumps(dict(U=[str(a) for a in UU], V=[str(b) for b in VV])))
    L(f"x={x} sat={sorted(sat)} shapes={shapes[:4]}")


seen = set()
for k in mine:
    g = MISS[k]
    xs = set()
    for p in pari.hyperellratpoints(g, H):
        xs.add(fr(p[0]))
    L(f"# entry {k}: {len(xs)} small points (H={H})")
    if NB > 0:
        c0 = pari(1)
        w = weier(c0, g)
        if w is not None:
            E, to_x = w
            r = pari.ellrank(E)
            gens = list(pari.ellsaturation(E, r[3], 100)) if len(r[3]) else []
            L(f"# entry {k}: rank {r[0]}..{r[1]}, {len(gens)} gens")
            for n in product(range(-NB, NB + 1), repeat=len(gens)):
                nz = [c for c in n if c]
                if not nz or nz[0] < 0:
                    continue
                Pt = [0]
                for c, G in zip(n, gens):
                    if c:
                        Pt = pari.elladd(E, Pt, pari.ellmul(E, G, c))
                if len(Pt) > 1:
                    xv = to_x(Pt)
                    if xv is not None:
                        xs.add(xv)
    for x in xs:
        if x in seen:
            continue
        seen.add(x)
        analyse(x)
    L(f"# entry {k} done, {len(xs)} x")
L("# done")
