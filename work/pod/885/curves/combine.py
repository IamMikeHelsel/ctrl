"""Combine low-degree extensions of a 1-parameter 4x4 family.

New rows R_i(x) (from column-triple curves), new columns C_j(x) (from row-triple curves).
Each has square conditions against the leftover original columns/rows.  Collect x where
each element is valid (points on y^2 = F), then look for
  6x4: two new rows valid at the same x,
  5x5: a new row and a new column valid at the same x with R+C a square,
and print any hit (exactly verified afterwards with verify_grid.py).
usage: combine.py FAMILY "subs" box H
"""
import sys, json
from fractions import Fraction as Fr
from itertools import combinations
from families import pari, load
from lowdeg import new_rows
from known import is_sq

fam = sys.argv[1]
subs = dict(kv.split("=") for kv in sys.argv[2].split(","))
box = int(sys.argv[3]) if len(sys.argv) > 3 else 1
H = int(sys.argv[4]) if len(sys.argv) > 4 else 10**4
U, V = load(fam, subs)
log = open(f"logs/combine_{fam}_{sys.argv[2].replace('=','').replace(',','_')}_b{box}.log", "a")


def L(s):
    print(s, flush=True)
    log.write(s + "\n")
    log.flush()


def tofr(g):
    return Fr(int(pari.numerator(g)), int(pari.denominator(g)))


def xset(conds):
    """Rational x with all conds square, from the first cond's points, filtered by the rest."""
    c0, F = conds[0]
    pts = pari.hyperellratpoints(c0 * F, H)
    xs = set()
    for p in pts:
        x = p[0]
        if all(pari.issquare(pari.subst(c * G, "x", x)) for c, G in conds[1:]):
            xs.add(tofr(x))
    return xs


rows = new_rows(U, V, box)
cols = new_rows(V, U, box)
L(f"# {fam} {subs} box={box} H={H}: {len(rows)} new rows, {len(cols)} new cols (low degree)")
RX = [xset(d["conds"]) for d in rows]
CX = [xset(d["conds"]) for d in cols]
for i, d in enumerate(rows):
    L(f"  row {i} T={d['T']} co={d['co']} #x={len(RX[i])}")
for j, d in enumerate(cols):
    L(f"  col {j} T={d['T']} co={d['co']} #x={len(CX[j])}")


def ev(g, x):
    return tofr(pari.subst(g, "x", pari(f"{x.numerator}/{x.denominator}")))


from verify_grid import check_grid, integer_form


def full(x, ri, cj):
    Ux = [ev(g, x) for g in U] + [ev(rows[i]["X"], x) for i in ri]
    Vx = [ev(g, x) for g in V] + [ev(cols[j]["X"], x) for j in cj]
    try:
        check_grid(Ux, Vx)
        integer_form(Ux, Vx)
        integer_form(Vx, Ux)
    except AssertionError as e:
        return None, str(e)[:80]
    return (Ux, Vx), "ok"


def report(tag, x, ri, cj):
    g, msg = full(x, ri, cj)
    if g is None:
        L(f"degenerate {tag} x={x} rows+{ri} cols+{cj}: {msg}")
    else:
        L(f"GRID {tag} x={x} " + json.dumps(dict(U=[str(a) for a in g[0]], V=[str(b) for b in g[1]])))


for i, j in combinations(range(len(rows)), 2):
    for x in RX[i] & RX[j]:
        report("6x4", x, [i, j], [])
for i, j in combinations(range(len(cols)), 2):
    for x in CX[i] & CX[j]:
        report("4x6", x, [], [i, j])
for i in range(len(rows)):
    for j in range(len(cols)):
        for x in RX[i] & CX[j]:
            report("5x5", x, [i], [j])
for k in (3,):
    for ri in combinations(range(len(rows)), k):
        for x in set.intersection(*[RX[i] for i in ri]):
            report(f"{4+k}x4", x, list(ri), [])
L("# done")
