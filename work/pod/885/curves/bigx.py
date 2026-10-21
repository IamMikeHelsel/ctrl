"""Large-height x search for a 1-parameter family: for each low-degree extension condition
y^2 = c*F(x) (quartic), map to Weierstrass form, generate points by the group law in a box over an
ellrank basis, and test every x against all other conditions; report 6x4 / 4x6 / 5x5 / bigger.

Quartic -> cubic (monic quartic y^2 = x^4+bx^3+cx^2+dx+e):
  t = y - x^2 - b x/2,  S = 2(b^2/4+2t-c) x + (b t - d),  T = -2t,
  E: S^2 = T^3 + c T^2 + (bd-4e) T + (d^2 + b^2 e - 4ce);
  inverse: t=-T/2, x = (S-(bt-d)) / (2(b^2/4+2t-c)).
usage: bigx.py FAMILY subs box N
"""
import sys, json
from fractions import Fraction as Fr
from itertools import product
from families import pari, load
from lowdeg import new_rows
from known import is_sq
from verify_grid import check_grid, integer_form

fam = sys.argv[1]
subs = dict(kv.split("=") for kv in sys.argv[2].split(","))
box = int(sys.argv[3])
NB = int(sys.argv[4])
log = open(f"logs/bigx_{fam}_{sys.argv[2].replace('=','').replace(',','_')}_N{NB}.log", "a")


def L(s):
    print(s, flush=True)
    log.write(s + "\n")
    log.flush()


def fr(g):
    return Fr(int(pari.numerator(g)), int(pari.denominator(g)))


U, V = load(fam, subs)
rows = new_rows(U, V, box)
cols = new_rows(V, U, box)
elems = [("row", i, d) for i, d in enumerate(rows)] + [("col", j, d) for j, d in enumerate(cols)]
L(f"# {fam} {subs}: {len(rows)} rows, {len(cols)} cols")


def valid(d, x):
    xp = pari(f"{x.numerator}/{x.denominator}")
    return all(pari.issquare(pari.subst(c * G, "x", xp)) for c, G in d["conds"])


def ev(g, x):
    return fr(pari.subst(g, "x", pari(f"{x.numerator}/{x.denominator}")))


from ellquartic import weier


for kind, idx, d in elems:
    c0, Fp = d["conds"][0]
    if int(pari.poldegree(Fp)) != 4:
        continue
    w = weier(c0, Fp)
    if w is None:
        L(f"# {kind}{idx}: no point")
        continue
    E, to_x = w
    r = pari.ellrank(E)
    gens = list(pari.ellsaturation(E, r[3], 100)) if len(r[3]) else []
    L(f"# {kind}{idx}: rank {r[0]}..{r[1]} gens {len(gens)}")
    seen = set()
    nvalid = 0
    for n in product(range(-NB, NB + 1), repeat=len(gens)):
        nz = [k for k in n if k]
        if not nz or nz[0] < 0:
            continue
        P = [0]
        for k, G in zip(n, gens):
            if k:
                P = pari.elladd(E, P, pari.ellmul(E, G, k))
        for tor in [P]:
            x = to_x(tor) if len(tor) > 1 else None
            if x is None or x in seen:
                continue
            seen.add(x)
            if not valid(d, x):
                continue
            nvalid += 1
            # partners
            pr = [(k2, i2) for (k2, i2, d2) in elems if (k2, i2) != (kind, idx) and valid(d2, x)]
            if pr:
                Ux = [ev(g, x) for g in U]
                Vx = [ev(g, x) for g in V]
                allr = [i for k2, i in [(kind, idx)] + pr if k2 == "row"]
                allc = [i for k2, i in [(kind, idx)] + pr if k2 == "col"]
                Rx = [ev(rows[i]["X"], x) for i in allr]
                Cx = [ev(cols[j]["X"], x) for j in allc]
                cross = [(a, b) for a in range(len(Rx)) for b in range(len(Cx)) if is_sq(Rx[a] + Cx[b])]
                L(f"PARTNERS x={x} hx={max(abs(x.numerator), x.denominator).bit_length()}b {kind}{idx} with {pr} cross={cross}")
                for tag, UU, VV in [("rows", Ux + Rx, Vx), ("cols", Ux, Vx + Cx)]:
                    try:
                        if len(UU) + len(VV) > 9:
                            check_grid(UU, VV); integer_form(UU, VV); integer_form(VV, UU)
                            L(f"GRID {len(UU)}x{len(VV)} x={x} " + json.dumps(dict(U=[str(a) for a in UU], V=[str(b) for b in VV])))
                    except (AssertionError, ZeroDivisionError) as e:
                        L(f"  degenerate {tag}: {str(e)[:60]}")
                for a, b in cross:
                    UU, VV = Ux + [Rx[a]], Vx + [Cx[b]]
                    try:
                        check_grid(UU, VV); integer_form(UU, VV); integer_form(VV, UU)
                        L(f"GRID 5x5 x={x} " + json.dumps(dict(U=[str(a) for a in UU], V=[str(b) for b in VV])))
                    except (AssertionError, ZeroDivisionError) as e:
                        L(f"  degenerate 5x5: {str(e)[:60]}")
    L(f"# {kind}{idx}: {len(seen)} x tested, {nvalid} valid")
L("# done")
