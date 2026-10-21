"""Sweep 1-parameter specialisations of 4x4 families; for each, find low-degree group-law
extensions, their rational x-sets, and all combined grids (6x4, 4x6, 5x5, 7x4, 6x5, ...).
Every 5x4 obtained is also pushed through numeric extension (numext, box N=1).

usage: famsweep.py JOBFILE WORKER NWORKERS
JOBFILE lines: FAMILY|subs|box|H
"""
import sys, json, time, traceback
from fractions import Fraction as Fr
from itertools import combinations
from families import pari, load
from lowdeg import new_rows
from known import is_sq
from verify_grid import check_grid, integer_form
from numext import extend

jobs = [l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith("#")]
W, NW = int(sys.argv[2]), int(sys.argv[3])
jobs = jobs[W::NW]
log = open(f"logs/famsweep_{sys.argv[1].split('/')[-1]}_w{W}.log", "a")


def L(s):
    log.write(s + "\n")
    log.flush()


def tofr(g):
    return Fr(int(pari.numerator(g)), int(pari.denominator(g)))


def ev(g, x):
    return tofr(pari.subst(g, "x", pari(f"{x.numerator}/{x.denominator}")))


def xset(conds, H):
    c0, Fp = conds[0]
    pts = pari.hyperellratpoints(c0 * Fp, H)
    xs = set()
    for p in pts:
        x = p[0]
        if all(pari.issquare(pari.subst(c * G, "x", x)) for c, G in conds[1:]):
            xs.add(tofr(x))
    return xs


def grid_at(U, V, rows, cols, x, ri, cj):
    Ux = [ev(g, x) for g in U] + [ev(rows[i]["X"], x) for i in ri]
    Vx = [ev(g, x) for g in V] + [ev(cols[j]["X"], x) for j in cj]
    try:
        check_grid(Ux, Vx)
        integer_form(Ux, Vx)
        integer_form(Vx, Ux)
    except (AssertionError, ZeroDivisionError):
        return None
    return Ux, Vx


def emit(tag, x, g, extra=""):
    L(f"GRID {tag} x={x} {extra} " + json.dumps(dict(U=[str(a) for a in g[0]], V=[str(b) for b in g[1]])))


def run(fam, subs, box, H):
    U, V = load(fam, subs)
    rows = new_rows(U, V, box)
    cols = new_rows(V, U, box)
    RX = [xset(d["conds"], H) for d in rows]
    CX = [xset(d["conds"], H) for d in cols]
    L(f"# {fam} {subs} box={box} H={H}: rows {[len(s) for s in RX]} cols {[len(s) for s in CX]}")
    nr, nc = len(rows), len(cols)
    # all subsets of new rows / new cols sharing x
    allx = {}
    for i, s in enumerate(RX):
        for x in s:
            allx.setdefault(x, [set(), set()])[0].add(i)
    for j, s in enumerate(CX):
        for x in s:
            allx.setdefault(x, [set(), set()])[1].add(j)
    n54 = 0
    for x, (ri, cj) in allx.items():
        ri, cj = sorted(ri), sorted(cj)
        # largest grids first: try all rows + cols, then subsets compatible with cross terms
        Ux = [ev(g, x) for g in U]
        Vx = [ev(g, x) for g in V]
        try:
            check_grid(Ux, Vx)
        except AssertionError:
            continue
        R = {}
        for i in ri:
            r = ev(rows[i]["X"], x)
            if r not in Ux and r not in R.values():
                R[i] = r
        C = {}
        for j in cj:
            c = ev(cols[j]["X"], x)
            if c not in Vx and c not in C.values():
                C[j] = c
        # remove rows equal to each other / degenerate handled by grid_at
        if len(R) >= 2:
            for k in range(len(R), 1, -1):
                for sub in combinations(R, k):
                    g = grid_at(U, V, rows, cols, x, list(sub), [])
                    if g:
                        emit(f"{4+k}x4", x, g, f"{fam} {subs} rows{sub}")
                        break
        if len(C) >= 2:
            for k in range(len(C), 1, -1):
                for sub in combinations(C, k):
                    g = grid_at(U, V, rows, cols, x, [], list(sub))
                    if g:
                        emit(f"4x{4+k}", x, g, f"{fam} {subs} cols{sub}")
                        break
        for i in R:
            for j in C:
                if is_sq(R[i] + C[j]):
                    g = grid_at(U, V, rows, cols, x, [i], [j])
                    if g:
                        emit("5x5", x, g, f"{fam} {subs} row{i} col{j}")
        # numeric extension of each 5x4 at this x
        for i in list(R)[:2] + [None] + list(C)[:2]:
            pass
        for i in R:
            g = grid_at(U, V, rows, cols, x, [i], [])
            if not g:
                continue
            n54 += 1
            o = extend(g[0], g[1], 1)
            if o["rows"] or o["cols"]:
                L(f"NUMEXT x={x} row{i}: +{len(o['rows'])} rows +{len(o['cols'])} cols grids={[(a, len(b), len(c)) for a, b, c in o['grids']]}")
                for r in o["rows"]:
                    emit("6x4num", x, (g[0] + [r], g[1]), f"{fam} {subs}")
                for c in o["cols"]:
                    emit("5x5num", x, (g[0], g[1] + [c]), f"{fam} {subs}")
        for j in C:
            g = grid_at(U, V, rows, cols, x, [], [j])
            if not g:
                continue
            n54 += 1
            o = extend(g[0], g[1], 1)
            if o["rows"] or o["cols"]:
                L(f"NUMEXT x={x} col{j}: +{len(o['rows'])} rows +{len(o['cols'])} cols")
                for r in o["rows"]:
                    emit("5x5num", x, (g[0] + [r], g[1]), f"{fam} {subs}")
                for c in o["cols"]:
                    emit("4x6num", x, (g[0], g[1] + [c]), f"{fam} {subs}")
    L(f"# done {fam} {subs}: {n54} nondegenerate 5x4/4x5 grids pushed through numext")


for job in jobs:
    fam, subs, box, H = job.split("|")
    subs = dict(kv.split("=") for kv in subs.split(","))
    t = time.time()
    try:
        run(fam, subs, int(box), int(H))
    except Exception:
        L("# ERROR " + job + " " + traceback.format_exc().replace("\n", " | ")[-400:])
    L(f"# time {time.time()-t:.1f} {job}")
