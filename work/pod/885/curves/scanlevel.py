"""Scan a polynomial closure level: x-points (complete up to height H) of every missing entry's
quartic, inverted to x -> satisfied entries, then exact grid extraction at each x.
usage: scanlevel.py closure.json H NPROC
"""
import sys, json, os, time
from fractions import Fraction as Fr
from multiprocessing import Pool

PATH, H, NP = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
TAG = os.path.basename(PATH).replace(".json", "")
LOG = f"logs/scan_{TAG}_H{H}.log"


def init():
    global pari, R, C, gp_sqfree
    from families import pari as p
    from famext import gp_sqfree as g
    pari, gp_sqfree = p, g
    P = json.load(open(PATH))
    R = [pari(s) for s in P["R"]]
    C = [pari(s) for s in P["C"]]


def work(ij):
    i, j = ij
    g = R[i] + C[j]
    if pari.issquare(g):
        return (i, j, None, [])
    c0, F = gp_sqfree(g)
    d = int(pari.poldegree(F))
    if d > 6:
        return (i, j, d, [])
    pts = pari.hyperellratpoints(c0 * F, H)
    xs = sorted({f"{pari.numerator(p[0])}/{pari.denominator(p[0])}" for p in pts})
    return (i, j, d, xs)


if __name__ == "__main__":
    init()
    nR, nC = len(R), len(C)
    t = time.time()
    with Pool(NP, initializer=init) as pool:
        res = pool.map(work, [(i, j) for i in range(nR) for j in range(nC)], chunksize=16)
    inc = [[0] * nC for _ in range(nR)]
    xmap = {}
    degs = {}
    for i, j, d, xs in res:
        if d is None:
            inc[i][j] = 1
            continue
        degs[d] = degs.get(d, 0) + 1
        for x in xs:
            xmap.setdefault(x, []).append((i, j))
    json.dump(dict(inc=inc, xmap=xmap), open(f"logs/scan_{TAG}_H{H}.json", "w"))
    log = open(LOG, "a")
    log.write(f"# {TAG} H={H}: {nR}x{nC}, degrees of missing {degs}, {len(xmap)} x values, {time.time()-t:.0f}s\n")
    multi = {x: e for x, e in xmap.items() if len(e) >= 2}
    log.write(f"# x with >=2 satisfied entries: {len(multi)}\n")
    log.flush()

    from verify_grid import check_grid, integer_form

    def fr(g):
        return Fr(int(pari.numerator(g)), int(pari.denominator(g)))

    rowbits0 = [sum(1 << j for j in range(nC) if inc[i][j]) for i in range(nR)]
    for x, ents in sorted(multi.items(), key=lambda t: -len(t[1])):
        rb = list(rowbits0)
        for (i, j) in ents:
            rb[i] |= 1 << j
        rel_rows = sorted({i for i, j in ents})
        # candidate rows: those touched plus the polynomial core; DFS bicliques
        best = []

        def dfs(start, rows, common):
            n = bin(common).count("1")
            if len(rows) >= 4 and n >= 4 and (len(rows) + n >= 10):
                best.append((tuple(rows), common))
            if n < 4:
                return
            for k in range(start, nR):
                c2 = common & rb[k]
                if bin(c2).count("1") >= 4:
                    dfs(k + 1, rows + [k], c2)

        # restrict DFS to rows touched by the extra entries plus all rows (bounded by pruning)
        dfs(0, [], (1 << nC) - 1)
        if not best:
            continue
        xp = pari(x)
        good = []
        for rows, common in sorted(best, key=lambda b: -(len(b[0]) * bin(b[1]).count("1")))[:200]:
            cols = [j for j in range(nC) if common >> j & 1]
            UU = [fr(pari.subst(R[i], "x", xp)) for i in rows]
            VV = [fr(pari.subst(C[j], "x", xp)) for j in cols]
            # drop duplicates greedily
            U2, V2 = [], []
            for u in UU:
                if u not in U2:
                    U2.append(u)
            for v in VV:
                if v not in V2:
                    V2.append(v)
            try:
                check_grid(U2, V2)
                integer_form(U2, V2); integer_form(V2, U2)
            except (AssertionError, ZeroDivisionError):
                continue
            if len(U2) >= 4 and len(V2) >= 4 and len(U2) + len(V2) >= 10:
                good.append((len(U2), len(V2), U2, V2, rows, cols))
        if good:
            m, n, U2, V2, rows, cols = max(good, key=lambda g: (min(g[0], g[1]), g[0] * g[1]))
            log.write(f"GRID {m}x{n} x={x} rows={rows} cols={cols} " + json.dumps(dict(U=[str(a) for a in U2], V=[str(b) for b in V2])) + "\n")
            log.flush()
    log.write("# done\n")
