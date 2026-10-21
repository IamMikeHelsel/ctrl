"""Fast near-biclique search on a polynomial incidence via bitsets.
For each target (m, n): minimum over m-row subsets of (sum of the n smallest per-column miss
counts), via DFS on rows with pruning.  Also exact bicliques (0 missing) of max size.
usage: fastbic.py closure.json [incidence-cache]
"""
import sys, json, os, time
from itertools import combinations
from families import pari

P = json.load(open(sys.argv[1]))
cache = sys.argv[1].replace(".json", "_inc.json")
if os.path.exists(cache):
    inc = json.load(open(cache))
else:
    R = [pari(s) for s in P["R"]]
    C = [pari(s) for s in P["C"]]
    inc = [[1 if pari.issquare(r + c) else 0 for c in C] for r in R]
    json.dump(inc, open(cache, "w"))
nR, nC = len(inc), len(inc[0])
rowbits = [sum(1 << j for j in range(nC) if inc[i][j]) for i in range(nR)]
print(f"{nR}x{nC}, density {sum(map(sum, inc))/(nR*nC):.3f}", flush=True)


def popc(x):
    return bin(x).count("1")


# exact bicliques: max n for each m via DFS over rows with common-col bitset
bestn = {}


def dfs(start, rows, common):
    m = len(rows)
    n = popc(common)
    if m >= 1:
        if n > bestn.get(m, (-1,))[0]:
            bestn[m] = (n, tuple(rows))
    if n < 3:
        return
    for i in range(start, nR):
        c2 = common & rowbits[i]
        if popc(c2) >= 3:
            dfs(i + 1, rows + [i], c2)


t = time.time()
dfs(0, [], (1 << nC) - 1)
print("exact polynomial bicliques: m -> (max n, rows):", {m: v for m, v in sorted(bestn.items()) if m >= 3}, f"{time.time()-t:.1f}s", flush=True)

# near-bicliques with at most `budget` missing entries for targets
targets = [(5, 5), (6, 4), (6, 5), (5, 6), (7, 4), (6, 6)]
for (m, n) in targets:
    best = [99, None]
    # columns-first: choose n columns, count rows missing <= ... ; use rows-DFS with bound on missing
    colmiss_cache = {}

    def rec(start, rows, misscount):
        if len(rows) == m:
            ms = sorted(misscount)
            tot = sum(ms[:n])
            if tot < best[0]:
                order = sorted(range(nC), key=lambda j: misscount[j])[:n]
                best[0], best[1] = tot, (tuple(rows), tuple(sorted(order)))
            return
        # lower bound: current sum of n smallest
        ms = sorted(misscount)
        if sum(ms[:n]) >= best[0]:
            return
        for i in range(start, nR - (m - len(rows)) + 1):
            new = [misscount[j] + (0 if inc[i][j] else 1) for j in range(nC)]
            rec(i + 1, rows + [i], new)

    t = time.time()
    rec(0, [], [0] * nC)
    print(f"{m}x{n}: min missing {best[0]} at {best[1]}  ({time.time()-t:.1f}s)", flush=True)
