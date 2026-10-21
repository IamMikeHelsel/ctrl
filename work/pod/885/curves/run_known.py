"""Run the two-sided extension search on every column triple of every known grid (both orientations)."""
import sys, time
from itertools import combinations
from ext import search_curve
from known import KNOWN

Nrow = int(sys.argv[1]) if len(sys.argv) > 1 else 2
K = int(sys.argv[2]) if len(sys.argv) > 2 else 16
Ncol = int(sys.argv[3]) if len(sys.argv) > 3 else 2
names = sys.argv[4].split(",") if len(sys.argv) > 4 else list(KNOWN)
log = open(f"logs/known_N{Nrow}_K{K}_M{Ncol}.log", "a")


def L(s):
    print(s, flush=True)
    log.write(s + "\n")
    log.flush()


for name in names:
    U, V = KNOWN[name]
    for orient, (A, B) in (("rows", (U, V)), ("cols", (V, U))):
        for T in combinations(range(len(B)), 3):
            t = time.time()
            L(f"## {name} {orient} triple {T}")
            search_curve([B[i] for i in T], Nrow=Nrow, K=K, Ncol=Ncol, extra_rows=A, log=L)
            L(f"## time {time.time()-t:.1f}")
