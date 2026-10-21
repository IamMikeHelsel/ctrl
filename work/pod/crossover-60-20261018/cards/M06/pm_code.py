"""Exact five-bit cut-code certificate and a bounded attempt to find its obstruction."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
vertices = [i for i in range(32) if i.bit_count() % 2 == 0]
edges = [
    (i, j) for i, j in combinations(range(16), 2) if (vertices[i] ^ vertices[j]).bit_count() == 4
]
assert len(edges) == 40
assert all(
    not ((a, b) in edges and (a, c) in edges and (b, c) in edges)
    for a, b, c in combinations(range(16), 3)
)
labels = vertices
cuts = [sum(1 << i for i in range(16) if (labels[i] >> bit) & 1) for bit in range(5)]


def internal(es, mask):
    return sum(((mask >> a) & 1) == ((mask >> b) & 1) for a, b in es)


assert [internal(edges, s) for s in cuts] == [8] * 5
# Each edge agrees in exactlyone coordinate, so sumcutcosts=totaledgeweight.
for a, b in edges:
    assert sum(((s >> a) & 1) == ((s >> b) & 1) for s in cuts) == 1
best = min((internal(edges, s), s) for s in range(1 << 15))
assert best[0] == 8
# Any nonnegative edgeweights retain identity; arbitrary blowup sizes included.
weighted = []
for weights in ([1] * 16, list(range(1, 17)), [1 if i % 3 else 5 for i in range(16)]):
    costs = [
        sum(weights[a] * weights[b] for a, b in edges if ((s >> a) & 1) == ((s >> b) & 1))
        for s in cuts
    ]
    m = sum(weights[a] * weights[b] for a, b in edges)
    n = sum(weights)
    assert sum(costs) == m and 5 * min(costs) <= m
    weighted.append(
        {"sizes": weights, "n": n, "m": m, "costs": costs, "target": str(F(2 * n * n, 47))}
    )


# Mycielski(C5) thenMycielski again: a trianglefree graph in the gap.
def myc(n, es):
    out = list(es)
    for a, b in es:
        out.extend([(a, n + b), (b, n + a)])
    out.extend((n + i, 2 * n) for i in range(n))
    return 2 * n + 1, sorted({tuple(sorted(e)) for e in out})


n, es = myc(5, [(i, (i + 1) % 5) for i in range(5)])
n, es = myc(n, es)
assert n == 23 and len(es) == 71
adj = [set() for _ in range(n)]
for a, b in es:
    adj[a].add(b)
    adj[b].add(a)
assert all(not (adj[a] & adj[b]) for a, b in es)
# Exact deterministic DSATUR search, symmetrybreak only interchangeable color names.
color = [-1] * n
nodes = 0


def search(used):
    global nodes
    nodes += 1
    remaining = [i for i in range(n) if color[i] < 0]
    if not remaining:
        return True
    v = max(
        remaining, key=lambda i: (len({color[j] for j in adj[i] if color[j] >= 0}), len(adj[i]), -i)
    )
    banned = {color[j] for j in adj[v]}
    for c in range(min(used + 1, 4)):
        if c not in banned:
            color[v] = c
            if search(max(used, c + 1)):
                return True
    color[v] = -1
    return False


fourcolorable = search(0)
assert not fourcolorable
out = {
    "code_vertices": vertices,
    "code_edges": edges,
    "coordinate_cuts": cuts,
    "clebsch_optimum": best,
    "weighted_blowup_checks": weighted,
    "density_gate": "r<=20/47 gives m/5<=2n²/47; this covers the frozenmiddle interval PROVIDED validlabels exist",
    "obstruction": {
        "n": n,
        "edges": es,
        "density": str(F(2 * len(es), n * n)),
        "fourcolorable_search": fourcolorable,
        "nodes": nodes,
    },
    "scope": "Code edge identity exact, averaging proof handderived and scalar kernelhelpers separate. Search failure is not Lean proof or accepted UNSAT certificate. Code map existence is restrictive, not universal.",
}
(HERE / "pm_code.json").write_text(json.dumps(out, indent=2) + "\n")
print("Clebsch cost", best, "Mycielski nodes", nodes, "density", F(142, 529))
