"""Two complementary edge-rooted cuts and exact C4 cancellation on finite graphs."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent


def check(n, es):
    adj = [set() for _ in range(n)]
    for a, b in es:
        adj[a].add(b)
        adj[b].add(a)
    assert all(not adj[a] & adj[b] for a, b in es)
    m = len(es)
    if not m:
        return None
    deg = list(map(len, adj))
    s2 = sum(d * d for d in deg)
    prod = sum(deg[a] * deg[b] for a, b in es)
    c4 = (
        sum(
            len(adj[a] & adj[b]) * (len(adj[a] & adj[b]) - 1) // 2
            for a, b in combinations(range(n), 2)
        )
        // 2
    )
    us = []
    fs = []
    for v, w in es:
        A = adj[v] - {w}
        B = adj[w] - {v}
        S = A | B
        squares = sum(a in adj[b] for a in A for b in B)
        crossing = sum((a in S) != (b in S) for a, b in es)
        assert crossing == sum(deg[a] for a in S) - 2 * squares
        us.append(crossing)
        eAB = sum(a in adj[b] for a in adj[v] for b in adj[w])
        assert eAB == deg[v] + deg[w] - 1 + squares
        fs.append(F(m + eAB, 2))
    assert sum(us) == 2 * prod - s2 - 8 * c4
    assert sum(fs) == F(m * m + s2 - m + 4 * c4, 2)
    mixture = F(4, 5) * sum(fs) / m + F(1, 5) * sum(us) / m
    assert mixture == F(2 * m, 5) - F(2, 5) + F(s2 + 2 * prod, 5 * m)
    return {
        "n": n,
        "m": m,
        "C4": c4,
        "best_open_union_crossing": max(us),
        "best_opposed_expected_crossing": str(max(fs)),
        "mixture_internal_bound": str(m - mixture),
        "target": str(F(2 * n * n, 47)),
    }


count = 0
for n in range(1, 7):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        es = [e for i, e in enumerate(pairs) if mask >> i & 1]
        adj = [0] * n
        for a, b in es:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
        if any(adj[a] & adj[b] for a, b in es):
            continue
        check(n, es)
        count += 1
j = json.loads((HERE / "pm_code.json").read_text())
out = {
    "exhaustive_labelled_trianglefree_n1to6": count,
    "clebsch": check(16, j["code_edges"]),
    "mycielski23": check(23, j["obstruction"]["edges"]),
    "scope": "Exact finite checks and hand graph-count identities. C4 cancellation is a candidate multiplier constraint, not a universal2/47 bound. Opposed rooted cut uses fair independent assignment for leftover vertices; its expected crossing is not an actual integer cut witness.",
}
(HERE / "pm_edgecuts.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
