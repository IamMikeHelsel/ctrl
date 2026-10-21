"""Exact two-neighborhood cut test; no solver and no source imports."""

import json
from fractions import Fraction
from pathlib import Path


def audit(name, n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert all(not (adj[u] & adj[v]) for u, v in edges)
    degree = [len(a) for a in adj]
    m = len(edges)
    cuts = []
    for v in range(n):
        s = adj[v]
        base = sum(degree[u] for u in s)
        for w in range(n):
            gains = {u: degree[u] - 2 * len(adj[u] & s) for u in adj[w] - s}
            t = {u for u, g in gains.items() if g > 0}
            cut = s | t
            actual = sum((u in cut) != (v in cut) for u, v in edges)
            predicted = base + sum(gains[u] for u in t)
            assert actual == predicted
            cuts.append((actual, v, w, sorted(cut)))
    best = max(cuts)
    optimum = max(
        (sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges), mask)
        for mask in range(1 << (n - 1))
    )
    mean = Fraction(2 * m, n)
    variance = sum((Fraction(d) - mean) ** 2 for d in degree) / n
    return {
        "name": name,
        "n": n,
        "m": m,
        "edges": edges,
        "degrees": degree,
        "density": str(Fraction(2 * m, n * n)),
        "normalized_variance": str(variance / (n * n)),
        "two_neighborhood_best": best,
        "maxcut_exhaustive": optimum,
        "route_internal": m - best[0],
        "route_excess_over_target": str(Fraction(m - best[0], n * n) - Fraction(2, 47)),
        "actual_internal": m - optimum[0],
    }


petersen = [(i, (i + 1) % 5) for i in range(5)]
petersen += [(i + 5, (i + 2) % 5 + 5) for i in range(5)]
petersen += [(i, i + 5) for i in range(5)]
clebsch = [(u, v) for u in range(16) for v in range(u + 1, 16) if (u ^ v).bit_count() in (1, 4)]
results = [audit("Petersen", 10, petersen), audit("Clebsch", 16, clebsch)]
assert results[1]["route_internal"] == 11
assert results[1]["route_excess_over_target"] == "5/12032"
Path(__file__).with_suffix(".json").write_text(json.dumps(results, indent=2) + "\n")
print([(r["name"], r["route_internal"], r["actual_internal"]) for r in results])
