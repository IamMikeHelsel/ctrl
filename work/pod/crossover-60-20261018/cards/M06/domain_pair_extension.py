"""Predeclared next motif: two independent neighborhoods, exact edge penalties."""

import json
from pathlib import Path

n = 16
edges = [(u, v) for u in range(n) for v in range(u + 1, n) if (u ^ v).bit_count() in (1, 4)]
adj = [{v for v in range(n) if (u ^ v).bit_count() in (1, 4)} for u in range(n)]
s = adj[0]  # vertex transitivity is not needed for the positive witness.
best = (25, None)
checks = 0
for w in range(n):
    for z in range(w + 1, n):
        candidates = sorted((adj[w] | adj[z]) - s)
        for mask in range(1 << len(candidates)):
            t = {u for j, u in enumerate(candidates) if mask >> j & 1}
            gains = sum(5 - 2 * len(adj[u] & s) for u in t)
            penalty = 2 * sum(u in t and v in t for u, v in edges)
            cut = s | t
            actual = sum((u in cut) != (v in cut) for u, v in edges)
            assert actual == 25 + gains - penalty
            checks += 1
            if actual > best[0]:
                best = (
                    actual,
                    {
                        "roots": [0, w, z],
                        "T": sorted(t),
                        "S_union_T": sorted(cut),
                        "gain": gains,
                        "penalty": penalty,
                    },
                )
result = {
    "checks": checks,
    "best_cross": best[0],
    "witness": best[1],
    "scope": "One finite Clebsch fixture; no universal guarantee.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result)
outside = sorted(set(range(n)) - s)
completion = []
for mask in range(1 << len(outside)):
    cut = s | {u for j, u in enumerate(outside) if mask >> j & 1}
    completion.append(sum((u in cut) != (v in cut) for u, v in edges))
result["all_supersets_of_N0"] = {"count": len(completion), "max_cross": max(completion)}
assert max(completion) == 29
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result["all_supersets_of_N0"])
