"""Clebsch seed-neighborhood splitting, independently labeled by odd five-bit words."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
words = [word for word in range(32) if word.bit_count() % 2 == 1]
edges = [(i, j) for i, j in combinations(range(16), 2) if (words[i] ^ words[j]).bit_count() == 4]
adj = [set() for _ in words]
for i, j in edges:
    adj[i].add(j)
    adj[j].add(i)
assert len(edges) == 40 and list(map(len, adj)) == [5] * 16
assert all(not (adj[i] & adj[j]) for i, j in edges)
seed = words.index(1)
neighborhood = adj[seed]
records = {
    str(j): {
        "count": 0,
        "max_cross": -1,
        "witness_words": None,
        "max_cross_seed_out": -1,
        "witness_seed_out_words": None,
        "cost_spectrum": {},
    }
    for j in range(6)
}
for mask in range(1 << 16):
    selected = {i for i in range(16) if mask & (1 << i)}
    k = len(selected & neighborhood)
    crossing = sum((u in selected) != (v in selected) for u, v in edges)
    record = records[str(k)]
    record["count"] += 1
    cost = str(40 - crossing)
    record["cost_spectrum"][cost] = record["cost_spectrum"].get(cost, 0) + 1
    if crossing > record["max_cross"]:
        record["max_cross"] = crossing
        record["witness_words"] = [words[i] for i in sorted(selected)]
    if seed not in selected and crossing > record["max_cross_seed_out"]:
        record["max_cross_seed_out"] = crossing
        record["witness_seed_out_words"] = [words[i] for i in sorted(selected)]
assert sum(row["count"] for row in records.values()) == 1 << 16
target = F(2 * 16**2, 47)
needed_cross = 30
assert 40 - needed_cross <= target < 40 - (needed_cross - 1)
minimum_split = min(5 - int(k) for k, row in records.items() if row["max_cross"] >= needed_cross)
minimum_split_seed_out = min(
    5 - int(k) for k, row in records.items() if row["max_cross_seed_out"] >= needed_cross
)
assert records["5"]["max_cross"] == 29
assert max(row["max_cross"] for row in records.values()) == 32
out = {
    "scope": "Exact finite Clebsch spectrum, not a uniform graph theorem.",
    "labels": "Odd-parity five-bit words; edge iff Hamming distance4.",
    "words": words,
    "edges_indexed": edges,
    "seed_word": 1,
    "seed_neighborhood_words": [words[i] for i in sorted(neighborhood)],
    "target_internal": str(target),
    "necessary_integer_crossing": needed_cross,
    "minimum_removed_seed_neighbors": minimum_split,
    "minimum_removed_seed_neighbors_seed_fixed_out": minimum_split_seed_out,
    "spectrum_by_retained_neighbor_count": records,
}
(HERE / "inventor_seed_split.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            k: v
            for k, v in out.items()
            if k not in ("edges_indexed", "spectrum_by_retained_neighbor_count")
        },
        indent=2,
    )
)
print(
    json.dumps(
        {
            k: {key: val for key, val in row.items() if key != "cost_spectrum"}
            for k, row in records.items()
        },
        indent=2,
    )
)

# An explicit motif attains the optimum; no residual subset optimization needed.
edge_motifs = []
for v, w in edges:
    left, right = adj[v] - {w}, adj[w] - {v}
    assert not left & right
    assert not any(a in left and b in left for a, b in edges)
    assert not any(a in right and b in right for a, b in edges)
    selected = left | right
    between = sum((a in left and b in right) or (a in right and b in left) for a, b in edges)
    cross = sum((a in selected) != (b in selected) for a, b in edges)
    assert cross == sum(len(adj[u]) for u in selected) - 2 * between
    assert between == 4 and cross == 32
    edge_motifs.append(
        {
            "edge_words": [words[v], words[w]],
            "selected_words": sorted(words[u] for u in selected),
            "four_cycles_through_edge": between,
            "crossing": cross,
        }
    )
# Double-counting identity for average edge-motif crossing.
four_cycle_count = sum(row["four_cycles_through_edge"] for row in edge_motifs) // 4
average_numerator = (
    2 * sum(len(adj[v]) * len(adj[w]) for v, w in edges)
    - sum(len(a) ** 2 for a in adj)
    - 8 * four_cycle_count
)
assert average_numerator == sum(row["crossing"] for row in edge_motifs)
out["adjacent_edge_motifs"] = edge_motifs
out["four_cycle_count"] = four_cycle_count
out["edge_motif_crossing_sum"] = average_numerator
(HERE / "inventor_seed_split.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    "All40 adjacent-edge endpoint-removed neighborhood cuts attain crossing32; C4 count",
    four_cycle_count,
)
