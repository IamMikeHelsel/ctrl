"""Exact cut-space and local-optimum diagnostics, not a general extremal proof."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent


def graph(name, n, edges):
    edges = sorted({tuple(sorted(e)) for e in edges})
    assert all(u != v for u, v in edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert all(not (adj[u] & adj[v]) for u, v in edges)
    cuts = []
    for mask in range(1 << (n - 1)):
        internal = sum(((mask >> u) & 1) == ((mask >> v) & 1) for u, v in edges)
        cuts.append(internal)
    best = min(cuts)
    local = []
    for mask, internal in enumerate(cuts):
        signs = [(mask >> u) & 1 for u in range(n)]
        deltas = [sum(1 if signs[u] != signs[v] else -1 for v in adj[u]) for u in range(n)]
        if min(deltas) >= 0:
            local.append({"mask": mask, "cost": internal, "one_flip_changes": deltas})
    # Enumerate simple odd cycles as edge sets, removing traversal duplicates.
    cycle_masks = set()
    edge_index = {e: i for i, e in enumerate(edges)}

    def extend(path):
        for v in adj[path[-1]]:
            if v == path[0] and len(path) >= 3 and len(path) % 2:
                es = [tuple(sorted((path[i], path[(i + 1) % len(path)]))) for i in range(len(path))]
                cycle_masks.add(sum(1 << edge_index[e] for e in es))
            elif v > path[0] and v not in path:
                extend(path + [v])

    for u in range(n):
        extend([u])
    cycle_masks = sorted(cycle_masks)
    # Every odd cycle must contain an internal edge, for each actual cut.
    for mask in range(1 << (n - 1)):
        internal_mask = sum(
            1 << i for i, (u, v) in enumerate(edges) if ((mask >> u) & 1) == ((mask >> v) & 1)
        )
        for cyc in cycle_masks:
            assert (internal_mask & cyc).bit_count() % 2 == 1
    disjoint = next(((a, b) for a, b in combinations(cycle_masks, 2) if not a & b), None)
    # Lower bound certificate 2 if two edge-disjoint odd cycles exist.
    if disjoint:
        assert best >= 2
    worst_local = max(local, key=lambda item: item["cost"])
    return {
        "name": name,
        "n": n,
        "edges": edges,
        "degree_sequence": list(map(len, adj)),
        "density_r": str(F(2 * len(edges), n * n)),
        "target": str(F(2 * n * n, 47)),
        "global_internal_cost": best,
        "best_cut": cuts.index(best),
        "neighbor_best": min(len(edges) - sum(len(adj[u]) for u in adj[v]) for v in range(n)),
        "local_optima_count": len(local),
        "worst_one_flip_local": worst_local,
        "odd_cycle_edge_masks": cycle_masks,
        "two_edge_disjoint_odd_cycles": disjoint,
        "cut_count_mod_complement": len(cuts),
    }


cube = graph("cube Q3", 8, [(u, u ^ (1 << bit)) for u in range(8) for bit in range(3)])
wagner = graph(
    "Wagner M8", 8, [(u, (u + 1) % 8) for u in range(8)] + [(u, u + 4) for u in range(4)]
)
petersen = graph(
    "Petersen",
    10,
    [(u, (u + 1) % 5) for u in range(5)]
    + [(u + 5, (u + 2) % 5 + 5) for u in range(5)]
    + [(u, u + 5) for u in range(5)],
)
assert cube["degree_sequence"] == wagner["degree_sequence"] == [3] * 8
assert cube["global_internal_cost"] == 0
assert wagner["global_internal_cost"] == 2
assert petersen["global_internal_cost"] == 3
out = {
    "scope": "Finite exact diagnostic; graph cuts are unbalanced unless specifically counted otherwise.",
    "graphs": [cube, wagner, petersen],
}
(HERE / "inventor_graph.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        [
            {k: v for k, v in g.items() if k not in ("odd_cycle_edge_masks", "edges")}
            for g in out["graphs"]
        ],
        indent=2,
    )
)

# Explicit subset-flip identity and smallest strictly improving move.
for g in out["graphs"]:
    n, edges = g["n"], g["edges"]
    mask = g["worst_one_flip_local"]["mask"]
    old_cost = g["worst_one_flip_local"]["cost"]
    delta = g["worst_one_flip_local"]["one_flip_changes"]
    minima = []
    for size in range(1, n + 1):
        candidates = []
        for subset in combinations(range(n), size):
            selected = set(subset)
            changed = mask ^ sum(1 << u for u in subset)
            new_cost = sum(((changed >> u) & 1) == ((changed >> v) & 1) for u, v in edges)
            internal_sub = sum(
                u in selected and v in selected and ((mask >> u) & 1) == ((mask >> v) & 1)
                for u, v in edges
            )
            crossed_sub = sum(
                u in selected and v in selected and ((mask >> u) & 1) != ((mask >> v) & 1)
                for u, v in edges
            )
            assert (
                new_cost - old_cost
                == sum(delta[u] for u in subset) + 2 * internal_sub - 2 * crossed_sub
            )
            candidates.append((new_cost - old_cost, subset))
        best_delta, witness = min(candidates)
        minima.append({"size": size, "best_cost_change": best_delta, "witness": witness})
    g["subset_flip_minima"] = minima
    # Uniform fractional odd-cycle packing, a valid lower bound on internal cost.
    cycles = g["odd_cycle_edge_masks"]
    counts = [sum(bool(cycle & (1 << i)) for cycle in cycles) for i in range(len(edges))]
    if cycles:
        packing = F(len(cycles), max(counts))
        assert g["global_internal_cost"] >= packing
        g["uniform_odd_cycle_packing"] = {
            "count": len(cycles),
            "max_edge_load": max(counts),
            "lower_bound": str(packing),
        }
(HERE / "inventor_graph.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        [
            {
                "name": g["name"],
                "flips": g["subset_flip_minima"][:4],
                "packing": g.get("uniform_odd_cycle_packing"),
            }
            for g in out["graphs"]
        ],
        indent=2,
    )
)
