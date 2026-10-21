"""Exact graph/cut diagnostics; exhaustive finite tests are not a BCL theorem."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def cut(n, edges, side):
    return sum(((side >> u) ^ (side >> v)) & 1 for u, v in edges)


def audit(name, n, edges):
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    assert all(0 <= u < v < n for u, v in edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert all(not (adj[u] & adj[v]) for u, v in edges)
    degrees = list(map(len, adj))
    m = len(edges)
    crossings = []
    for nbrs in adj:
        side = sum(1 << v for v in nbrs)
        observed = cut(n, edges, side)
        assert observed == sum(degrees[v] for v in nbrs)
        crossings.append(observed)
    assert sum(crossings) == sum(d * d for d in degrees)
    best, bestside = max((cut(n, edges, s), s) for s in range(1 << (n - 1)))
    r = F(2 * m, n * n)
    variance = F(sum(d * d for d in degrees), n**3) - r * r
    return {
        "name": name,
        "n": n,
        "edges": edges,
        "m": m,
        "r": str(r),
        "normalized_variance": str(variance),
        "neighbor_bound": str(F(m, n * n) - F(sum(d * d for d in degrees), n**3)),
        "best_neighbor_cost": m - max(crossings),
        "min_internal_cost": m - best,
        "optimal_side": bestside,
        "target_pass": 47 * (m - best) <= 2 * n * n,
        "middle_density": F(8, 47) < r < F(49, 125),
    }


def main():
    rows = []
    for k in range(2, 7):
        n = 3 * k - 1
        edges = [(i, j) for i in range(n) for j in range(i + 1, n) if (j - i) % 3 == 1]
        rows.append(audit(f"Andrasfai_{k}", n, edges))
    cube_edges = [(i, j) for i in range(8) for j in range(i + 1, 8) if (i ^ j).bit_count() == 1]
    cube = audit("3cube", 8, cube_edges)
    side = sum(1 << v for v in range(8) if ((v & 3).bit_count() % 2))
    baseline = cut(8, cube_edges, side)
    best_by_size = {}
    for size in range(1, 5):
        best_by_size[size] = max(
            cut(8, cube_edges, side ^ sum(1 << v for v in vs)) - baseline
            for vs in itertools.combinations(range(8), size)
        )
    assert best_by_size == {1: -1, 2: 0, 3: 1, 4: 4}
    assert F(12 - baseline, 64) > F(2, 47)
    assert cube["min_internal_cost"] == 0
    cube["local_trap"] = {
        "side": side,
        "crossing": baseline,
        "internal": 12 - baseline,
        "best_improvement_by_flipped_vertices": best_by_size,
        "scope": "Strict 1-flip local optimum and nonimproving every 2-flip move; not global optimum.",
    }
    rows.append(cube)
    clebsch_edges = [
        (i, j) for i in range(16) for j in range(i + 1, 16) if (i ^ j).bit_count() in (1, 4)
    ]
    clebsch = audit("folded_5cube_Clebsch", 16, clebsch_edges)
    adj = [set() for _ in range(16)]
    for u, v in clebsch_edges:
        adj[u].add(v)
        adj[v].add(u)
    candidates = []
    for v, w in itertools.product(range(16), repeat=2):
        start = adj[v]
        gains = {u: 5 - 2 * len(adj[u] & start) for u in range(16) if u not in start}
        moved = {u for u in adj[w] - start if gains[u] > 0}
        assert all(b not in adj[a] for a, b in itertools.combinations(moved, 2))
        side = sum(1 << u for u in start | moved)
        actual = cut(16, clebsch_edges, side)
        assert actual == 25 + sum(gains[u] for u in moved)
        candidates.append(actual)
    assert max(candidates) == 29
    assert F(40 - max(candidates), 256) - F(2, 47) == F(5, 12032)
    clebsch["two_neighbor_family"] = {
        "all_ordered_pairs_checked": 256,
        "max_crossing": 29,
        "internal_cost": 11,
        "normalized_excess_over_target": "5/12032",
        "scope": "No member of this prescribed family certifies the target; graph itself has a better cut.",
    }
    rows.append(clebsch)
    # Mutation: triangle condition is essential for the neighbor identity.
    tri = [(0, 1), (1, 2), (0, 2)]
    assert cut(3, tri, (1 << 1) | (1 << 2)) == 2 != 4
    # Mutation: edge-density rho=m/binom(n,2) is not r=2m/n².
    assert F(12, 28) == F(3, 7) != F(3, 8)
    out = {
        "rows": rows,
        "negative_controls": [
            "triangle breaks neighbor crossing equals neighbor degree sum",
            "pair-normalized density differs from r",
            "local optimality does not imply global target",
        ],
        "scope": "Finite explicit graph/cut audit; no universal or asymptotic certificate; known Andrasfai family prior art arXiv0907.3928.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps([{k: v for k, v in r.items() if k not in ("edges",)} for r in rows], indent=2))


if __name__ == "__main__":
    main()
