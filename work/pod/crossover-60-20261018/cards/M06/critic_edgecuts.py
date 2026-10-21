"""Independent explicit random-leftover enumeration for edge-rooted cuts."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def crossing(edges, side):
    return sum((a in side) != (b in side) for a, b in edges)


def main():
    count = 0
    for n in range(1, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
            adj = [set() for _ in range(n)]
            for a, b in edges:
                adj[a].add(b)
                adj[b].add(a)
            if not edges or any(adj[a] & adj[b] for a, b in edges):
                continue
            degree = list(map(len, adj))
            m = len(edges)
            s2 = sum(d * d for d in degree)
            products = sum(degree[a] * degree[b] for a, b in edges)
            u = []
            f = []
            for a, b in edges:
                u.append(crossing(edges, (adj[a] - {b}) | (adj[b] - {a})))
                leftover = sorted(set(range(n)) - adj[a] - adj[b])
                values = []
                for bits in range(1 << len(leftover)):
                    side = adj[a] | {v for j, v in enumerate(leftover) if bits >> j & 1}
                    values.append(crossing(edges, side))
                f.append(F(sum(values), len(values)))
            observed = m - (sum(u) + 4 * sum(f)) / (5 * m)
            claimed = F(3 * m, 5) + F(2, 5) - F(s2 + 2 * products, 5 * m)
            assert observed == claimed
            count += 1
    # Omitting the finite +2/5 term would claim negative internal cost on K2.
    assert F(3, 5) - F(4, 5) == F(-1, 5)
    out = {
        "nonempty_trianglefree_graphs_n1to5": count,
        "expected_cut_method": "Explicit every fair-leftover assignment, not producer formula",
        "finite_constant_omission_K2_bound": "-1/5",
        "scope": "Finite corroboration of exact identities; no universal middle-density bound.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(out)


if __name__ == "__main__":
    main()
