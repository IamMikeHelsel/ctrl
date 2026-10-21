"""Independent cut-code certificate consumer and semantic mutations."""

import copy
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def consume(n, edges, labels):
    assert len(labels) == n and all(type(x) is int and 0 <= x < 32 for x in labels)
    assert len(set(map(tuple, edges))) == len(edges)
    assert all(0 <= a < b < n for a, b in edges)
    costs = [0] * 5
    for a, b in edges:
        assert (labels[a] ^ labels[b]).bit_count() == 4
        for j in range(5):
            costs[j] += int((labels[a] >> j) % 2 == (labels[b] >> j) % 2)
    assert sum(costs) == len(edges)
    assert 5 * min(costs) <= len(edges)
    return costs


def main():
    data = json.loads((HERE / "pm_code.json").read_text())
    labels, edges = data["code_vertices"], data["code_edges"]
    costs = consume(16, edges, labels)
    assert costs == [8] * 5
    # Independent explicit isomorphism from own folded-four-bit construction.
    iso = [u if u.bit_count() % 2 == 0 else u ^ 31 for u in range(16)]
    assert set(iso) == set(labels)
    for a, b in itertools.combinations(range(16), 2):
        assert ((a ^ b).bit_count() in (1, 4)) == ((iso[a] ^ iso[b]).bit_count() == 4)
    # Independently check weighted expansion identity from exact edge products.
    for row in data["weighted_blowup_checks"]:
        sizes = row["sizes"]
        assert all(type(s) is int and s >= 0 for s in sizes)
        m = sum(sizes[a] * sizes[b] for a, b in edges)
        c = [
            sum(
                sizes[a] * sizes[b]
                for a, b in edges
                if (labels[a] >> j) % 2 == (labels[b] >> j) % 2
            )
            for j in range(5)
        ]
        assert c == row["costs"] and m == row["m"] and sum(c) == m
        assert 5 * min(c) <= m
        assert F(2 * m, sum(sizes) ** 2) <= F(20, 47)
        assert F(min(c), sum(sizes) ** 2) <= F(2, 47)
    bad = []
    for name in ("label_bit", "high_bit", "duplicate_edge", "loop", "missing_label"):
        ee, ll = copy.deepcopy(edges), labels[:]
        if name == "label_bit":
            ll[0] ^= 1
        if name == "high_bit":
            ll[0] += 32
        if name == "duplicate_edge":
            ee.append(ee[0])
        if name == "loop":
            ee.append([0, 0])
        if name == "missing_label":
            ll.pop()
        try:
            consume(16, ee, ll)
        except AssertionError:
            bad.append(name)
        else:
            raise AssertionError(name)
    # Repeat labels on independent twins is valid; injectivity is not necessary.
    assert consume(3, [(0, 2), (1, 2)], [0, 0, 15]) == [0, 0, 0, 0, 2]
    # Exact four-color witness search is used only to obtain a checked positive map.
    adj = [set() for _ in labels]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    col = [-1] * 16

    def go(v):
        if v == 16:
            return True
        for c in range(4):
            if all(col[u] != c for u in adj[v]):
                col[v] = c
                if go(v + 1):
                    return True
        col[v] = -1
        return False

    assert go(0) and all(col[a] != col[b] for a, b in edges)
    out = {
        "coordinate_costs": costs,
        "independent_folded_cube_isomorphism": iso,
        "weighted_cases_checked": len(data["weighted_blowup_checks"]),
        "rejected_mutations": bad,
        "four_color_witness": col,
        "scope": "Exact finite certificate consumer; general graph homomorphism edgewise averaging hand-derived; no claim every triangle-free graph has such labels.",
    }
    (HERE / "critic_code.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
