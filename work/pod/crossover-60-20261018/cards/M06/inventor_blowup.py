"""Exact finite witnesses for a general bounded-local-move obstruction."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
base_edges = sorted({tuple(sorted((u, u ^ (1 << bit)))) for u in range(8) for bit in range(3)})
mask = 60
rows = []
for k in range(1, 5):
    vertices = [(u, i) for u in range(8) for i in range(k)]
    edges = [
        (vertices.index((u, i)), vertices.index((v, j)))
        for u, v in base_edges
        for i in range(k)
        for j in range(k)
    ]
    signs = [(mask >> u) & 1 for u, _ in vertices]
    old_cost = sum(signs[u] == signs[v] for u, v in edges)
    deltas = [
        sum(
            (1 if signs[u] != signs[v] else -1)
            for a, b in edges
            for v in ([b] if a == u else [a] if b == u else [])
        )
        for u in range(8 * k)
    ]
    assert old_cost == 4 * k * k
    assert deltas == [k] * (8 * k)
    assert F(old_cost, (8 * k) ** 2) == F(1, 16) > F(2, 47)
    assert F(2 * len(edges), (8 * k) ** 2) == F(3, 8)
    # Bipartition by cube Hamming parity gives zero internal cost in the blowup.
    parity = [u.bit_count() % 2 for u, _ in vertices]
    assert all(parity[u] != parity[v] for u, v in edges)
    # Within component clusters {0,2,4,6}, take k of side{0,6}, k+1 of{2,4}.
    chosen = (
        {vertices.index((0, i)) for i in range(k)}
        | {vertices.index((2, i)) for i in range(k)}
        | {vertices.index((4, 0))}
    )
    assert len(chosen) == 2 * k + 1
    new_signs = [s ^ int(u in chosen) for u, s in enumerate(signs)]
    new_cost = sum(new_signs[u] == new_signs[v] for u, v in edges)
    assert new_cost - old_cost == -k
    # Exhaust all smaller moves for k<=2. Higher k relies on the hand bound,
    # with exact integer minimum of ks-2ab for a+b=s used as an algebra test.
    examined = 0
    if k <= 2:
        for size in range(1, 2 * k + 1):
            for subset in combinations(range(8 * k), size):
                selected = set(subset)
                changed = [s ^ int(u in selected) for u, s in enumerate(signs)]
                cost = sum(changed[u] == changed[v] for u, v in edges)
                assert cost >= old_cost
                examined += 1
    for size in range(2 * k + 1):
        assert min(k * size - 2 * a * (size - a) for a in range(size + 1)) >= 0
    rows.append(
        {
            "k": k,
            "n": 8 * k,
            "internal_cost": old_cost,
            "normalized_cost": "1/16",
            "target": "2/47",
            "global_cost": 0,
            "minimum_improving_cardinality": 2 * k + 1,
            "explicit_improvement": -k,
            "exhaustive_small_moves_checked": examined,
        }
    )
# Balanced BOTH-side internal objective is different: star K1,5.
star_edges = [(0, u) for u in range(1, 6)]
balanced = min(
    sum((u in subset) == (v in subset) for u, v in star_edges)
    for subset in map(set, combinations(range(6), 3))
)
assert balanced == 2 > F(72, 47)
out = {
    "scope": "General hand obstruction backed by exact finite blowups, not a general 2/47 proof.",
    "blowups": rows,
    "balanced_cut_negative": {
        "graph": "K1,5",
        "unrestricted_internal_cost": 0,
        "balanced_both_side_cost": balanced,
        "target": "72/47",
        "warning": "Not a counterexample to a one-half induced-edge problem or the unrestricted cut theorem.",
    },
}
(HERE / "inventor_blowup.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
