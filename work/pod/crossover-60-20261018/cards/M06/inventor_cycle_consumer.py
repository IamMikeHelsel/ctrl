"""Independent-format certificate consumer: listed cycles need not be exhaustive."""
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
producer = json.loads((HERE / 'inventor_graph.json').read_text())
graph = next(g for g in producer['graphs'] if g['name'] == 'Wagner M8')


def check(n, edges, cycles, weight, cut, expected):
    if len(edges) != len(set(map(tuple, edges))) or weight < 0:
        return False
    load = [F(0)] * len(edges)
    lower = F(0)
    for mask in cycles:
        if mask < 0 or mask >> len(edges):
            return False
        chosen = [i for i in range(len(edges)) if mask & (1 << i)]
        if len(chosen) < 3 or len(chosen) % 2 != 1:
            return False
        adj = {}
        for i in chosen:
            u, v = edges[i]
            if not (0 <= u < v < n):
                return False
            adj.setdefault(u, set()).add(v)
            adj.setdefault(v, set()).add(u)
            load[i] += weight
        if any(len(neighbors) != 2 for neighbors in adj.values()):
            return False
        seen, todo = set(), [next(iter(adj))]
        while todo:
            u = todo.pop()
            if u not in seen:
                seen.add(u)
                todo.extend(adj[u] - seen)
        if len(seen) != len(adj):
            return False
        lower += weight
    upper = sum(((cut >> u) & 1) == ((cut >> v) & 1) for u, v in edges)
    return max(load) <= 1 and lower == expected and upper == expected


args = (graph['n'], graph['edges'], graph['odd_cycle_edge_masks'], F(1, 8), graph['best_cut'], F(2))
assert check(*args)
# Dropping a cycle loses the claimed lower bound; excess weights violate capacity.
assert not check(*args[:2], args[2][1:], *args[3:])
assert not check(*args[:3], F(1, 7), *args[4:])
assert not check(*args[:2], [1] + args[2][1:], *args[3:])
assert not check(*args[:4], graph['worst_one_flip_local']['mask'], args[5])
# Cut-space negative: an edge label must satisfy even as well as odd cycle parity.
c4_edges = [(0, 1), (1, 2), (2, 3), (0, 3)]
proposed_internal = [1, 0, 0, 0]
assert sum(proposed_internal) % 2 != len(c4_edges) % 2
assert not any([int(((mask >> u) & 1) == ((mask >> v) & 1)) for u, v in c4_edges] == proposed_internal for mask in range(16))
out = {'wagner_optimum': '2', 'cycle_count_supplied': len(args[2]), 'uniform_weight': '1/8',
    'positive_accepted': True, 'mutations_rejected': ['missing_cycle', 'overweight', 'noncycle', 'bad_cut'],
    'c4_noncut_edge_label_rejected': True,
    'scope': 'Exact independently structured consumer, not Lean-checked; cycle packing is a lower bound only.'}
(HERE / 'inventor_cycle_consumer.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
