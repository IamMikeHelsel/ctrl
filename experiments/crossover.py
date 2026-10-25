"""Exact, reproducible crossover experiments; run with `uv run python -m experiments.crossover`.

Reads the actual Li witness, checks its energy/cut identity and criticality, and searches
for a small NAE propagation tree. Numerical optimizers are not dependencies of this replay.
The independent tree checker is deliberately separate from the search. Lean checks the
corresponding four-case argument in ErdosLab/Erdos834.lean.

AI-assisted: OpenAI Codex, 2026-10-18. No new mathematical priority is claimed.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/ErdosLab/Erdos834.lean"
OUTPUT = ROOT / "work/834/certs/crossover.json"


def read_edges(source: str) -> tuple[tuple[int, ...], ...]:
    """Narrow parser for the explicit `liH` literal, failing closed on unexpected content."""
    match = re.search(
        r"private def liH : Finset \(Finset \(Fin 9\)\) :=\s*(\{[\s\S]*?\})\s*\n\n",
        source,
    )
    if match is None:
        raise ValueError("expected the explicit Fin 9 liH literal")
    literal = match[1]
    if re.fullmatch(r"[\s{},0-8]+", literal) is None:
        raise ValueError("unexpected token in liH")
    edges = tuple(
        tuple(map(int, re.findall(r"\d+", e))) for e in re.findall(r"\{([^{}]+)\}", literal)
    )
    if len(edges) != 22 or len(set(edges)) != 22:
        raise ValueError("expected 22 distinct edges")
    if any(len(e) != 3 or tuple(sorted(set(e))) != e for e in edges):
        raise ValueError("expected distinct sorted 3-element edges")
    return edges


def search_tree(edges: tuple[tuple[int, ...], ...], n: int = 9) -> dict:
    """Minimize binary branch nodes under this deterministic unit-propagation procedure."""

    @lru_cache(None)
    def solve(state: tuple[int, ...]) -> tuple[int, dict]:
        colors = list(state)
        forced = []
        while True:
            changed = False
            for edge_id, edge in enumerate(edges):
                vals = [colors[v] for v in edge]
                if -1 not in vals and len(set(vals)) == 1:
                    return 0, {"forced": forced, "conflict": edge_id}
                if vals.count(-1) == 1:
                    known = [v for v in vals if v != -1]
                    if known[0] == known[1]:
                        vertex = edge[vals.index(-1)]
                        colors[vertex] = 1 - known[0]
                        forced.append([vertex, colors[vertex], edge_id])
                        changed = True
            if not changed:
                break
        best = None
        for vertex, color in enumerate(colors):
            if color != -1:
                continue
            children = []
            count = 1
            for value in (0, 1):
                child = colors.copy()
                child[vertex] = value
                size, tree = solve(tuple(child))
                children.append(tree)
                count += size
            if best is None or count < best[0]:
                best = count, {"forced": forced, "branch": vertex, "children": children}
        if best is None:
            raise ValueError("satisfying coloring found; contradiction tree does not exist")
        return best

    nodes, tree = solve((0,) + (-1,) * (n - 1))
    return {"normalized_vertex": 0, "normalized_color": 0, "branch_nodes": nodes, "tree": tree}


def check_tree(edges: tuple[tuple[int, ...], ...], certificate: dict, n: int = 9) -> int:
    """Independently replay every inference; return the number of contradiction leaves.

    Complement normalization is valid for NAE constraints. Bounds and exact node keys are
    checked so a malformed search output cannot silently skip a branch or add assignments.
    """
    if certificate["normalized_vertex"] != 0 or certificate["normalized_color"] != 0:
        raise ValueError("expected normalization at vertex 0 to color 0")

    def visit(node: dict, incoming: dict[int, int]) -> tuple[int, int]:
        colors = incoming.copy()
        for vertex, value, edge_id in node["forced"]:
            if not 0 <= vertex < n or vertex in colors or value not in (0, 1):
                raise ValueError("invalid forced assignment")
            if not 0 <= edge_id < len(edges):
                raise ValueError("invalid force edge")
            edge = edges[edge_id]
            others = [v for v in edge if v != vertex]
            if vertex not in edge or len(others) != 2:
                raise ValueError("force vertex is not in its edge")
            if any(colors.get(v) != 1 - value for v in others):
                raise ValueError("force has no equal-color antecedents")
            colors[vertex] = value
        if "conflict" in node:
            if set(node) != {"forced", "conflict"}:
                raise ValueError("unexpected conflict fields")
            edge_id = node["conflict"]
            if not 0 <= edge_id < len(edges):
                raise ValueError("invalid conflict edge")
            vals = [colors.get(v, -1) for v in edges[edge_id]]
            if -1 in vals or len(set(vals)) != 1:
                raise ValueError("claimed conflict is not monochromatic")
            return 1, 0
        if set(node) != {"forced", "branch", "children"} or len(node["children"]) != 2:
            raise ValueError("binary split must include both children")
        vertex = node["branch"]
        if not 0 <= vertex < n or vertex in colors:
            raise ValueError("invalid branch vertex")
        checked = [
            visit(child, {**colors, vertex: value}) for value, child in enumerate(node["children"])
        ]
        return sum(v[0] for v in checked), 1 + sum(v[1] for v in checked)

    leaves, nodes = visit(certificate["tree"], {0: 0})
    if nodes != certificate["branch_nodes"]:
        raise ValueError("branch count mismatch")
    return leaves


def clique_relaxation_certificate(weights: Counter) -> dict:
    """Exact dual of the weighted clique-cover LP, discovered numerically then rechecked.

    A k-clique crosses at most floor(k²/4) cut edges. Minimizing the sum of these
    clique bounds over nonnegative exact covers cannot beat 44 on this instance.
    Original hyperedge triangles supply a cover costing 44; this dual supplies 44 below.
    This is rational replay in Python, not a Lean-checked LP-duality theorem.
    """
    pairs = sorted(weights)
    numerators = [
        0,
        2,
        1,
        1,
        1,
        1,
        1,
        2,
        2,
        1,
        1,
        1,
        1,
        2,
        1,
        1,
        1,
        1,
        1,
        2,
        2,
        1,
        2,
        2,
        1,
        2,
        0,
        1,
        0,
        1,
    ]
    if len(pairs) != len(numerators):
        raise ValueError("dual certificate has wrong support")
    dual = dict(zip(pairs, (Fraction(x, 2) for x in numerators), strict=True))
    count = 0
    for size in range(2, 10):
        for clique in combinations(range(9), size):
            ps = list(combinations(clique, 2))
            if not all(p in weights for p in ps):
                continue
            count += 1
            if sum(dual[p] for p in ps) > size**2 // 4:
                raise ValueError("infeasible clique dual")
    objective = sum(weights[p] * dual[p] for p in pairs)
    if objective != 44:
        raise ValueError("unexpected dual objective")
    return {
        "exact_dual_objective": str(objective),
        "checked_cliques": count,
        "pair_dual_weights": [[*p, str(dual[p])] for p in pairs],
        "primal_cover": "the 22 original hyperedge triangles, each with coefficient 1",
        "interpretation": "this relaxation cannot certify a cut bound below 44",
        "trust": "exact Fraction arithmetic replay; not a Lean proof of LP duality",
    }


def run() -> dict:
    edges = read_edges(SOURCE.read_text())
    weights = Counter(p for e in edges for p in combinations(e, 2))
    histogram = Counter()
    critical = {}
    degrees = [sum(v in e for e in edges) for v in range(9)]
    for rest in product((0, 1), repeat=8):
        colors = (0, *rest)
        mono = [i for i, e in enumerate(edges) if len({colors[v] for v in e}) == 1]
        cut = sum(w for (i, j), w in weights.items() if colors[i] != colors[j])
        signs = [1 - 2 * x for x in colors]
        ising = sum(w * signs[i] * signs[j] for (i, j), w in weights.items())
        if 2 * len(mono) + cut != 44 or 4 * len(mono) != 22 + ising:
            raise ValueError("energy/cut/Ising identity failed")
        histogram[len(mono)] += 1
        if len(mono) == 1:
            critical.setdefault(mono[0], list(colors))
    if min(histogram) != 1 or len(critical) != 22 or min(degrees) != 7:
        raise ValueError("witness no longer has the expected properties")
    tree = search_tree(edges)
    leaves = check_tree(edges, tree)
    return {
        "source": str(SOURCE.relative_to(ROOT)),
        "witness_sha256": hashlib.sha256(json.dumps(edges).encode()).hexdigest(),
        "edges": edges,
        "degrees": degrees,
        "pair_weights": [[*p, w] for p, w in sorted(weights.items())],
        "normalized_colorings_checked": sum(histogram.values()),
        "monochromatic_edge_histogram": dict(sorted(histogram.items())),
        "minimum_monochromatic_edges": min(histogram),
        "maximum_weighted_cut": 2 * (len(edges) - min(histogram)),
        "minimum_ising_pair_sum": 4 * min(histogram) - len(edges),
        "unique_violation_witnesses": critical,
        "contradiction_leaves": leaves,
        "propagation_certificate": tree,
        "clique_cover_relaxation": clique_relaxation_certificate(weights),
        "trust": "Python exact replay plus independently elaborated Lean four-case proof",
        "novelty": "structural reproof of Li's existing witness; no new Erdős result claimed",
    }


if __name__ == "__main__":
    result = run()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: result[k]
                for k in (
                    "normalized_colorings_checked",
                    "minimum_monochromatic_edges",
                    "maximum_weighted_cut",
                    "minimum_ising_pair_sum",
                    "contradiction_leaves",
                )
            },
            indent=2,
        )
    )
    print(f"Certificate: {OUTPUT}")
