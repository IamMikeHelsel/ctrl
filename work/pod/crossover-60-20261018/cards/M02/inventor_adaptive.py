"""AI-written exact one-branch refinement; independent reconstruction, no source imports."""

import json
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json")


def main():
    saved = json.loads(SOURCE.read_text())
    primes, caps = saved["primes"], saved["caps"]
    period = saved["period"]
    assignments = saved["worst_assignment"]
    prefix = {m for m, _ in assignments}
    total = prod(F(p, p - 1) for p in primes[1:])
    box = (1 - F(1, 2 ** caps[0])) * prod(
        F(p, p - 1) * (1 - F(1, p ** (c + 1))) for p, c in zip(primes[1:], caps[1:], strict=True)
    )
    tail = total - box
    assert tail == F(saved["tail"])
    powers = [[2**a for a in range(1, caps[0] + 1)]] + [
        [p**a for a in range(c + 1)] for p, c in zip(primes[1:], caps[1:], strict=True)
    ]
    pool = []
    for factors in product(*powers):
        m = prod(factors)
        if m >= 4 and pow(2, m, m + 1) == pow(3, m, m + 1) == 1:
            pool.append(m)
    assert len(pool) == saved["retained_count"]
    mass = {}
    for m in pool:
        if m not in prefix:
            g = gcd(m, period)
            mass[g] = mass.get(g, F()) + F(1, m)
    denominator = lcm(tail.denominator, *(v.denominator for v in mass.values()))
    weights = {g: int(v * denominator) * g for g, v in mass.items()}
    tail_scaled = int(tail * denominator) * period
    all_bits = (1 << period) - 1
    masks = {g: [(all_bits // ((1 << g) - 1)) << a for a in range(g)] for g in set(mass) | prefix}
    survivors = all_bits
    for m, a in assignments:
        survivors &= ~masks[m][a]

    def excess(bits, removed=()):
        counts = {g: max((bits & mask).bit_count() for mask in masks[g]) for g in mass}
        upper = tail_scaled + sum(weights[g] * counts[g] for g in mass)
        # Every refinement modulus divides period: its old weighted contribution is D*C_m.
        upper -= denominator * sum(counts[m] for m in removed)
        return upper - bits.bit_count() * denominator

    scale = denominator * period
    base = excess(survivors)
    assert F(base, scale) == F(saved["worst_unresolved_excess"])
    candidates = sorted(m for m in pool if m not in prefix and period % m == 0 and m <= 120)
    records = []
    for m in candidates:
        children = [survivors & ~mask for mask in masks[m]]
        unique = sorted(set(children))
        values = [excess(bits, (m,)) for bits in unique]
        records.append(
            {
                "modulus": m,
                "residue_branches": m,
                "unique_children": len(unique),
                "pruned_children": sum(v < 0 for v in values),
                "worst_excess": str(F(max(values), scale)),
                "best_excess": str(F(min(values), scale)),
                "worst_excess_float": float(F(max(values), scale)),
                "unresolved_residues": [
                    a for a, bits in enumerate(children) if excess(bits, (m,)) >= 0
                ],
            }
        )
    result = {
        "scope": "Only one saved worst 13-smooth prefix assignment; all residues of each new modulus. Infinite tail unchanged. No covering witness and no full exclusion.",
        "source": str(SOURCE),
        "period": period,
        "tail": str(tail),
        "survivors": survivors.bit_count(),
        "base_excess": str(F(base, scale)),
        "base_excess_float": float(F(base, scale)),
        "candidate_moduli": candidates,
        "one_step": sorted(records, key=lambda r: F(r["worst_excess"])),
    }
    pair_bounds = []
    for i, m in enumerate(candidates):
        for n in candidates[i + 1 :]:
            left = [survivors & mask for mask in masks[m]]
            right = [survivors & mask for mask in masks[n]]
            separate = max(x.bit_count() for x in left) + max(y.bit_count() for y in right)
            joint, joint_a, joint_b = max(
                ((x | y).bit_count(), a, b) for a, x in enumerate(left) for b, y in enumerate(right)
            )
            pair_bounds.append(
                {
                    "moduli": [m, n],
                    "separate_max_count": separate,
                    "joint_union_max_count": joint,
                    "attaining_residues": [joint_a, joint_b],
                    "density_gain": str(F(separate - joint, period)),
                    "new_excess": str(F(base, scale) - F(separate - joint, period)),
                }
            )
    result["coupled_pair_bounds"] = sorted(pair_bounds, key=lambda r: F(r["new_excess"]))
    gains = {
        tuple(r["moduli"]): r["separate_max_count"] - r["joint_union_max_count"]
        for r in pair_bounds
    }

    def matchings(vertices):
        if not vertices:
            yield ()
            return
        first, *rest = vertices
        yield from matchings(rest)
        for i, other in enumerate(rest):
            for suffix in matchings(rest[:i] + rest[i + 1 :]):
                yield ((first, other),) + suffix

    choices = list(matchings(candidates))
    matching = max(choices, key=lambda edges: (sum(gains[e] for e in edges), -len(edges)))
    gain = sum(gains[e] for e in matching)
    assert len({vertex for edge in matching for vertex in edge}) == 2 * len(matching)
    result["disjoint_matching"] = {
        "enumerated": len(choices),
        "edges": matching,
        "saved_count": gain,
        "density_gain": str(F(gain, period)),
        "new_excess": str(F(base, scale) - F(gain, period)),
        "excluded": F(base, scale) - F(gain, period) < 0,
    }
    # Nonuniform dual weights w in {0,1}: focus on parts of the surviving period.
    # Each retained modulus still has its full valid conditional capacity; max(w)=1
    # retains exactly the same geometric infinite-tail bound.
    subset_results = []
    for k in (2, 3, 5, 7, 10, 12):
        for a in range(k):
            indicator = sum(1 << t for t in range(a, period, k))
            for mode, bits in (
                ("class", survivors & indicator),
                ("complement", survivors & ~indicator),
            ):
                if bits:
                    value = F(excess(bits), scale)
                    subset_results.append(
                        {
                            "modulus": k,
                            "residue": a,
                            "mode": mode,
                            "survivors": bits.bit_count(),
                            "excess": str(value),
                            "normalized_excess": str(value * period / bits.bit_count()),
                        }
                    )
    result["indicator_weight_test"] = {
        "tested": len(subset_results),
        "excluded": sum(F(r["excess"]) < 0 for r in subset_results),
        "best_normalized": min(subset_results, key=lambda r: F(r["normalized_excess"])),
        "best_strict_subset": min(
            (r for r in subset_results if r["survivors"] < survivors.bit_count()),
            key=lambda r: F(r["normalized_excess"]),
        ),
        "uniform_normalized": str(F(base, denominator * survivors.bit_count())),
    }
    result["negative_controls"] = {
        "even_zero_tail_excess": str(F(base, scale) - tail),
        "tail_zero_is_counterfactual": "Removing even the entire tail cannot close this leaf, but removing it is not a valid certificate.",
        "overlapping_pair_correction": {
            "toy_sets": [[0], [0], [0]],
            "true_union": 1,
            "separate_sum": 3,
            "each_pair_overlap": 1,
            "incorrect_all_pairs_subtraction": 0,
            "correct_matching_subtraction": 2,
        },
    }
    # A bounded adaptive partition, not an unrestricted tree search. Retain every
    # child of the selected first split, and test BOTH proposed next moduli.
    parent_map = {}
    for a, mask in enumerate(masks[42]):
        parent_map.setdefault(survivors & ~mask, []).append(a)
    second = []
    for bits, residues in parent_map.items():
        options = []
        for m in (40, 60):
            children = {bits & ~mask for mask in masks[m]}
            values = [excess(child, (42, m)) for child in children]
            options.append(
                {
                    "modulus": m,
                    "unique_children": len(children),
                    "pruned_children": sum(v < 0 for v in values),
                    "worst_excess": str(F(max(values), scale)),
                }
            )
        chosen = min(options, key=lambda r: F(r["worst_excess"]))
        second.append({"residues_mod42": residues, "options": options, "chosen": chosen})
    result["second_level"] = second
    result["comparison"] = {
        "fixed_42_40_worst": str(max(F(r["options"][0]["worst_excess"]) for r in second)),
        "fixed_42_60_worst": str(max(F(r["options"][1]["worst_excess"]) for r in second)),
        "adaptive_worst": str(max(F(r["chosen"]["worst_excess"]) for r in second)),
        "adaptive_chosen_counts": {
            str(m): sum(r["chosen"]["modulus"] == m for r in second) for m in (40, 60)
        },
        "adaptive_pruned_children": sum(r["chosen"]["pruned_children"] for r in second),
        "adaptive_total_children": sum(r["chosen"]["unique_children"] for r in second),
    }
    (HERE / "inventor_adaptive.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {k: v for k, v in result.items() if k not in ("one_step", "second_level")}, indent=2
        )
    )
    print(
        json.dumps(
            [
                {k: v for k, v in r.items() if k != "unresolved_residues"}
                for r in result["one_step"]
            ],
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
