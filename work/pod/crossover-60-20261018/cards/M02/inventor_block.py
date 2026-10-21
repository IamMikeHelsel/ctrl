"""Exact four-modulus block union, with exhaustive finite dominance certificates."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json")


def main():
    source = json.loads(SOURCE.read_text())
    earlier = json.loads((HERE / "inventor_adaptive.json").read_text())
    period = source["period"]
    assert period == earlier["period"] == 5040
    survivors = [x for x in range(period) if all(x % m != a for m, a in source["worst_assignment"])]
    assert len(survivors) == earlier["survivors"] == 1574
    # Compact survivor coordinates preserve union, subset, and cardinality exactly.
    masks = {
        m: [sum(1 << i for i, x in enumerate(survivors) if x % m == a) for a in range(m)]
        for m in (40, 42, 60, 70, 72, 112)
    }

    def pair_group(m, n):
        unique = {}
        for a, b in product(range(m), range(n)):
            bits = masks[m][a] | masks[n][b]
            unique.setdefault(bits, []).append((a, b))
        ordered = sorted(unique, key=lambda bits: (-bits.bit_count(), bits))
        maximal = []
        discarded = []
        for bits in ordered:
            dominator = next((other for other in maximal if bits & ~other == 0), None)
            if dominator is None:
                maximal.append(bits)
            else:
                discarded.append((bits, dominator))
        assert len(maximal) + len(discarded) == len(unique)
        assert sum(len(v) for v in unique.values()) == m * n
        assert all(bits & ~dom == 0 for bits, dom in discarded)
        certificate = {
            "moduli": [m, n],
            "all_residue_assignments": m * n,
            "unique_union_masks": len(unique),
            "maximal_union_masks": len(maximal),
            "maximal_representatives": [unique[bits][0] for bits in maximal],
            "dominance_witnesses": [
                {"discarded": unique[bits][0], "superset": unique[dom][0]}
                for bits, dom in discarded
            ],
            "duplicate_multiplicities": [
                {"representative": unique[bits][0], "count": len(unique[bits])} for bits in ordered
            ],
            "maximum_cardinality": max(bits.bit_count() for bits in unique),
        }
        return unique, maximal, certificate

    left_all, left, left_cert = pair_group(42, 60)
    right_all, right, right_cert = pair_group(70, 72)
    best = (-1, 0, 0)
    maximizing_masks = {}
    checked = 0
    for a in left:
        for b in right:
            checked += 1
            count = (a | b).bit_count()
            if count > best[0]:
                best = (count, a, b)
                maximizing_masks = {}
            if count == best[0]:
                maximizing_masks[a | b] = left_all[a][0] + right_all[b][0]
    maximum, left_bits, right_bits = best
    representative = left_all[left_bits][0] + right_all[right_bits][0]
    assert (
        sum(
            any(x % m == a for m, a in zip((42, 60, 70, 72), representative, strict=True))
            for x in survivors
        )
        == maximum
    )
    separate = sum(max(bits.bit_count() for bits in masks[m]) for m in (42, 60, 70, 72))
    pair_sum = left_cert["maximum_cardinality"] + right_cert["maximum_cardinality"]
    gain = separate - maximum
    result = {
        "scope": "Exact finite four-modulus block bound on one saved13-smooth leaf; infinite tail and all other capacity terms unchanged.",
        "source": str(SOURCE),
        "period": period,
        "survivors": len(survivors),
        "moduli": [42, 60, 70, 72],
        "full_residue_tuples": 42 * 60 * 70 * 72,
        "deduplicated_pair_cross_product": len(left_all) * len(right_all),
        "dominance_reduced_cross_product_checked": checked,
        "left_certificate": left_cert,
        "right_certificate": right_cert,
        "separate_count_bound": separate,
        "disjoint_pair_count_bound": pair_sum,
        "exact_joint_maximum": maximum,
        "attaining_residues": representative,
        "pair_gain_count": separate - pair_sum,
        "additional_cross_pair_gain_count": pair_sum - maximum,
        "total_density_gain": str(F(gain, period)),
        "remaining_excess": str(F(earlier["base_excess"]) - F(gain, period)),
        "excluded": F(earlier["base_excess"]) - F(gain, period) < 0,
        "proof_of_pruning": "If A is a subset of B, then A union C is a subset of B union C for every C. Every discarded mask has a retained-superset witness; every original pair assignment appears in the regenerated deduplication map.",
    }
    third_all, third, third_cert = pair_group(40, 112)
    third_max = third_cert["maximum_cardinality"]
    third_max_masks = [bits for bits in third if bits.bit_count() == third_max]
    six_upper = maximum + third_max
    six_best, six_witness = -1, None
    for four, four_assignment in maximizing_masks.items():
        for two in third_max_masks:
            count = (four | two).bit_count()
            if count > six_best:
                six_best = count
                six_witness = four_assignment + third_all[two][0]
    # If equality in the sum of block bounds is impossible, every integer-valued
    # six-block union is at most one below it. Only equality cases need testing.
    certified_upper = six_upper if six_best == six_upper else six_upper - 1
    assert (
        sum(
            any(x % m == a for m, a in zip((42, 60, 70, 72, 40, 112), six_witness, strict=True))
            for x in survivors
        )
        == six_best
    )
    result["six_modulus_equality_test"] = {
        "modulus_order": [42, 60, 70, 72, 40, 112],
        "third_pair_certificate": third_cert,
        "four_maximizing_masks": len(maximizing_masks),
        "four_maximizing_representatives": list(maximizing_masks.values()),
        "third_maximizing_masks": len(third_max_masks),
        "third_maximizing_representatives": [third_all[b][0] for b in third_max_masks],
        "equality_combinations_checked": len(maximizing_masks) * len(third_max_masks),
        "initial_block_upper": six_upper,
        "best_union_among_equality_candidates": six_best,
        "attaining_residues": six_witness,
        "certified_global_upper": certified_upper,
        "exact_global_maximum_established": six_best == certified_upper,
        "argument": "Equality in |A union B| <= |A|+|B| <= maxA+maxB requires both blocks to maximize and be disjoint. Exhaustively check those candidates. If none attains the integer upper, subtract one; do not equate a restricted candidate maximum with global maximum otherwise.",
    }
    (HERE / "inventor_block.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if not k.endswith("certificate")}, indent=2))


if __name__ == "__main__":
    main()
