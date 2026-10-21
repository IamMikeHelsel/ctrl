"""Cheap local lifting checks on structured quotient candidates, not denominators."""

import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

here = Path(__file__).parent
source = json.loads((here / "inventor_elliptic.json").read_text())
A = [4 * n for n in source["original_Ns"]]
columns = source["original_columns"]
primes = [p for p in range(3, 200) if all(p % d for d in range(2, isqrt(p) + 1))]


def residue(value, p):
    value = F(value)
    if value.denominator % p == 0:
        return None
    return value.numerator * pow(value.denominator, -1, p) % p


def obstructions(x, p):
    square_classes = {z * z % p for z in range(p)}
    values = [x] + [x + a for a in A]
    return [
        (i, r)
        for i, value in enumerate(values)
        if (r := residue(value, p)) is not None and r not in square_classes
    ]


records = [r for r in source["exact_operation_records"] if "point" in r]
bad = [
    i
    for i, r in enumerate(records)
    if not (r["positive_X"] and r["X_square"] and all(r["factor_square_mask"]))
]
coverage = {p: {i for i in bad if obstructions(F(records[i]["point"][0]), p)} for p in primes}
remaining = set(bad)
greedy = []
while remaining:
    p = max(primes, key=lambda candidate: len(coverage[candidate] & remaining))
    covered = coverage[p] & remaining
    if not covered:
        break
    greedy.append(
        {
            "prime": p,
            "newly_rejected_operations": [records[i]["operation"] for i in sorted(covered)],
        }
    )
    remaining -= covered
for w in columns:
    for p in primes:
        assert obstructions(F(w * w), p) == []
# Actual quotient candidate2P1 gets an independently checkable residue witness.
target = next(r for r in records if r["operation"] == "P1+P1")
x = F(target["point"][0])
first_prime = next(p for p in primes if obstructions(x, p))
witnesses = obstructions(x, first_prime)

# Analyze affine filters while preserving the projective denominator-at-zero
# branch. Distinct row shifts may coincide modulo p, reducing check count.
filters = []
for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 43, 101]:
    squares = {z * z % p for z in range(p)}
    allowed = [w for w in range(p) if all((w * w + a) % p in squares for a in A)]
    assert all(w % p in allowed for w in columns)
    # Any primitive pair(P,Q) with Q=0 and P!=0 passes all projective tests.
    assert all((1 + a * 0) % p in squares for a in A)
    filters.append(
        {
            "prime": p,
            "distinct_row_residues": len({a % p for a in A}),
            "affine_allowed_w": allowed,
            "denominator_zero_point_allowed": True,
        }
    )
result = {
    "candidate_source": str(here / "inventor_elliptic.json"),
    "finite_candidates": len(records),
    "failing_complete_lift": len(bad),
    "greedy_small_prime_cover": greedy,
    "failing_candidates_not_rejected_by_primes_below_200": [
        records[i]["operation"] for i in sorted(remaining)
    ],
    "original_columns_pass_every_odd_prime_below_200": True,
    "two_P1_local_witness": {
        "X": str(x),
        "prime": first_prime,
        "failed_gate_indices_and_residues": witnesses,
        "gate_order": ["X_square"] + [f"X+4N{i + 1}_square" for i in range(5)],
    },
    "projective_filter_samples": filters,
    "scope": "Necessary finite local conditions for exact generated candidates. Affine filters assume denominator invertibility; projective infinity always survives, so these do not prove nonextension. Correlated row residues are not counted as independent evidence.",
}
(here / "inventor_local_checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            k: result[k]
            for k in [
                "finite_candidates",
                "failing_complete_lift",
                "greedy_small_prime_cover",
                "failing_candidates_not_rejected_by_primes_below_200",
                "two_P1_local_witness",
            ]
        },
        indent=2,
    )
)
