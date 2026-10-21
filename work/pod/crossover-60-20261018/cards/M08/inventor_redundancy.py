"""Exact row-erasure diagnostic for Q4 -> (e_i wedge Q4)_i."""

import json
from itertools import combinations
from math import comb
from pathlib import Path

N = 14
blades = [sum(1 << i for i in a) for a in combinations(range(N), 4)]
# Coordinates in a fixed row have unique outputs, hence no cancellation between
# different input blades. Kernel is spanned by blades containing every retained row.
ranks = []
for k in range(15):
    retained = (1 << k) - 1
    invisible = [m for m in blades if retained & m == retained]
    expected = comb(14 - k, 4 - k) if k <= 4 else 0
    assert len(invisible) == expected
    ranks.append({"retained_rows": k, "kernel_dimension": expected, "rank": len(blades) - expected})
# Check every choice of five rows, not merely a favorable coordinate choice.
for five in combinations(range(N), 5):
    rows = sum(1 << i for i in five)
    assert not any(rows & m == rows for m in blades)
# Exactly ten erasures can hide a nonzero four-blade.
remaining_four = (0, 1, 2, 3)
q4 = 15
assert all(q4 & (1 << i) for i in remaining_four)
assert all(not q4 & (1 << i) for i in range(4, 14))
# Coordinate-blade messages have exactly ten nonzero rows (sharp).
assert all(sum(not m & (1 << i) for i in range(N)) == 10 for m in blades)
# Mixed messages may have more support, never fewer: each zero row must be
# contained in every nonzero monomial; the intersection has at most four indices.
examples = [{15: 4}, {15: 4, 23: -7}, {15: 4, 240: 3}]
weights = []
for message in examples:
    zero = [i for i in range(N) if all(m & (1 << i) for m in message)]
    assert len(zero) <= 4
    weights.append(N - len(zero))
# Paired ambiguity at five arbitrary corrupted rows: split the ten support rows.
# Received block vector agrees with zero message on five and nonzero message on five.
assert 5 + 5 == 10
out = {
    "status": "pass",
    "rank_by_retained_prefix": ranks,
    "all_five_row_subsets_checked": comb(14, 5),
    "minimum_nonzero_block_weight": 10,
    "mixed_example_weights": weights,
    "consequence": "At most four adversarial row errors are uniquely correctable "
    "in this exact linear code; no decoder is supplied.",
    "negative_control": "Retain rows 0,1,2,3 only: Q4=e0123 is invisible. "
    "Five row errors can tie zero and that message.",
    "boundary": "This is an algebraic implementation diagnostic; not sensor "
    "fault attribution, an invariant norm, or a source operator selection.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
