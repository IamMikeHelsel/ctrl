"""State sufficiency and deliberately changed-model memo counterexamples."""

import json
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
period = 36


def uncovered(assignments):
    return {x for x in range(period) if all(x % m != r for m, r in assignments)}


first = [(4, 0), (12, 0)]
second = [(4, 0), (12, 4)]
assert uncovered(first) == uncovered(second)
# Same allowed future choices gives equal uncovered sets for every remaining assignment.
checked = 0
for r6, r18 in product(range(6), range(18)):
    assert uncovered(first + [(6, r6), (18, r18)]) == uncovered(second + [(6, r6), (18, r18)])
    checked += 1
# Added history-sensitive constraint r6 = previous residue mod12, reduced mod6.
a = uncovered(first + [(6, first[-1][1] % 6)])
b = uncovered(second + [(6, second[-1][1] % 6)])
assert a != b
# Adaptive selection at the same depth can consume different moduli.
third = [(4, 0), (36, 0)]
assert uncovered(first) == uncovered(third)
assert {m for m, _ in first} != {m for m, _ in third}
result = {
    "same_depth_same_used_moduli": [first, second],
    "all_future_assignments_checked": checked,
    "equivalence_scope": "Original problem permits all independent future residues. Equality is structural for every future family, not inferred only from these finite tests.",
    "changed_model_history_dependent_rule": "r6 = previous r12 mod6",
    "changed_model_differing_children": [sorted(a), sorted(b)],
    "adaptive_same_depth_different_used_moduli": [first, third],
    "required_adaptive_key": "uncovered set plus consumed/remaining moduli (and any declared side constraints), not depth alone",
}
(HERE / "critic_memo.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"future_checks": checked, "history_control_differs": a != b}))
