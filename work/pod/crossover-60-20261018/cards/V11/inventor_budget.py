"""Exact error-budget and threat-model negative controls for information admission."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).parent
# Scalar information update with a geometrically plausible but biased reading.
Y, lam, mu, z, x = F(1), F(1000000), F(0), F(1, 2), F(0)
post = (Y * mu + lam * z) / (Y + lam)
variance = 1 / (Y + lam)
assert abs(z - mu) <= 1
assert post > F(49, 100) and variance < F(1, 1000000)
# Without a truth-bearing measurement constraint, preserve the whole prior.
r = F(1)
full_prior_bound = r + abs(post - mu)
assert full_prior_bound > r
# Spending an explicit extra margin beta permits a bounded information weight.
beta = F(1, 10)
cap = Y * beta / (abs(z - mu) - beta)
assert cap == F(1, 4)
post_cap = (Y * mu + cap * z) / (Y + cap)
assert r + abs(post_cap - mu) == r + beta
# Repeating an origin changes raw numerical information, not a deterministic box.
clones = []
for count in [1, 10, 100]:
    weight = count * lam
    mean = (Y * mu + weight * z) / (Y + weight)
    clones.append(
        {
            "copies": count,
            "mean": str(mean),
            "claimed_variance": str(1 / (Y + weight)),
            "actual_error_at_same_truth_x0": str(abs(mean - x)),
            "same_prior_set_worst_error": str(r + abs(mean - mu)),
        }
    )
# Explicit noise/fault-budget failure: two corruptions can imitate a one-fault world.
H = [(F(1), F(0)), (F(0), F(1)), (F(1), F(1)), (F(1), F(2))]
readings = [F(1), F(0), F(1), F(0)]
truth = (F(0), F(0))
false_world = (F(1), F(0))
true_bad = [
    i
    for i, ((a, b), v) in enumerate(zip(H, readings, strict=True))
    if a * truth[0] + b * truth[1] != v
]
false_bad = [
    i
    for i, ((a, b), v) in enumerate(zip(H, readings, strict=True))
    if a * false_world[0] + b * false_world[1] != v
]
assert true_bad == [0, 2] and false_bad == [3]
result = {
    "scalar_poisoning": {
        "precision_prior": str(Y),
        "measurement_precision": str(lam),
        "candidate": str(post),
        "inverse_information": str(variance),
        "true_error": str(abs(post - x)),
        "geometric_gate_abs_innovation_le1": True,
        "full_prior_worst_error": str(full_prior_bound),
    },
    "margin_budget": {
        "prior_radius": str(r),
        "extra_margin": str(beta),
        "max_precision_weight": str(cap),
        "admitted_candidate": str(post_cap),
        "worst_error": str(r + abs(post_cap - mu)),
    },
    "duplicate_origin": clones,
    "fault_budget_negative_control": {
        "observations": list(map(str, readings)),
        "actual_faults_0based": true_bad,
        "false_world": list(map(str, false_world)),
        "false_world_faults_0based": false_bad,
    },
    "scope": "Scalar deterministic prior bound and additive information mean/inverse. No Gaussian interpretation. Clone examples do not create independent sources. A nonempty one-fault branch cannot verify that the physical fault budget holds.",
}
(HERE / "inventor_budget.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
