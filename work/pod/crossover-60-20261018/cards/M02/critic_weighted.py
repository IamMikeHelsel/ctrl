"""Exact independent evaluation of the proposed weighted single-capacity dual."""

import json
import runpy
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
# Reconstruct masses from original source using the critic's independently authored enumerator.
checked = runpy.run_path(str(HERE / "critic_thirteen.py"))
L, mass, tail = checked["L"], checked["mass"], checked["tail"]
source = checked["source"]
U = [x for x in range(L) if all(x % m != a for m, a in source["worst_assignment"])]
payload = json.loads((HERE / "pm_weighted_dual_weights.json").read_text())
claim = json.loads((HERE / "pm_weighted_dual.json").read_text())


def verify(data, upper_claim):
    assert data["residues"] == U
    w = list(map(F, data["weights"]))
    assert len(w) == len(U) and min(w) >= 0 and sum(w) == 1
    upper = L * tail * max(w)
    for g, M in mass.items():
        buckets = {}
        for x, z in zip(U, w, strict=True):
            buckets[x % g] = buckets.get(x % g, F()) + z
        upper += g * M * max(buckets.values())
    assert upper == F(upper_claim)
    return upper


upper = verify(payload, claim["exact_upper"])
rejected = []
for name in ["negative_weight", "wrong_normalization", "wrong_residue", "understated_objective"]:
    bad = deepcopy(payload)
    value = claim["exact_upper"]
    if name == "negative_weight":
        bad["weights"][0] = "-1"
    elif name == "wrong_normalization":
        bad["weights"][0] = str(F(bad["weights"][0]) + 1)
    elif name == "wrong_residue":
        bad["residues"][0] = 0
    else:
        value = str(upper - F(1, 10))
    try:
        verify(bad, value)
    except AssertionError:
        rejected.append(name)
    else:
        raise AssertionError(name)
result = {
    "exact_upper": str(upper),
    "excludes": upper < 1,
    "rejected_mutations": rejected,
    "scope": "Exact proposal evaluation only, not LP optimality or exclusion of all weights. Nonnegative normalized survivor weights; tail multiplier L times max weight retained.",
}
(HERE / "critic_weighted.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
