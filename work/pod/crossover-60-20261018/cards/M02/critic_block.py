"""Short independent completeness certificate: pair upper bounds plus attaining quadruple."""

import json
from copy import deepcopy
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = json.loads(
    Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json").read_text()
)
U = {x for x in range(5040) if all(x % m != a for m, a in source["worst_assignment"])}
assert len(U) == 1574
masks = {m: [{x for x in U if x % m == a} for a in range(m)] for m in [42, 60, 70, 72]}
# Exhaust all 2520+5040 pair choices, with no symmetry or dominance pruning.
leftmax = max(len(masks[42][a] | masks[60][b]) for a, b in product(range(42), range(60)))
rightmax = max(len(masks[70][a] | masks[72][b]) for a, b in product(range(70), range(72)))
assert (leftmax, rightmax) == (192, 97)


def verify(payload):
    assert payload["moduli"] == [42, 60, 70, 72]
    assert payload["period"] == 5040 and payload["survivors"] == len(U)
    residues = payload["attaining_residues"]
    assert len(residues) == 4 and all(
        0 <= a < m for m, a in zip(payload["moduli"], residues, strict=True)
    )
    hit = set().union(*(masks[m][a] for m, a in zip(payload["moduli"], residues, strict=True)))
    assert len(hit) == payload["exact_joint_maximum"] == leftmax + rightmax
    return len(hit)


payload = json.loads((HERE / "inventor_block.json").read_text())
assert verify(payload) == 289
mutations = []
for name in ["understated_maximum", "wrong_attaining_residue", "missing_modulus"]:
    bad = deepcopy(payload)
    if name == "understated_maximum":
        bad["exact_joint_maximum"] = 288
    elif name == "wrong_attaining_residue":
        bad["attaining_residues"][0] = 0
    else:
        bad["moduli"].pop()
    try:
        verify(bad)
    except AssertionError:
        mutations.append(name)
    else:
        raise AssertionError(name)
result = {
    "survivors": len(U),
    "complete_pair_checks": 2520 + 5040,
    "pair_maxima": [leftmax, rightmax],
    "joint_upper": leftmax + rightmax,
    "attaining_residues": payload["attaining_residues"],
    "attained": 289,
    "extra_coupling_gain": 0,
    "rejected_mutations": mutations,
    "scope": "Universal upper over all12700800 quadruples follows from two exhaustive pair bounds; one attaining quadruple proves equality. No reliance on producer dominance reduction.",
}
(HERE / "critic_block.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
for m in [40, 112]:
    masks[m] = [{x for x in U if x % m == a} for a in range(m)]
thirdmax = max(len(masks[40][a] | masks[112][b]) for a, b in product(range(40), range(112)))
assert thirdmax == 141
six = [42, 60, 70, 72, 40, 112]
residues = [5, 23, 14, 33, 6, 10]
attained = len(set().union(*(masks[m][a] for m, a in zip(six, residues, strict=True))))
assert attained == leftmax + rightmax + thirdmax == 430
result["six_block"] = {
    "pair_maxima": [leftmax, rightmax, thirdmax],
    "universal_upper": 430,
    "attaining_residues": residues,
    "attained": attained,
    "extra_coupling_gain": 0,
}
(HERE / "critic_block.json").write_text(json.dumps(result, indent=2) + "\n")
