"""Independent consumer: exact witness/KKT checks, producer not imported."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
n = [1, -1, 1]
D = F(1, 25)


def bil(x, y):
    return sum(P[i][j] * x[i] * y[j] for i in range(3) for j in range(3))


def check(row):
    try:
        z = list(map(F, row["state"]))
        c = list(map(F, row["core"]))
        d = F(row["delta"])
        assert len(z) == len(c) == 3 and abs(d) <= D
        assert all(z[i] == c[i] + d * n[i] for i in range(3))
        assert bil(c, c) == F(row["core_energy"]) and bil(z, z) == F(row["state_energy"])
        slope = -2 * bil(n, c)
        assert (d == -D and slope >= 0) or (d == D and slope <= 0) or (slope == 0)
        # For every allowed d', V(z-d'n)-V(c)=slope*(d'-d)+A*(d'-d)^2>=0.
        assert bil(n, n) == F(189, 50) > 0
        assert row["member"] == (bil(c, c) <= 12)
        return True
    except (KeyError, ValueError, AssertionError, IndexError):
        return False


rows = json.loads((HERE / "pm_membership.json").read_text())["cases"]
assert len(rows) == 6 and all(check(r) for r in rows.values())
mutations = []
for field, value in [
    ("delta", "0"),
    ("core", ["0", "0", "0"]),
    ("core_energy", "0"),
    ("member", False),
]:
    row = copy.deepcopy(rows["active_extra"])
    row[field] = value
    assert not check(row)
    mutations.append(field)
row = copy.deepcopy(rows["outside_travel"])
row["member"] = True
assert not check(row)
mutations.append("false_accept_outside_travel")
(HERE / "critic_membership.json").write_text(
    json.dumps(
        {
            "cases": {k: check(v) for k, v in rows.items()},
            "semantic_corruptions_rejected": mutations,
            "scope": "Exact capsule witness and convex scalar KKT certificate; no producerimports or solverstatus; source/model pin external.",
        },
        indent=2,
    )
    + "\n"
)
print("6 exact membership certificates and5 corruptions independently checked")
