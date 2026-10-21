"""Consume exact fractional relaxation obstruction using independently rebuilt model."""

import json
import runpy
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
model = runpy.run_path(str(HERE / "critic_thirteen.py"))
L, mass, tail = model["L"], model["mass"], model["tail"]
source = model["source"]
U = [x for x in range(L) if all(x % m != a for m, a in source["worst_assignment"])]


def unique_object(pairs):
    answer = {}
    for k, v in pairs:
        assert k not in answer
        answer[k] = v
    return answer


certificate = json.loads(
    (HERE / "pm_fractional_obstruction_certificate.json").read_text(),
    object_pairs_hook=unique_object,
)


def verify(cert):
    assert cert["residues"] == U
    ts = list(map(F, cert["tail_multipliers"]))
    assert len(ts) == len(U) and min(ts) >= 0 and sum(ts) <= L * tail
    groups = {}
    for name, coefficients in cert["group_multipliers"].items():
        g = int(name)
        assert str(g) == name and g in mass
        row = {int(a): F(v) for a, v in coefficients.items()}
        assert len(row) == len(coefficients)
        assert all(str(int(a)) == a for a in coefficients)
        assert all(0 <= a < g and v >= 0 for a, v in row.items())
        assert sum(row.values()) <= g * mass[g]
        groups[g] = row
    cover = [
        t + sum((row.get(x % g, F()) for g, row in groups.items()), F())
        for x, t in zip(U, ts, strict=True)
    ]
    minimum = min(cover)
    assert minimum == F(cert["claimed_minimum"]) and minimum >= 1
    return minimum


minimum = verify(certificate)
rejected = []
for name in [
    "exceeded_group_budget",
    "omitted_cell",
    "wrong_residue",
    "negative_coefficient",
    "exaggerated_minimum",
]:
    bad = deepcopy(certificate)
    g = next(iter(bad["group_multipliers"]))
    a = next(iter(bad["group_multipliers"][g]))
    if name == "exceeded_group_budget":
        bad["group_multipliers"][g][a] = str(int(g) * mass[int(g)] + 1)
    elif name == "omitted_cell":
        bad["residues"].pop()
        bad["tail_multipliers"].pop()
    elif name == "wrong_residue":
        bad["residues"][0] = 4
    elif name == "negative_coefficient":
        bad["group_multipliers"][g][a] = "-1"
    else:
        bad["claimed_minimum"] = str(minimum + 1)
    try:
        verify(bad)
    except (AssertionError, KeyError):
        rejected.append(name)
    else:
        raise AssertionError(name)
result = {
    "cells": len(U),
    "groups_supplied": len(certificate["group_multipliers"]),
    "exact_minimum": str(minimum),
    "minimum_float": float(minimum),
    "all_group_and_tail_budgets_valid": True,
    "rejected_mutations": rejected,
    "claim": "For every nonnegative normalized weight on this fixed survivor set, its single-capacity plus worst-point-tail upper bound is at least this minimum. Not a congruence covering and not a no-go for coupled or branched refinements.",
}
(HERE / "critic_fractional.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "exact_minimum"}, indent=2))
