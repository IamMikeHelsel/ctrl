"""Downward-round PM fractional certificate; no solver and no producer imports.

This checks coverage and coordinatewise domination. It inherits original budget
validity and survivor-set binding from the independent PM/critic audit; it does
not independently regenerate the arithmetic covering pool.
"""

import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEN = 1_000_000
raw = json.loads((HERE / "pm_fractional_obstruction_certificate.json").read_text())
assert len(set(raw["residues"])) == len(raw["residues"])
groups = {
    int(g): {int(r): Fraction(v) for r, v in row.items()}
    for g, row in raw["group_multipliers"].items()
}
tail = {int(r): Fraction(v) for r, v in raw["tail_multipliers"].items()}
rounded = {g: {r: (v * DEN).__floor__() for r, v in row.items()} for g, row in groups.items()}
rounded_tail = {r: (v * DEN).__floor__() for r, v in tail.items()}
for g, row in groups.items():
    assert g > 0
    for r, v in row.items():
        assert 0 <= r < g and v >= 0
        assert 0 <= Fraction(rounded[g][r], DEN) <= v
        assert v - Fraction(rounded[g][r], DEN) < Fraction(1, DEN)
for r, v in tail.items():
    assert v >= 0
    assert 0 <= Fraction(rounded_tail[r], DEN) <= v
    assert v - Fraction(rounded_tail[r], DEN) < Fraction(1, DEN)
cover = {
    x: sum(row.get(x % g, 0) for g, row in rounded.items()) + rounded_tail.get(x, 0)
    for x in raw["residues"]
}
original = {
    x: sum((row.get(x % g, Fraction()) for g, row in groups.items()), Fraction())
    + tail.get(x, Fraction())
    for x in raw["residues"]
}
assert min(original.values()) == Fraction(raw["claimed_minimum"])
assert min(cover.values()) >= 1_080_000
for x in raw["residues"]:
    assert original[x] - Fraction(cover[x], DEN) <= Fraction(len(groups) + 1, DEN)
summary = {
    "denominator": DEN,
    "groups": len(groups),
    "survivors": len(cover),
    "minimum_integer_coverage": min(cover.values()),
    "minimum_rational_coverage": str(Fraction(min(cover.values()), DEN)),
    "simple_certified_lower_bound": "27/25",
    "maximum_loss_bound": str(Fraction(len(groups) + 1, DEN)),
    "group_multipliers_integer": rounded,
    "tail_multipliers_integer": rounded_tail,
    "residues": raw["residues"],
    "scope": "Exact rounding/coverage only; original budgets and survivor binding inherited.",
}
(HERE / "domain_round_certificate_results.json").write_text(json.dumps(summary, indent=2) + "\n")
print(
    {
        k: v
        for k, v in summary.items()
        if k not in {"group_multipliers_integer", "tail_multipliers_integer", "residues"}
    }
)
