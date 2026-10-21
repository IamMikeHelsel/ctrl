"""Bind expanded Lean assumptions to exact normalized-ray incidence rows."""

import json
import re
from fractions import Fraction as F
from pathlib import Path

p = Path(__file__).parent
source = (p / "domain_linear_identification.lean").read_text()
pattern = r"\(h(\d+) : (.*?) = 0\)"
clauses = re.findall(pattern, source)
assert len(clauses) == 11
pairs = [
    ([u, v, F(1)], [u + 1, v, F(1)]) for u in [F(0), F(1, 2), F(1)] for v in [F(0), F(1, 2), F(1)]
]
pairs += [([F(1, 4), v, F(1)], [F(3, 4), v, F(1)]) for v in [F(1, 4), F(3, 4)]]
rows = []
for (index, text), (x, y) in zip(clauses, pairs, strict=True):
    row = [F(0)] * 9
    for term in text.split(" + "):
        m = re.fullmatch(r"(?:\((\d+(?:/\d+)?)\)\*)?f([012])([012])", term)
        assert m, term
        coefficient, i, j = m.groups()
        row[3 * int(i) + int(j)] += F(coefficient or 1)
    expected = [y[i] * x[j] for i in range(3) for j in range(3)]
    assert row == expected, index
    rows.append(row)
# Concrete extra nonessential matrix survives the grid and repeated first separator.
witness = list(map(F, [0, -4, 1, 4, 0, 4, -1, 0, -1]))
residuals = [sum(a * b for a, b in zip(row, witness, strict=True)) for row in rows]
assert residuals[:10] == [0] * 10 and residuals[10] == 1
# Duplicate the first separator as the second: this leaves an extra matrix freedom.
mutated = source.replace("(h10 : " + clauses[10][1] + " = 0)", "(h10 : " + clauses[9][1] + " = 0)")
assert mutated != source
(p / "critic_linear_duplicate_separator.lean").write_text(mutated)
(p / "critic_linear_binding_results.json").write_text(
    json.dumps(
        {
            "rows_checked": 11,
            "duplicate_separator_extra_matrix": witness,
            "extra_matrix_residuals": residuals,
            "row_convention": "y_i*x_j",
            "rows": rows,
            "mutation": "h10 replaced by h9, preserving claimed matrix-line conclusion",
        },
        default=str,
        indent=2,
    )
    + "\n"
)
print("All 11 expanded incidence rows match declared rays exactly.")
