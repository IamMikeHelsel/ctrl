"""Exact covector metamorphic tests; primary w1 matrices remain separately saved."""

import json
from pathlib import Path

import pm_symbol as m
from pm_exact_det import bareiss, components, parity

P = Path(__file__).resolve().parent
c = [1, 1, 1, 1, 0, 1, 1, 1, 1, 1]
base = int(json.loads((P / "pm_exact_det.json").read_text())[0]["determinant"])
results = []
for name, v, norm2 in [
    ("e2", m.d.blade(2), 1),
    ("e1_plus_e2", m.d.add(m.d.blade(1), m.d.blade(2)), 2),
    ("minus_e1", m.d.scale(-1, m.d.blade(1)), 1),
]:
    a = m.matrix(c, v)
    assert all(x.denominator == 1 for row in a for x in row)
    rows = [{j: int(x) for j, x in enumerate(row) if x} for row in a]
    groups = components(rows, 448)
    value = parity([r for rs, _ in groups for r in rs]) * parity(
        [c for _, cs in groups for c in cs]
    )
    blocks = []
    for rs, cs in groups:
        det = bareiss([[rows[r].get(c, 0) for c in cs] for r in rs]) if len(rs) == len(cs) else 0
        value *= det
        blocks.append([len(rs), len(cs)])
    expected = base * norm2**224
    result = {
        "covector": name,
        "determinant": str(value),
        "prediction_from_norm_homogeneity": str(expected),
        "matches": value == expected,
        "largest_component": max(max(x) for x in blocks),
        "scope": "Three exact finite covectors, not proof of covariance or ellipticity",
    }
    results.append(result)
    (P / "pm_covector.json").write_text(json.dumps(results, indent=2) + "\n")
    print(name, result["matches"], result["largest_component"], flush=True)
