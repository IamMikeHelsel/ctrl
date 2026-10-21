"""Independent trace derivation check; no producer imports or metric realization."""

import hashlib
import json
from itertools import product
from pathlib import Path

N = 14
SIG = [1] * 7 + [-1] * 7


def metric(i, j):
    return SIG[i] if i == j else 0


records = []
for seed in [(0, 0, 0), (0, 0, 7), (0, 7, 7), (7, 7, 7), (0, 1, 7)]:

    def h(i, j, k, active_seed=seed):
        return int(tuple(sorted((i, j, k))) == active_seed)

    def derivative(m, i, j, k, l):
        return (
            h(i, k, m) * metric(j, l)
            + h(j, l, m) * metric(i, k)
            - h(i, l, m) * metric(j, k)
            - h(j, k, m) * metric(i, l)
        )

    trace = [sum(SIG[j] * h(j, j, m) for j in range(N)) for m in range(N)]
    dr = {
        (m, i, l): sum(SIG[j] * derivative(m, j, i, j, l) for j in range(N))
        for m, i, l in product(range(N), repeat=3)
    }
    for m, i, l in product(range(N), repeat=3):
        assert dr[m, i, l] == 12 * h(i, l, m) + trace[m] * metric(i, l)
    div = [sum(SIG[i] * dr[i, i, l] for i in range(N)) for l in range(N)]
    ds = [sum(SIG[i] * dr[m, i, i] for i in range(N)) for m in range(N)]
    assert div == [13 * t for t in trace]
    assert ds == [26 * t for t in trace]
    records.append(
        {"symmetric_H_seed": seed, "trace_H": trace, "divergence_ricci": div, "scalar_gradient": ds}
    )
base = Path(__file__).parent
root = json.loads((base / "pm_curvature_jet.json").read_text())
assert records[0]["divergence_ricci"] == root["divergence_ricci"]
assert records[0]["scalar_gradient"] == root["scalar_gradient"]
result = {
    "checks": 5 * N**3,
    "cases": records,
    "root_000_fields_match": True,
    "producer_hash": hashlib.sha256((base / "pm_curvature_jet.py").read_bytes()).hexdigest(),
    "scope": "Independent Ricci-derivative and trace checks, general formula hand-derived; no global metric claim.",
}
(base / "domain_jet_check.json").write_text(json.dumps(result, indent=2) + "\n")
print("Five symmetric cubic jets pass exact DR=12H+tr(H)g, div=13tr(H), dscal=26tr(H)")
