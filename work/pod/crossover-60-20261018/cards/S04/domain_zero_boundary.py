"""Check the original model's overlapping zero-d boundary, without modifying sources."""

import importlib.util
import json
from pathlib import Path

CARD = Path(__file__).resolve().parent
ROOT = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
spec = importlib.util.spec_from_file_location("zero_checker", ROOT / "check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
model = json.loads((ROOT / "model.json").read_text())
results = {}
for sign in sorted(checker.SIGNS):
    constraints = checker.expected(model, "baseline", sign)
    witness = checker.valid_witness(model, constraints, ["1", "0", "0"])
    assert witness == (1, 0, 0)
    results[sign] = "same original baseline world admitted"
    separated = checker.expected(model, "separated", sign)
    try:
        checker.valid_witness(model, separated, ["1", "0", "0"])
    except AssertionError:
        results[sign + "_separated"] = "rejected by separating observation"
    else:
        raise AssertionError("Baseline boundary witness incorrectly survived separation")
report = {
    "witness": ["1", "0", "0"],
    "results": results,
    "interpretation": "A semantic cover need not be disjoint. Shared zero-d worlds do not invalidate universal per-branch safety.",
}
(CARD / "domain_zero_boundary.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
