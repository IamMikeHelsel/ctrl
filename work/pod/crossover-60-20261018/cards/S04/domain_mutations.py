"""Independent source-attribution checker mutations, never change original files."""

import copy
import hashlib
import importlib.util
import json
from pathlib import Path

CARD = Path(__file__).resolve().parent
ROOT = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
spec = importlib.util.spec_from_file_location("fixed_checker", ROOT / "check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
model = json.loads((ROOT / "model.json").read_text())
original = json.loads((ROOT / "results.json").read_text())
assert hashlib.sha256((ROOT / "model.json").read_bytes()).hexdigest() == checker.MODEL_SHA256
assert checker.verify(original, model) == (56, 1, 8)
cases = []


def reject(name, mutate):
    value = copy.deepcopy(original)
    mutate(value)
    try:
        checker.verify(value, model)
    except (AssertionError, KeyError, ValueError) as error:
        cases.append({"name": name, "rejected": True, "reason": str(error)})
    else:
        raise AssertionError(f"Unexpected acceptance: {name}")


reject("delete_stage", lambda r: r["stages"].pop("duplicate"))
reject(
    "same_count_rename_stage",
    lambda r: r["stages"].__setitem__("new_stage", r["stages"].pop("duplicate")),
)
reject(
    "same_labels_duplicate_positive_branch",
    lambda r: r["stages"]["baseline"]["branches"].__setitem__(
        "nonpositive_d", copy.deepcopy(r["stages"]["baseline"]["branches"]["nonnegative_d"])
    ),
)
reject(
    "same_count_replace_required_objective",
    lambda r: r["stages"]["baseline"]["ranges"].__setitem__(
        "unused", r["stages"]["baseline"]["ranges"].pop("wheel")
    ),
)
reject("delete_action", lambda r: r["stages"]["baseline"]["actions"].pop("-1"))
reject("stale_producer_hash", lambda r: r.__setitem__("script_sha256", "0" * 64))
reject("stale_model_hash", lambda r: r.__setitem__("model_sha256", "0" * 64))
report = {
    "positive_counts": [56, 1, 8],
    "negative_controls": cases,
    "source_sha256": {
        p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
        for p in ["check.py", "model.json", "results.json", "experiment.py"]
    },
    "boundary": "Imported verify with independently pinned model bytes; Python assertions enabled; no Lean or physical guarantee.",
}
(CARD / "domain_mutations.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
