"""Read-only replay of pinned original certificates and mutation rejection."""

import copy
import hashlib
import json
import runpy
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
checker = runpy.run_path(str(SOURCE / "check.py"), run_name="critic_import")
model = json.loads((SOURCE / "model.json").read_text())
if hashlib.sha256((SOURCE / "model.json").read_bytes()).hexdigest() != checker["MODEL_SHA256"]:
    raise ValueError("model binding mismatch")
result = json.loads((SOURCE / "results.json").read_text())
counts = checker["verify"](result, model)
negatives = []
for kind in ["missing_branch", "missing_action", "wrong_heldout", "wrong_action", "wrong_dual"]:
    bad = copy.deepcopy(result)
    if kind == "missing_branch":
        del bad["stages"]["separated"]["branches"]["nonpositive_d"]
    elif kind == "missing_action":
        del bad["stages"]["separated"]["actions"]["-1"]
    elif kind == "wrong_heldout":
        bad["held_out_checks"]["held_out"]["compatible_in_scalar_model"] = False
    elif kind == "wrong_action":
        bad["stages"]["separated"]["actions"]["-1"]["accepted"] = True
    else:
        bound = bad["stages"]["separated"]["branches"]["nonnegative_d"]["bounds"]["wheel"]
        bound["upper_dual"][0]["weight"] = "-1"
    try:
        checker["verify"](bad, model)
    except AssertionError as error:
        negatives.append(dict(mutation=kind, rejection=str(error)))
    else:
        raise ValueError("negative accepted")
out = dict(
    counts=counts,
    negative_controls=negatives,
    model_sha256=checker["MODEL_SHA256"],
    scope="Reexecution of original independent checker, whose Python/Fraction implementation remains trusted; no source modifications",
)
Path(__file__).with_name("critic_original_replay_results.json").write_text(
    json.dumps(out, indent=2) + "\n"
)
print(json.dumps(out, indent=2))
