"""Independent source checker replay using copied files and a read-interleaving hook."""

import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import shutil
import sys
from pathlib import Path
from unittest.mock import patch

P = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
BOX = P / "critic_snapshot_copy"
BOX.mkdir(exist_ok=True)
for f in ["check.py", "model.json", "results.json", "experiment.py"]:
    shutil.copyfile(SOURCE / f, BOX / f)
spec = importlib.util.spec_from_file_location("critic_copied_checker", BOX / "check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
model_path = BOX / "model.json"
original = model_path.read_bytes()
m = json.loads(original)
r = json.loads((BOX / "results.json").read_bytes())
assert checker.verify(r, m) == (56, 1, 8)
changed = copy.deepcopy(m)
changed["prior"]["relation"] = "q = lambda*d + 1"
changed["transfer_assumptions"][0] = "Wheel gain is exactly 2."
changedbytes = (json.dumps(changed, indent=2) + "\n").encode()
real_read = Path.read_bytes
trace = []


def swap_after_read(path):
    blob = real_read(path)
    if path == model_path:
        model_path.write_bytes(changedbytes)
        trace.append("approved bytes returned for hash; copied disk changed before parse")
    return blob


with (
    patch.object(Path, "read_bytes", swap_after_read),
    patch.object(sys, "argv", [str(BOX / "check.py")]),
    contextlib.redirect_stdout(io.StringIO()),
):
    checker.main()
assert model_path.read_bytes() == changedbytes
# Persistent mutation before hashing must still reject.
with patch.object(sys, "argv", [str(BOX / "check.py")]), contextlib.redirect_stdout(io.StringIO()):
    try:
        checker.main()
    except AssertionError as exc:
        assert str(exc) == "Predeclared model changed"
    else:
        raise AssertionError("stable changed model accepted")
model_path.write_bytes(original)
mutations = []


def reject(name, edit):
    rr = copy.deepcopy(r)
    edit(rr)
    try:
        checker.verify(rr, m)
    except (AssertionError, KeyError):
        mutations.append(name)
    else:
        raise AssertionError(name + " accepted")


reject("missing_stage", lambda rr: rr["stages"].pop("trial"))
reject("missing_branch", lambda rr: rr["stages"]["baseline"]["branches"].pop("nonpositive_d"))
reject("missing_action", lambda rr: rr["stages"]["separated"]["actions"].pop("-1/2"))
reject("missing_heldout", lambda rr: rr["held_out_checks"].pop("held_out"))
reject(
    "false_acceptance",
    lambda rr: rr["stages"]["baseline"]["actions"]["-1/2"].__setitem__("accepted", True),
)
reject(
    "same_label_wrong_semantic_branch",
    lambda rr: rr["stages"]["baseline"]["branches"].__setitem__(
        "nonpositive_d", copy.deepcopy(rr["stages"]["baseline"]["branches"]["nonnegative_d"])
    ),
)
# Redundant identical constraints preserve meaning and existing dual indices.
duplicate = copy.deepcopy(r)
for stage in duplicate["stages"].values():
    for branch in stage["branches"].values():
        branch["constraints"].append(copy.deepcopy(branch["constraints"][0]))
assert checker.verify(duplicate, m) == (56, 1, 8)
# Raw JSON duplicate object names are normalized by json.loads; the last object wins.
raw = json.dumps(r)
marker = '"model_sha256":'
assert raw.count(marker) == 1
raw = raw.replace(marker, '"model_sha256":"INVALID_EARLIER_VALUE",' + marker, 1)
assert checker.verify(json.loads(raw), m) == (56, 1, 8)
out = {
    "status": "pass",
    "original_counts": [56, 1, 8],
    "source_sha256": hashlib.sha256((SOURCE / "check.py").read_bytes()).hexdigest(),
    "copied_disk_TOCTOU_accepted": True,
    "trace": trace,
    "persistent_change_rejected": True,
    "six_semantic_omission_mutations_rejected": mutations,
    "duplicate_constraint_positive_control": "accepted; mathematically equivalent",
    "duplicate_JSON_member": "accepted through standard last-wins decoding; decoded certificate remains mathematically valid, strict-schema boundary only",
    "scope": "No original modified. Actual checker run on copies, model read interleaving injected. No claim historical acceptance was raced.",
}
(P / "critic_snapshot.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
