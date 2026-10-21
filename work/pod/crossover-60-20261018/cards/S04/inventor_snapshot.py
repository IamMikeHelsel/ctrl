"""Isolated in-memory snapshot race against the unchanged source checker.

No source files are modified. This models mutable model storage during checking;
it does not claim that a race occurred in the saved artifact.
"""

import contextlib
import copy
import hashlib
import io
import json
import sys
import types
from pathlib import Path
from unittest.mock import patch

if not __debug__:
    raise RuntimeError("Assertions required")

source = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution/check.py"
)
model_path = source.with_name("model.json")
source_bytes = source.read_bytes()
model_bytes = model_path.read_bytes()
original = json.loads(model_bytes)
mutant = copy.deepcopy(original)
mutant["prior"]["relation"] = "q = lambda*d + 1"
mutant["transfer_assumptions"][0] = "Wheel gain is exactly 2; the same observations are reused."
mutant_bytes = (json.dumps(mutant, indent=2) + "\n").encode()
assert hashlib.sha256(model_bytes).hexdigest() != hashlib.sha256(mutant_bytes).hexdigest()
module = types.ModuleType("isolated_original_checker")
module.__file__ = str(source)
exec(compile(source_bytes, str(source), "exec"), module.__dict__)
real_read_bytes = Path.read_bytes
real_read_text = Path.read_text


def run(mode):
    trace = []

    def read_bytes(path, *args, **kwargs):
        if path == model_path:
            trace.append("model hash read")
            return mutant_bytes if mode == "changed_before_hash" else model_bytes
        return real_read_bytes(path, *args, **kwargs)

    def read_text(path, *args, **kwargs):
        if path == model_path:
            trace.append("model parse read")
            return (mutant_bytes if mode == "swap_between_reads" else model_bytes).decode()
        return real_read_text(path, *args, **kwargs)

    stream = io.StringIO()
    try:
        with (
            patch.object(Path, "read_bytes", read_bytes),
            patch.object(Path, "read_text", read_text),
        ):
            with patch.object(sys, "argv", [str(source)]), contextlib.redirect_stdout(stream):
                module.main()
        accepted, error = True, None
    except AssertionError as exc:
        accepted, error = False, str(exc)
    return {"accepted": accepted, "error": error, "trace": trace, "output": stream.getvalue()}


normal = run("normal")
stable_changed = run("changed_before_hash")
race = run("swap_between_reads")
assert normal["accepted"]
assert not stable_changed["accepted"] and stable_changed["error"] == "Predeclared model changed"
assert race["accepted"]
assert race["trace"] == ["model hash read", "model parse read"]


# Proposed boundary repair: parse the exact bytes that passed the immutable pin.
def snapshot_parse(blob):
    assert hashlib.sha256(blob).hexdigest() == module.MODEL_SHA256
    return json.loads(blob)


assert snapshot_parse(model_bytes) == original
try:
    snapshot_parse(mutant_bytes)
except AssertionError:
    snapshot_rejects_changed = True
else:
    snapshot_rejects_changed = False
assert snapshot_rejects_changed
out = {
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "approved_model_sha256": hashlib.sha256(model_bytes).hexdigest(),
    "mutated_model_sha256": hashlib.sha256(mutant_bytes).hexdigest(),
    "baseline": normal,
    "stable_changed_model": stable_changed,
    "split_read_race": race,
    "single_snapshot_rejects_changed": snapshot_rejects_changed,
    "interpretation": "Current main verifies one model byte version but may parse another "
    "under concurrent mutable storage. Hash/parse once closes this "
    "modeled race; immutable trusted model storage also excludes it. "
    "This is not evidence that the saved original run experienced a race.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
