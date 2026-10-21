"""Independent actual wrapper replay and mutable-input boundary controls."""

import contextlib
import hashlib
import io
import json
import shutil
import types
from pathlib import Path

P = Path(__file__).parent
source = P / "pm_snapshot.py"
blob = source.read_bytes()
(P / "critic_wrapper_before.py.txt").write_bytes(blob)
mod = types.ModuleType("critic_captured_pm")
mod.__file__ = str(source)
exec(compile(blob, str(source), "exec"), mod.__dict__)
box = P / "critic_wrapper_replay"
box.mkdir(exist_ok=True)
shutil.copyfile(P / "pm_expected.json", box / "pm_expected.json")
mod.HERE = box
with contextlib.redirect_stdout(io.StringIO()):
    mod.main()
replay = json.loads((box / "pm_snapshot.json").read_text())
assert replay["negative_count"] == 20 and replay["benign_count"] == 5
assert replay["positive"]["counts"] == [56, 1, 8]
assert sum(not x["accepted"] for x in replay["cases"]) == 20
snapshot = {name: (mod.SOURCE / name).read_bytes() for name in mod.NAMES}
expected = json.loads((P / "pm_expected.json").read_text())
raw = (mod.SOURCE / "results.json").read_bytes()
changed = json.loads(snapshot["model.json"])
changed["prior"]["relation"] = "q = lambda*d + 1"
changedblob = json.dumps(changed).encode()


class SwapMapping(dict):
    def __init__(self, data):
        super().__init__(data)
        self.reads = 0

    def __getitem__(self, key):
        if key == "model.json":
            self.reads += 1
            if self.reads >= 2:
                return changedblob
        return super().__getitem__(key)


mapping = SwapMapping(snapshot)
try:
    result = mod.accept(mapping, raw, expected)
    mapping_out = {
        "accepted": True,
        "counts": result["counts"],
        "model_reads": mapping.reads,
        "receipt_hash": result["model_sha256"],
        "changed_semantics_hash": hashlib.sha256(changedblob).hexdigest(),
    }
except (AssertionError, TypeError, ValueError) as exc:
    mapping_out = {"accepted": False, "error": str(exc), "model_reads": mapping.reads}


class ChangeAfterDecode(bytearray):
    def decode(self, *args, **kwargs):
        original = super().decode(*args, **kwargs)
        changed = original.replace('"accepted": false', '"accepted": true', 1)
        assert changed != original
        self.clear()
        self.extend(changed.encode())
        return original


mutable = ChangeAfterDecode(raw)
try:
    receipt = mod.accept(snapshot, mutable, expected)
    # Receipt names the modified bytes, although arithmetic checked the old parse.
    assert receipt["certificate_sha256"] == hashlib.sha256(mutable).hexdigest()
    try:
        mod.accept(snapshot, bytes(mutable), expected)
    except (AssertionError, ValueError, TypeError, KeyError):
        replay_mutant = False
    else:
        replay_mutant = True
    mutable_out = {
        "accepted": True,
        "receipt_hash_is_changed_bytes": True,
        "changed_bytes_reverify": replay_mutant,
        "original_certificate_hash": hashlib.sha256(raw).hexdigest(),
        "receipt_certificate_hash": receipt["certificate_sha256"],
    }
except (AssertionError, ValueError, TypeError, KeyError) as exc:
    mutable_out = {"accepted": False, "error": str(exc)}
out = {
    "wrapper_source_sha256": hashlib.sha256(blob).hexdigest(),
    "replayed_negative_cases": 20,
    "replayed_benign_cases": 5,
    "positive_counts": [56, 1, 8],
    "mutable_mapping": mapping_out,
    "mutable_certificate": mutable_out,
    "scope": "Actual fixed wrapper plus actual arithmetic checker; deterministic mutable input objects emulate shared-input races, not hostile Lean/runtime or private-file modification.",
}
(P / "critic_wrapper.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
