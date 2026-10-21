"""Independent replay of repaired snapshot boundary, preserving first draft."""

import contextlib
import hashlib
import io
import json
import shutil
import types
from pathlib import Path

P = Path(__file__).parent
blob = (P / "pm_snapshot.py").read_bytes()
mod = types.ModuleType("critic_repaired_wrapper")
mod.__file__ = str(P / "pm_snapshot.py")
exec(compile(blob, mod.__file__, "exec"), mod.__dict__)
box = P / "critic_wrapper_fixed_replay"
box.mkdir(exist_ok=True)
shutil.copyfile(P / "pm_expected.json", box / "pm_expected.json")
mod.HERE = box
with contextlib.redirect_stdout(io.StringIO()):
    mod.main()
positive = json.loads((box / "pm_snapshot.json").read_text())
assert positive["negative_count"] == 20 and positive["benign_count"] == 5
snapshot = {name: (mod.SOURCE / name).read_bytes() for name in mod.NAMES}
expected = json.loads((P / "pm_expected.json").read_text())
raw = (mod.SOURCE / "results.json").read_bytes()


class HostileDict(dict):
    def __getitem__(self, key):
        raise AssertionError("must not access subclass")


class HostileBytes(bytearray):
    def decode(self, *args, **kwargs):
        raise AssertionError("must not decode mutable subclass")


new_model = json.loads(snapshot["model.json"])
new_model["prior"]["relation"] = "q=lambda*d+1"
new_blob = json.dumps(new_model).encode()
changed_snapshot = dict(snapshot)
changed_snapshot["model.json"] = new_blob
changed_expectation = dict(expected)
changed_expectation["model.json"] = hashlib.sha256(new_blob).hexdigest()
cases = [
    ("hostile_mapping", HostileDict(snapshot), raw, expected),
    ("mutable_certificate", snapshot, HostileBytes(raw), expected),
    ("hostile_expected", snapshot, raw, HostileDict(expected)),
    ("new_model_same_checker", changed_snapshot, raw, changed_expectation),
]
results = []
for name, s, c, e in cases:
    try:
        mod.accept(s, c, e)
    except (TypeError, ValueError) as exc:
        results.append({"name": name, "rejected": True, "error": str(exc)})
    else:
        raise AssertionError(name + " accepted")
# Plain caller dictionaries are captured before hash/parse. A digest hook mutates
# caller dictionaries only; local captured values and expected bindings must survive.
real_digest = mod.digest
external_s = dict(snapshot)
external_e = dict(expected)
fired = []


def mutate_caller_then_digest(b):
    if not fired:
        external_s["model.json"] = new_blob
        external_e["model.json"] = "0" * 64
        fired.append(True)
    return real_digest(b)


mod.digest = mutate_caller_then_digest
receipt = mod.accept(external_s, raw, external_e)
assert fired and receipt["model_sha256"] == expected["model.json"]
assert receipt["counts"] == [56, 1, 8]
mod.digest = real_digest
out = {
    "status": "pass",
    "fixed_wrapper_sha256": hashlib.sha256(blob).hexdigest(),
    "original_suite": {"negative": 20, "benign": 5, "counts": [56, 1, 8]},
    "extra_rejections": results,
    "plain_caller_mutation_after_capture": "accepted only captured approved model; external changes do not relabel receipt",
    "TCB": "Trusted Python, exact approved checker-model pair, authoritative expected hashes, private producer copy and non-adversarial host. Receipt is not a portable proof or physical freshness assertion.",
}
(P / "critic_wrapper_fixed.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
