"""Compile only the isolated adapter against hash-matched original C3 cache."""

import hashlib
import json
import os
import subprocess
from pathlib import Path

here = Path(__file__).resolve().parent
source = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/adaptive-admission-03"
)
cache = source / "fresh-replay"
work = source.parents[5]
base = work / "lean-controls"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


binding = {}
for original, copied in [
    (source / "AdaptiveAdmission.lean", cache / "AdaptiveAdmission.lean"),
    (source / "inputs/DigitalHold.lean", cache / "DigitalHold.lean"),
]:
    assert sha(original) == sha(copied)
    binding[str(original)] = sha(original)
env = os.environ.copy()
env["ELAN_HOME"] = str(work / ".tools/elan")
lake = str(work / ".tools/elan/bin/lake")


def query(*args):
    return subprocess.check_output([lake, "env", *args], cwd=base, env=env, text=True).strip()


lean = Path(query("which", "lean"))
paths = [
    str((base / p).resolve()) if not Path(p).is_absolute() else p
    for p in query("printenv", "LEAN_PATH").split(":")
]
paths = [p for p in paths if p != str(base / ".lake/build/lib/lean")]
env["LEAN_PATH"] = str(cache) + ":" + ":".join(paths)
env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
p = here / "inventor_adapter.lean"
run = subprocess.run([str(lean), str(p)], cwd=here, env=env, capture_output=True, text=True)
(here / "inventor_adapter.log").write_text(run.stdout + run.stderr)
(here / "inventor_adapter_replay.json").write_text(
    json.dumps(
        {
            "source_binding": binding,
            "lean": str(lean),
            "lean_sha256": sha(lean),
            "source": str(p),
            "source_sha256": sha(p),
            "exit_code": run.returncode,
            "lean_path": env["LEAN_PATH"],
        },
        indent=2,
    )
    + "\n"
)
print(run.stdout + run.stderr)
raise SystemExit(run.returncode)
