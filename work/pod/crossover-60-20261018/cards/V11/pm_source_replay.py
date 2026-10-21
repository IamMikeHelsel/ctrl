"""Byte-identical source replay in existing ctrl Lean environment, isolated copies."""

import hashlib
import json
import os
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
source = Path("/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Estimation")
replay = root / "pm_source_replay"
package = replay / "ControlsLean/Estimation"
package.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
# lake supplies its package search path; append isolated package root to it.
result = subprocess.run(
    ["lake", "env", "printenv", "LEAN_PATH"],
    cwd="/Users/mike/Dev/ctrl/lean",
    capture_output=True,
    text=True,
    check=True,
)
env["LEAN_PATH"] = str(replay) + ":" + result.stdout.strip()
lean = subprocess.run(
    ["lake", "env", "which", "lean"],
    cwd="/Users/mike/Dev/ctrl/lean",
    capture_output=True,
    text=True,
    check=True,
).stdout.strip()
results = []
for name in ["ScalarKalman", "InformationFilter"]:
    original = source / (name + ".lean")
    target = package / original.name
    target.write_bytes(original.read_bytes())
    r = subprocess.run(
        [lean, "--root=" + str(replay), "-o", str(target.with_suffix(".olean")), str(target)],
        cwd="/Users/mike/Dev/ctrl/lean",
        env=env,
        capture_output=True,
        text=True,
    )
    (root / ("pm_source_" + name + ".log")).write_text(r.stdout + r.stderr)
    results.append(
        {
            "module": name,
            "sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
            "exit_code": r.returncode,
        }
    )
    if r.returncode:
        break
(root / "pm_source_replay.json").write_text(
    json.dumps(
        {
            "scope": "Copied original sources compiled using ctrl pinned toolchain; not original notebook environment or stochastic semantics proof",
            "results": results,
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(results))
