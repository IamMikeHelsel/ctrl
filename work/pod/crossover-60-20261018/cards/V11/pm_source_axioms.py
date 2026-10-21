"""Audit original algebra declarations without changing source statements."""

import json
import os
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
replay = root / "pm_source_replay"
original = replay / "ControlsLean/Estimation/InformationFilter.lean"
names = re.findall(r"^theorem ([\w.]+)", original.read_text(), re.M)
audit = replay / "Audit.lean"
audit.write_text(
    "import ControlsLean.Estimation.InformationFilter\n"
    + "\n".join("#print axioms ControlsLean.Estimation." + n for n in names)
    + "\n"
)
env = os.environ.copy()
path = subprocess.run(
    ["lake", "env", "printenv", "LEAN_PATH"],
    cwd="/Users/mike/Dev/ctrl/lean",
    capture_output=True,
    text=True,
    check=True,
).stdout.strip()
lean = subprocess.run(
    ["lake", "env", "which", "lean"],
    cwd="/Users/mike/Dev/ctrl/lean",
    capture_output=True,
    text=True,
    check=True,
).stdout.strip()
env["LEAN_PATH"] = str(replay) + ":" + path
r = subprocess.run(
    [lean, str(audit)], cwd="/Users/mike/Dev/ctrl/lean", env=env, capture_output=True, text=True
)
text = r.stdout + r.stderr
(root / "pm_source_axioms.log").write_text(text)
blocks = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
blocks += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
allowed = {"propext", "Classical.choice", "Quot.sound"}
passed = (
    r.returncode == 0
    and len(blocks) == len(names)
    and all({a.strip() for a in ax.split(",") if a.strip()} <= allowed for _, ax in blocks)
)
(root / "pm_source_axioms.json").write_text(
    json.dumps(
        {
            "passed": passed,
            "declarations": len(blocks),
            "exit_code": r.returncode,
            "scope": "Original ring algebra only, no stochastic or geometric guarantee",
        },
        indent=2,
    )
    + "\n"
)
print(text)
assert passed
