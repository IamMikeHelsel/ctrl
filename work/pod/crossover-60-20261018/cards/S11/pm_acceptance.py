"""Replay scoped source-importing kernel helpers without changing source files."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
env = os.environ.copy()
env["ELAN_HOME"] = str(WORK / ".tools/elan")
env["LEAN_PATH"] = (
    str(HERE) + os.pathsep + json.loads((SOURCE / "verification.json").read_text())["lean_path"]
)
results = {}
for name in [
    "domain_terminal",
    "domain_face",
    "domain_obstruction",
    "domain_small_budget",
    "domain_small_faces",
    "inventor_retreat",
]:
    file = HERE / (name + ".lean")
    result = subprocess.run(
        [str(WORK / ".tools/elan/bin/lean"), str(file)],
        cwd=WORK / "lean-controls",
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    output = result.stdout + result.stderr
    (HERE / ("pm_" + name + ".log")).write_text(output)
    axioms = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert result.returncode == 0, output
    assert axioms
    assert all(
        set(x.strip() for x in group.split(",") if x.strip())
        <= {"propext", "Classical.choice", "Quot.sound"}
        for group in axioms
    )
    results[name] = {
        "exit": result.returncode,
        "sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
        "declarations": len(axioms),
        "axioms": axioms,
    }
(HERE / "pm_kernel_acceptance.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
