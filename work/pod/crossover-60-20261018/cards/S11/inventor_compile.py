"""Compile own arithmetic helpers in C8's existing pinned environment."""

import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
source = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
report = json.loads((source / "verification.json").read_text())
env = os.environ.copy()
env["ELAN_HOME"] = str(WORK / ".tools/elan")
env["LEAN_PATH"] = str(HERE) + os.pathsep + report["lean_path"]
result = subprocess.run(
    [str(WORK / ".tools/elan/bin/lean"), str(HERE / "inventor_retreat.lean")],
    cwd=WORK / "lean-controls",
    env=env,
    capture_output=True,
    text=True,
    check=False,
)
(HERE / "inventor_retreat.log").write_text(result.stdout + result.stderr)
print(result.stdout + result.stderr)
raise SystemExit(result.returncode)
