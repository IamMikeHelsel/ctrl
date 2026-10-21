"""Compile an isolated bridge against the original pinned copied-source closure."""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).parent.resolve()
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
report = json.loads((SOURCE / "verification.json").read_text())
for module, digest in report["source_sha256"].items():
    copied = SOURCE / "fresh-replay" / f"{module}.lean"
    assert hashlib.sha256(copied.read_bytes()).hexdigest() == digest, module
path = ROOT / (sys.argv[1] if len(sys.argv) > 1 else "domain_prefix.lean")
env = os.environ.copy()
env["ELAN_HOME"] = str(WORK / ".tools/elan")
env["LEAN_PATH"] = str(ROOT) + ":" + report["lean_path"]
lean = WORK / ".tools/elan/bin/lean"
log = path.with_name(path.stem + "_compile.log")
with log.open("w") as output:
    done = subprocess.run(
        [str(lean), "--root=" + str(ROOT), "-o", str(path.with_suffix(".olean")), str(path)],
        cwd=WORK / "lean-controls",
        env=env,
        stdout=output,
        stderr=subprocess.STDOUT,
        timeout=180,
        check=False,
    )
print(log.read_text())
print("exit_code", done.returncode)
sys.exit(done.returncode)
