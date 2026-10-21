"""Independent bridge compilation; validates source closure hashes, not a full rebuild."""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent.resolve()
work = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
source = work / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
report = json.loads((source / "verification.json").read_text())
for module, digest in report["source_sha256"].items():
    path = source / "fresh-replay" / f"{module}.lean"
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest
name = sys.argv[1]
path = HERE / name
before = hashlib.sha256(path.read_bytes()).hexdigest()
env = os.environ.copy()
env["ELAN_HOME"] = str(work / ".tools/elan")
env["LEAN_PATH"] = str(HERE) + os.pathsep + report["lean_path"]
result = subprocess.run(
    [str(work / ".tools/elan/bin/lean"), str(path)],
    cwd=work / "lean-controls",
    env=env,
    text=True,
    capture_output=True,
    timeout=180,
    check=False,
)
assert hashlib.sha256(path.read_bytes()).hexdigest() == before
(HERE / f"critic_{path.stem}.log").write_text(result.stdout + result.stderr)
(HERE / f"critic_{path.stem}_audit.json").write_text(
    json.dumps(
        {
            "file": str(path),
            "sha256": before,
            "exit_code": result.returncode,
            "source_closure_hashes_checked": len(report["source_sha256"]),
            "scope": "New bridge compile using original pinned toolchain and existing source-bound dependency closure; not a fresh full dependency rebuild.",
        },
        indent=2,
    )
    + "\n"
)
print(result.stdout + result.stderr)
sys.exit(result.returncode)
