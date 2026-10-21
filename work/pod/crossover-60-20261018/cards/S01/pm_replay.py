"""Independent copied-source replay using the original pinned Lean environment."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
report = json.loads((SOURCE / "verification.json").read_text())
for name, digest in report["source_sha256"].items():
    assert (
        hashlib.sha256((SOURCE / "fresh-replay" / f"{name}.lean").read_bytes()).hexdigest()
        == digest
    )
replay = ROOT / "pm_replay"
replay.mkdir(exist_ok=True)
env = os.environ.copy()
env["ELAN_HOME"] = str(WORK / ".tools/elan")
env["LEAN_PATH"] = str(replay) + os.pathsep + report["lean_path"]
results = []
for name in (
    "domain_prefix",
    "domain_global",
    "domain_handoff",
    "domain_assembly",
    "domain_absolute",
):
    original = ROOT / f"{name}.lean"
    path = replay / original.name
    path.write_bytes(original.read_bytes())
    run = subprocess.run(
        [
            str(WORK / ".tools/elan/bin/lean"),
            "--root=" + str(replay),
            "-o",
            str(path.with_suffix(".olean")),
            str(path),
        ],
        cwd=WORK / "lean-controls",
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    output = run.stdout + run.stderr
    (replay / f"{name}.log").write_text(output)
    decl = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", output, re.S)
    passed = (
        run.returncode == 0
        and bool(decl)
        and all(
            set(x.strip() for x in a.split(",")) <= {"propext", "Classical.choice", "Quot.sound"}
            for _, a in decl
        )
    )
    results.append(
        {
            "file": name,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "passed": passed,
            "declarations": [n for n, _ in decl],
        }
    )
    if not passed:
        break
(ROOT / "pm_replay.json").write_text(
    json.dumps(
        {
            "source_hashes_checked": len(report["source_sha256"]),
            "scope": "Fresh copied new bridge closure; original pinned dependency oleans reused, not full dependency rebuild.",
            "results": results,
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(results))
assert len(results) == 5 and all(x["passed"] for x in results)
