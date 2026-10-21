"""Replay promoted M01 proof files and audit printed axiom dependencies."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
results = []
for name in ("pm_combined.lean", "domain_doubling.lean", "domain_gap.lean"):
    source = ROOT / name
    run = subprocess.run(
        ["lake", "env", "lean", str(source)],
        cwd=ROOT.parents[4] / "lean",
        text=True,
        capture_output=True,
        check=False,
    )
    output = run.stdout + run.stderr
    (ROOT / f"pm_replay_{source.stem}.log").write_text(output)
    declarations = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", output, re.S)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    passed = (
        run.returncode == 0
        and bool(declarations)
        and all({a.strip() for a in axioms.split(",")} <= allowed for _, axioms in declarations)
    )
    results.append(
        {
            "file": name,
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "exit_code": run.returncode,
            "passed": passed,
            "declarations": [n for n, _ in declarations],
        }
    )
(ROOT / "pm_lean_replay.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results))
assert all(r["passed"] for r in results)
