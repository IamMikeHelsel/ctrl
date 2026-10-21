"""Independent root replay of scoped V11 kernel claims."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
results = []
for name in [
    "domain_gate",
    "domain_selection",
    "domain_geometry",
    "domain_survivor",
    "critic_branch",
    "critic_geometry",
    "critic_fault_bridge",
]:
    path = root / (name + ".lean")
    r = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd="/Users/mike/Dev/ctrl/lean",
        capture_output=True,
        text=True,
    )
    output = r.stdout + r.stderr
    (root / ("pm_" + name + ".log")).write_text(output)
    blocks = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    blocks += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    expected = len(re.findall(r"^#print axioms ", path.read_text(), re.M))
    passed = (
        r.returncode == 0
        and len(blocks) == expected
        and all(
            {a.strip() for a in ax.split(",") if a.strip()}
            <= {"propext", "Classical.choice", "Quot.sound"}
            for _, ax in blocks
        )
    )
    results.append(
        {
            "file": name,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "passed": passed,
            "declarations": [n for n, _ in blocks],
        }
    )
(root / "pm_new_replay.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results))
assert all(x["passed"] for x in results)
