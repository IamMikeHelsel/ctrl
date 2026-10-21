"""PM fresh module replay, preserving the source-pinned dependency environment."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
binding = json.loads((SOURCE / "verification.json").read_text())
dependencies = []
for module, expected in binding["source_sha256"].items():
    source = SOURCE / "fresh-replay" / f"{module}.lean"
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    assert actual == expected, module
    dependencies.append({"module": module, "sha256": actual})
build = HERE / "pm_replay"
build.mkdir(exist_ok=True)
env = dict(os.environ)
env["ELAN_HOME"] = str(WORK / ".tools/elan")
env["LEAN_PATH"] = str(build) + ":" + binding["lean_path"]
results = []
for name in [
    "domain_clock",
    "domain_binding",
    "domain_tie_witness",
    "domain_queue",
    "pm_processing",
    "domain_nonanticipation",
]:
    source = HERE / (name + ".lean")
    proc = subprocess.run(
        [
            str(WORK / ".tools/elan/bin/lean"),
            "--root=" + str(HERE),
            "-o",
            str(build / (name + ".olean")),
            str(source),
        ],
        cwd=WORK / "lean-controls",
        env=env,
        text=True,
        capture_output=True,
        timeout=180,
        check=False,
    )
    output = proc.stdout + proc.stderr
    (HERE / ("pm_" + name + ".log")).write_text(output)
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    for declaration, raw in axioms:
        used = set(filter(None, (x.strip() for x in raw.split(","))))
        assert used <= {"propext", "Classical.choice", "Quot.sound"}, (declaration, used)
    assert proc.returncode == 0, output
    assert axioms, output
    results.append(
        {
            "module": name,
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "exit": proc.returncode,
            "declarations": len(axioms),
            "axioms": axioms,
        }
    )
(HERE / "pm_kernel_acceptance.json").write_text(
    json.dumps(
        {
            "dependencies_source_hashes": dependencies,
            "results": results,
            "limitation": "Original pinned source dependency oleans reused; only three campaign modules freshly rebuilt. This is not full dependency rebuild or Python receiver refinement.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(results, indent=2))
