"""Fresh PM builds of campaign modules against pinned ctrl Mathlib."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path("/Users/mike/Dev/ctrl/lean")
build = HERE / "pm_replay"
build.mkdir(exist_ok=True)
path = subprocess.check_output(
    ["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN, text=True
).strip()
binary = subprocess.check_output(["lake", "env", "which", "lean"], cwd=LEAN, text=True).strip()
env = dict(os.environ)
env["LEAN_PATH"] = str(build) + ":" + path
results = []
for name in ["domain_fixture", "domain_scale", "pm_anchors", "pm_query"]:
    source = HERE / (name + ".lean")
    result = subprocess.run(
        [binary, "--root=" + str(HERE), "-o", str(build / (name + ".olean")), str(source)],
        cwd=LEAN,
        env=env,
        text=True,
        capture_output=True,
        timeout=180,
        check=False,
    )
    output = result.stdout + result.stderr
    (HERE / ("pm_replay_" + name + ".log")).write_text(output)
    assert result.returncode == 0, output
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    for declaration, raw in axioms:
        assert set(x.strip() for x in raw.split(",")) <= {
            "propext",
            "Classical.choice",
            "Quot.sound",
        }, (declaration, raw)
    assert axioms
    results.append(
        {
            "module": name,
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "exit": 0,
            "declarations": len(axioms),
            "axioms": axioms,
        }
    )
(HERE / "pm_kernel_acceptance.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
