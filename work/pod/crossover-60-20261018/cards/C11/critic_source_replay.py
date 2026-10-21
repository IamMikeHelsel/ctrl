"""Independent original-toolchain source adapter replay; originals are read only."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

P = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
BASE = WORK / "lean-controls"
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/adaptive-admission-03"
CACHE = SOURCE / "fresh-replay"
records = []
for module, original in [
    ("DigitalHold", SOURCE / "inputs/DigitalHold.lean"),
    ("AdaptiveAdmission", SOURCE / "AdaptiveAdmission.lean"),
]:
    assert original.read_bytes() == (CACHE / (module + ".lean")).read_bytes()
    records.append(
        {
            "module": module,
            "source_sha256": hashlib.sha256(original.read_bytes()).hexdigest(),
            "cached_olean_sha256": hashlib.sha256(
                (CACHE / (module + ".olean")).read_bytes()
            ).hexdigest(),
        }
    )
env = os.environ.copy()
env["ELAN_HOME"] = str(WORK / ".tools/elan")
lake = str(WORK / ".tools/elan/bin/lake")
compiler = subprocess.check_output(
    [lake, "env", "which", "lean"], cwd=BASE, env=env, text=True
).strip()
paths = (
    subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=BASE, env=env, text=True)
    .strip()
    .split(":")
)
env["LEAN_PATH"] = ":".join(
    [str(CACHE)] + [str((BASE / x).resolve()) for x in paths if ".lake/packages/" in x]
)
results = []
for module in ["domain_actual_startup", "inventor_adapter"]:
    source = P / (module + ".lean")
    sha = hashlib.sha256(source.read_bytes()).hexdigest()
    run = subprocess.run([compiler, str(source)], cwd=P, env=env, capture_output=True, text=True)
    text = run.stdout + run.stderr
    (P / ("critic_" + module + ".log")).write_text(text)
    assert sha == hashlib.sha256(source.read_bytes()).hexdigest()
    closures = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
    bad = [
        v.strip()
        for _, ax in closures
        for v in ax.split(",")
        if v.strip() and v.strip() not in {"propext", "Classical.choice", "Quot.sound"}
    ]
    row = {
        "module": module,
        "sha256": sha,
        "exit_code": run.returncode,
        "declarations": len(closures),
        "forbidden_axioms": bad,
        "accepted": run.returncode == 0 and not bad,
    }
    results.append(row)
    print(json.dumps(row), flush=True)
(P / "critic_source_replay.json").write_text(
    json.dumps(
        {
            "dependencies": records,
            "modules": results,
            "compiler": compiler,
            "scope": "New adapters freshly replayed; hashmatched historical source dependencies cached, not rebuilt.",
        },
        indent=2,
    )
    + "\n"
)
