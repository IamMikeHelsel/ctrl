"""Independent source-closure binding and new-module replay; no closure rebuild."""

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = Path("/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls")
BUNDLE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/geometric-unity-continuation-20261018/proof-bundle"
)
CACHE = Path(
    "/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/proof-bundle/.replay/integrated-20261018-053906"
)
files = {}
for directory in ("accepted", "source"):
    for file in (BUNDLE / directory).glob("*.lean"):
        files[file.stem] = file
queue = ["HermitianFamily"]
checked = {}
while queue:
    name = queue.pop()
    if name in checked:
        continue
    source = files[name].read_bytes()
    assert source == (CACHE / (name + ".lean")).read_bytes(), name
    checked[name] = {
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "cached_olean_sha256": hashlib.sha256((CACHE / (name + ".olean")).read_bytes()).hexdigest(),
    }
    for line in source.decode().splitlines():
        if line.startswith("import "):
            queue.extend(word for word in line.split()[1:] if word in files)
path_run = subprocess.run(
    ["lake", "env", "printenv", "LEAN_PATH"],
    cwd=PROJECT,
    capture_output=True,
    text=True,
    check=True,
)
lean_run = subprocess.run(
    ["lake", "env", "which", "lean"], cwd=PROJECT, capture_output=True, text=True, check=True
)
compiler = lean_run.stdout.strip()
environment = os.environ.copy()
environment["LEAN_PATH"] = ":".join(
    [str(CACHE)] + [str((PROJECT / x).resolve()) for x in path_run.stdout.strip().split(":")]
)
records = []
for name in sys.argv[1:]:
    file = HERE / (name + ".lean")
    before = hashlib.sha256(file.read_bytes()).hexdigest()
    result = subprocess.run(
        [compiler, str(file)], cwd=PROJECT, env=environment, text=True, capture_output=True
    )
    log = result.stdout + result.stderr
    (HERE / ("critic_" + name + ".log")).write_text(log)
    assert before == hashlib.sha256(file.read_bytes()).hexdigest(), "source changed during replay"
    closures = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    forbidden = [
        a.strip()
        for _, aa in closures
        for a in aa.split(",")
        if a.strip() and a.strip() not in {"propext", "Classical.choice", "Quot.sound"}
    ]
    record = {
        "module": name,
        "sha256": before,
        "exit_code": result.returncode,
        "declarations": len(closures),
        "forbidden_axioms": forbidden,
        "accepted": result.returncode == 0 and not forbidden,
    }
    records.append(record)
    print(json.dumps(record), flush=True)
output = {
    "compiler": compiler,
    "version": subprocess.check_output([compiler, "--version"], text=True).strip(),
    "closure_sources_hashmatched": checked,
    "modules": records,
    "scope": "New modules freshly compiled;28 accepted dependency sources bound to cached oleans by their colocated sources, not rebuilt. Cached oleans remain part of the trusted historical build environment.",
}
(HERE / "critic_source_replay.json").write_text(json.dumps(output, indent=2) + "\n")
