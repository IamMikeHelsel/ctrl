"""Independent replay with critic-owned outputs and pinned source hashes."""

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
SOURCE = WORK / "research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08"
binding = json.loads((SOURCE / "verification.json").read_text())
for module, expected in binding["source_sha256"].items():
    source = SOURCE / "fresh-replay" / f"{module}.lean"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
env = dict(os.environ)
env["ELAN_HOME"] = str(WORK / ".tools/elan")
BUILD = HERE / "critic_replay"
BUILD.mkdir(exist_ok=True)
env["LEAN_PATH"] = str(BUILD) + ":" + str(HERE) + ":" + binding["lean_path"]
results = []
for name in sys.argv[1:]:
    source = HERE / name
    log = HERE / ("critic_" + source.stem + ".log")
    with log.open("w") as out:
        proc = subprocess.run(
            [
                str(WORK / ".tools/elan/bin/lean"),
                "--root=" + str(HERE),
                "-o",
                str(BUILD / (source.stem + ".olean")),
                str(source),
            ],
            cwd=WORK / "lean-controls",
            env=env,
            stdout=out,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=False,
        )
    results.append(
        {
            "file": name,
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "exit_code": proc.returncode,
            "log": str(log),
        }
    )
    assert proc.returncode == 0, log.read_text()
manifest = HERE / "critic_lean_replay.json"
previous = json.loads(manifest.read_text()) if manifest.exists() else []
previous = [row for row in previous if row["file"] not in sys.argv[1:]]
manifest.write_text(json.dumps(previous + results, indent=2) + "\n")
print(json.dumps(results, indent=2))
