"""Compile new startup bridge against hashmatched source dependency cache."""

import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/adaptive-admission-03"
)
WORK = SOURCE.parents[5]
BASE = WORK / "lean-controls"
CACHE = SOURCE / "fresh-replay"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    records = []
    for name in ["DigitalHold", "AdaptiveAdmission"]:
        src = (SOURCE / "inputs" if name == "DigitalHold" else SOURCE) / (name + ".lean")
        cached = CACHE / src.name
        assert sha(src) == sha(cached)
        records.append(
            {"source": str(src), "sha256": sha(src), "olean_sha256": sha(CACHE / (name + ".olean"))}
        )
    env = os.environ.copy()
    env["ELAN_HOME"] = str(WORK / ".tools/elan")
    lake = str(WORK / ".tools/elan/bin/lake")

    def query(*args):
        return subprocess.check_output([lake, "env", *args], cwd=BASE, env=env, text=True).strip()

    lean = Path(query("which", "lean"))
    paths = [
        str((BASE / p).resolve()) if not Path(p).is_absolute() else p
        for p in query("printenv", "LEAN_PATH").split(":")
    ]
    paths = [p for p in paths if ".lake/packages/" in p]
    env["LEAN_PATH"] = str(CACHE) + ":" + ":".join(paths)
    target = HERE / "domain_actual_startup.lean"
    with (HERE / "domain_actual_startup.log").open("w") as log:
        run = subprocess.run(
            [str(lean), str(target)],
            cwd=HERE,
            env=env,
            stdout=log,
            stderr=subprocess.STDOUT,
            timeout=180,
        )
    result = {
        "exit_code": run.returncode,
        "source_sha256": sha(target),
        "dependencies": records,
        "lean_path": env["LEAN_PATH"],
        "toolchain": query("lean", "--version"),
        "scope": "New module fresh compiled; source dependency oleans reused with accompanying source hashes matched; no fresh source closure rebuild.",
    }
    (HERE / "domain_actual_replay.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    assert run.returncode == 0


if __name__ == "__main__":
    main()
