"""Compile the finite implementation interface against the source's pinned dependencies."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path("/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes")
BASE = WORK / "lean-controls"
SOURCE = Path("/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    modules = {}

    def visit(name):
        if name in modules:
            return
        relative = Path(name.replace(".", "/") + ".lean")
        a, b = SOURCE / relative, BASE / relative
        assert sha(a) == sha(b), name
        olean = BASE / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        modules[name] = {"source": str(a), "sha256": sha(a), "olean_sha256": sha(olean)}
        for child in re.findall(r"^(?:public )?import (LeanControls\.\S+)", a.read_text(), re.M):
            visit(child)

    visit("LeanControls.Quantized")
    env = os.environ.copy()
    env["ELAN_HOME"] = str(WORK / ".tools/elan")
    lake = str(WORK / ".tools/elan/bin/lake")

    def query(*args):
        return subprocess.check_output([lake, "env", *args], cwd=BASE, env=env, text=True).strip()

    lean = query("which", "lean")
    paths = [
        str((BASE / p).resolve()) if not Path(p).is_absolute() else p
        for p in query("printenv", "LEAN_PATH").split(":")
    ]
    env["LEAN_PATH"] = ":".join(paths)
    target = HERE / "domain_contract.lean"
    with (HERE / "domain_contract.log").open("w") as log:
        run = subprocess.run(
            [lean, str(target)],
            cwd=HERE,
            env=env,
            stdout=log,
            stderr=subprocess.STDOUT,
            timeout=180,
        )
    data = {
        "exit_code": run.returncode,
        "sha256": sha(target),
        "dependencies": modules,
        "lean_path": env["LEAN_PATH"],
        "lean": lean,
        "toolchain": query("lean", "--version"),
        "scope": "New interface fresh compiled. Existing dependency oleans reused; accompanying full local source closure hashmatched to frozen owning source. Not a fresh dependency build.",
    }
    (HERE / "domain_replay.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))
    assert run.returncode == 0


if __name__ == "__main__":
    main()
