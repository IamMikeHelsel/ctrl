"""Independent fresh replay of PM's local integer-cell initialization bridge."""

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = Path("/Users/mike/Dev/ctrl/lean")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assert (
        "'S03Initialization.full_cell_guard' depends on axioms:"
        in (HERE / "pm_initialization.log").read_text()
    )
    assert "error:" not in (HERE / "pm_initialization.log").read_text()
    root = HERE / "domain_initialization_env"
    root.mkdir(exist_ok=True)
    env = os.environ.copy()

    def query(*args):
        return subprocess.check_output(["lake", "env", *args], cwd=BASE, env=env, text=True).strip()

    lean = query("which", "lean")
    paths = [
        str((BASE / p).resolve()) if not Path(p).is_absolute() else p
        for p in query("printenv", "LEAN_PATH").split(":")
    ]
    env["LEAN_PATH"] = str(root) + ":" + ":".join(paths)
    rows = []
    for name in ["pm_cell", "pm_encoding", "pm_initialization"]:
        src = HERE / (name + ".lean")
        target = root / src.name
        before = sha(src)
        shutil.copyfile(src, target)
        with (root / (name + ".log")).open("w") as log:
            run = subprocess.run(
                [lean, "-o", str(target.with_suffix(".olean")), str(target)],
                cwd=root,
                env=env,
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=180,
            )
        row = {
            "module": name,
            "exit_code": run.returncode,
            "source_sha256": before,
            "post_sha256": sha(src),
            "copy_sha256": sha(target),
        }
        rows.append(row)
        (HERE / "domain_initialization_replay.json").write_text(
            json.dumps(
                {
                    "results": rows,
                    "scope": "Three local PM modules freshly compiled; source PD.energy equality remains a hand-checked ring binding across separate toolchain. Same-event ADC and current-state premise only; no stale initialization.",
                },
                indent=2,
            )
            + "\n"
        )
        print(row, flush=True)
        assert run.returncode == 0 and before == sha(src) == sha(target)


if __name__ == "__main__":
    main()
