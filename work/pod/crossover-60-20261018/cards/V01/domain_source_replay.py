"""Byte-identical vision source replay using available4.33 dependencies; not pinned4.36."""

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = Path("/Users/mike/Dev/ctrl/lean")
SOURCE = Path("/Users/mike/Dev/ctrl-research-notebook")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    root = HERE / "domain_source"
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
    for name in ["Epipolar", "Homography"]:
        rel = Path("ControlsLean/Vision") / (name + ".lean")
        src = SOURCE / rel
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        before = sha(src)
        shutil.copyfile(src, target)
        with (HERE / ("domain_source_" + name + ".log")).open("w") as log:
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
        (HERE / "domain_source_replay.json").write_text(
            json.dumps(
                {
                    "rows": rows,
                    "lean": lean,
                    "lean_path": env["LEAN_PATH"],
                    "scope": "Original source bytes freshly compiled in isolation using available4.33 Mathlib. Source pin4.36 unchanged; full pinned4.36 build unavailable because Mathlib artifacts absent.",
                },
                indent=2,
            )
            + "\n"
        )
        print(row, flush=True)
        assert run.returncode == 0 and before == sha(src) == sha(target)


if __name__ == "__main__":
    main()
