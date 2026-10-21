"""Independent compilation receipt; isolated mathematical helper replays."""

import hashlib
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

P = Path(__file__).resolve().parent
config = {"lean": "/Users/mike/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean", "lean_path": ""}


def replay(name):
    f = P / (name + ".lean")
    before = hashlib.sha256(f.read_bytes()).hexdigest()
    env = os.environ.copy()
    env["LEAN_PATH"] = config["lean_path"]
    r = subprocess.run(["lake", "env", "lean", str(f)], cwd="/Users/mike/Dev/ctrl/lean", capture_output=True, text=True)
    (P / ("critic_" + name + ".log")).write_text(r.stdout + r.stderr)
    ax = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", r.stdout)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    clean = (
        r.returncode == 0
        and "sorryAx" not in r.stdout
        and all(set(a.replace(" ", "").split(",")) <= allowed for _, a in ax)
    )
    return {
        "module": name,
        "sha256": before,
        "post_sha256": hashlib.sha256(f.read_bytes()).hexdigest(),
        "exit_code": r.returncode,
        "accepted": clean,
        "axioms": ax,
        "axiom_free": re.findall(r"'([^']+)' does not depend on any axioms", r.stdout),
        "toolchain": config["lean"],
        "scope": "Isolated algebraic helper in4.33; no actual source executor import.",
    }


with ThreadPoolExecutor(max_workers=2) as ex:
    rows = list(ex.map(replay, sys.argv[1:]))
for row in rows:
    (P / ("critic_" + row["module"] + "_replay.json")).write_text(json.dumps(row, indent=2) + "\n")
print(json.dumps(rows, indent=2))
