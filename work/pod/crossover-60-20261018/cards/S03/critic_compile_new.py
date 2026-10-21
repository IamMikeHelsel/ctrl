"""Private original-toolchain dependency rebuild for new decimal interface."""

import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

P = Path(__file__).resolve().parent
I = json.loads((P / "domain_replay.json").read_text())
CACHE = P / "critic_lean"
CACHE.mkdir(exist_ok=True)
env = os.environ.copy()
env["LEAN_PATH"] = str(CACHE) + ":" + I["lean_path"]


def compile_one(name, olean=False, generic=False):
    f = P / (name + ".lean")
    h = hashlib.sha256(f.read_bytes()).hexdigest()
    cmd = ["lake", "env", "lean", str(f)] if generic else [I["lean"], "--root=" + str(P), str(f)]
    if olean:
        cmd += ["-o", str(CACHE / (name + ".olean"))]
    r = subprocess.run(
        cmd,
        cwd="/Users/mike/Dev/ctrl/lean" if generic else P,
        env=None if generic else env,
        capture_output=True,
        text=True,
    )
    s = r.stdout + r.stderr
    (P / ("critic_fresh_" + name + ".log")).write_text(s)
    a = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", s)
    assert h == hashlib.sha256(f.read_bytes()).hexdigest()
    d = {
        "module": name,
        "sha256": h,
        "exit_code": r.returncode,
        "declarations": len(a),
        "axioms": a,
    }
    print(json.dumps(d), flush=True)
    return d


with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
    deps = list(
        ex.map(
            lambda name: compile_one(name, True),
            ["domain_contract", "domain_range", "domain_budget"],
        )
    )
assert all(r["exit_code"] == 0 for r in deps)
more = [compile_one("domain_decimal"), compile_one("pm_encoding", generic=True)]
(P / "critic_new_replay.json").write_text(
    json.dumps({"dependencies": deps, "modules": more}, indent=2) + "\n"
)
