"""Replay isolated actual-source bridge against hash-matched accepted dependencies."""

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

P = Path("/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls")
B = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/geometric-unity-continuation-20261018/proof-bundle"
)
C = Path(
    "/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/proof-bundle/.replay/integrated-20261018-053906"
)
O = Path(__file__).parent
mods = {f.stem: f for d in ["source", "accepted"] for f in (B / d).glob("*.lean")}
order = []


def visit(n):
    if n in order:
        return
    for m in re.findall(r"^import (\S+)", mods[n].read_text(), re.M):
        if m in mods:
            visit(m)
    order.append(n)


visit("HermitianFamily")
hashes = {}
for n in order:
    assert (C / (n + ".lean")).read_bytes() == mods[n].read_bytes(), n
    hashes[n] = {
        "source": hashlib.sha256(mods[n].read_bytes()).hexdigest(),
        "olean": hashlib.sha256((C / (n + ".olean")).read_bytes()).hexdigest(),
    }


def out(cmd):
    return subprocess.check_output(cmd, cwd=P, text=True).strip()


lean = out(["lake", "env", "which", "lean"])
paths = out(["lake", "env", "printenv", "LEAN_PATH"]).split(":")
env = os.environ.copy()
env["LEAN_PATH"] = ":".join([str(C)] + [str((P / p).resolve()) for p in paths])
r = subprocess.run(
    [lean, str(O / "domain_actual_flip.lean")],
    cwd=P,
    env=env,
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
)
(O / "domain_actual_flip.log").write_text(r.stdout)
(O / "domain_actual_replay.json").write_text(
    json.dumps(
        {
            "compiler": lean,
            "version": out([lean, "--version"]),
            "exit_code": r.returncode,
            "dependency_sources_hashmatched": len(order),
            "dependencies": hashes,
            "scope": "New module compiled against prior accepted dependency oleans whose accompanying sources hash-match frozen source closure. Full closure not freshly rebuilt.",
        },
        indent=2,
    )
    + "\n"
)
print(r.returncode, r.stdout)
raise SystemExit(r.returncode)
