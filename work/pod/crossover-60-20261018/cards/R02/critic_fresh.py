"""Verify fresh-native receipts and independently rerun the same frozen local binary."""

import gzip
import hashlib
import json
import subprocess
from pathlib import Path

P = Path(__file__).parent
S = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
B = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/robot-motion/native-execution-06/builder/.cache/native_replay"
)


def sha(b):
    return hashlib.sha256(b).hexdigest()


root = json.loads((P / "pm_fresh_native.json").read_text())
provenance = json.loads((S / "native-build-provenance.json").read_text())
assert sha(B.read_bytes()) == root["binary_sha256"] == provenance["executables"]["native_replay"]
rows = []
expected = {
    x.name.removesuffix("-output.json.gz") for x in (S / "native-checks").glob("*-output.json.gz")
}
assert {r["identity"] for r in root["rows"]} == expected and len(root["rows"]) == 12
for r in root["rows"]:
    name = r["identity"]
    inp = (S / "native-checks" / (name + "-input.txt")).read_bytes()
    old = gzip.decompress((S / "native-checks" / (name + "-output.json.gz")).read_bytes())
    fresh = gzip.decompress((P / "pm_native_replay" / (name + ".json.gz")).read_bytes())
    assert r["exit"] == 0 and r["equal_saved_json"] and r["bytes_equal"]
    assert sha(inp) == r["input_sha256"] and sha(fresh) == r["stdout_sha256"] and fresh == old
    run = subprocess.run(
        [str(B), "0.8" if name.endswith("ruckig_min_08") else "0"],
        input=inp,
        capture_output=True,
        check=False,
    )
    assert run.returncode == 0 and not run.stderr and run.stdout == old
    n = len(json.loads(run.stdout)["queries"])
    assert n == r["queries"]
    rows.append(
        {
            "identity": name,
            "independent_exit": run.returncode,
            "stderr_empty": True,
            "bytes_equal_original_and_root": True,
            "queries": n,
            "input_sha256": sha(inp),
            "stdout_sha256": sha(run.stdout),
        }
    )
assert sum(r["queries"] for r in rows) == 84316
(P / "critic_fresh.json").write_text(
    json.dumps(
        {
            "binary": str(B),
            "binary_sha256": sha(B.read_bytes()),
            "rows": rows,
            "scope": "Independent fresh finite replay of12original local native inputs,84316queries; same saved binary, no fresh build/hardware or continuous runtime proof.",
        },
        indent=2,
    )
    + "\n"
)
print(
    "12 independent fresh native processes passed; all84316query output JSON bytes equal original and root"
)
