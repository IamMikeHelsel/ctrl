"""Reproduce the frozen exact calculations and check read-only input hashes.

This is a reproducibility check. It is not a proof of the general theorem or of
the Python-to-Lean executable bridge.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[4]
SCRIPTS = ["exact_checks.py", "knot_check.py", "make_cases.py", "reference_enclosures.py"]
GENERATED = ["kernel-coefficients.json", "exact-results.json", "fixed-streams.json",
             "reference-checks.json", "reference-enclosures.json"]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

audit = json.loads((HERE / "input-audit.json").read_text())
before = {name: digest(WORKSPACE / name) for name in audit["sha256"]}
assert before == audit["sha256"], "Read-only dependency changed since audit"
results = []
with tempfile.TemporaryDirectory(prefix=".verify-", dir=HERE) as temporary:
    temp = Path(temporary)
    for name in SCRIPTS:
        shutil.copyfile(HERE / name, temp / name)
    for name in ["exact_checks.py", "make_cases.py", "reference_enclosures.py"]:
        run = subprocess.run([sys.executable, "-B", str(temp / name)], cwd=temp,
                             text=True, capture_output=True, check=True)
        results.append({"script": name, "returncode": run.returncode,
                        "stdout_sha256": hashlib.sha256(run.stdout.encode()).hexdigest(),
                        "stderr": run.stderr})
    outputs = {name: {"sha256": digest(HERE / name),
                      "reproduced_sha256": digest(temp / name)} for name in GENERATED}
    assert all(row["sha256"] == row["reproduced_sha256"] for row in outputs.values())
after = {name: digest(WORKSPACE / name) for name in audit["sha256"]}
assert before == after, "Read-only dependency changed during reproduction"
result = {"passed": True, "scope": "exact finite arithmetic and byte-for-byte reproduction only",
          "general_Lean_theorem": "open", "executable_rational_bridge": "open",
          "plant_simulation": "not run", "scripts": results, "outputs": outputs,
          "read_only_dependencies_unchanged": len(before)}
(HERE / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": True, "reproduced_files": len(outputs),
                  "read_only_dependencies_unchanged": len(before)}, indent=2))
