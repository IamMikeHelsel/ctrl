"""Independent immutable-source replay of the frozen Hodge milestone."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILDER = HERE.parent / "builder"
FROZEN = ROOT / "research/weinstein-lean/operator-audit"
BASE = ROOT / "lean-controls"
SOURCES = HERE / "source"
LOGS = HERE / "logs"
SOURCES.mkdir(exist_ok=True)
LOGS.mkdir(exist_ok=True)
TARGETS = ["HodgeBridge", "HodgeChecks", "HodgeInterface"]
MODULES = ["GaugeSignAudit", "ContractionCovariance"] + TARGETS
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def tree_hashes():
    return {str(p.relative_to(BUILDER)): sha(p) for p in BUILDER.rglob("*") if p.is_file()}

before_tree = tree_hashes()
expected = json.loads((BUILDER / "verification.json").read_text())["source_sha256"]
assert expected == json.loads((BUILDER / "result.json").read_text())["source_sha256"]
manifest_checks = []
for line in (BUILDER / "SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    assert sha(BUILDER / name) == digest, name
    manifest_checks.append(name)

originals = {m: (BUILDER if m in TARGETS else FROZEN) / (m + ".lean") for m in MODULES}
for m, src in originals.items():
    assert sha(src) == expected[m], m
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", src.read_text()), m
    shutil.copyfile(src, SOURCES / src.name)
    assert sha(SOURCES / src.name) == expected[m]

env = os.environ.copy()
env["ELAN_HOME"] = str(ROOT / ".tools/elan")
lake = ROOT / ".tools/elan/bin/lake"
lean = Path(subprocess.check_output([str(lake), "env", "which", "lean"], cwd=BASE, env=env, text=True).strip())
paths = subprocess.check_output([str(lake), "env", "printenv", "LEAN_PATH"], cwd=BASE, env=env, text=True).strip().split(":")
dependency_paths = [str((BASE / p).resolve()) for p in paths]
assert all(str(BUILDER) not in p for p in dependency_paths)
env["LEAN_PATH"] = ":".join([str(SOURCES)] + dependency_paths)
env["PATH"] = str(lean.parent) + ":" + env["PATH"]
assert (BASE / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0"
manifest = json.loads((BASE / "lake-manifest.json").read_text())
revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
assert revision == "56a005855ea17e0b0958f73ec801ae140b0a1679"

steps = []
def run(name, command, failure=False):
    start = time.monotonic()
    with (LOGS / (name + ".log")).open("w") as stream:
        p = subprocess.run([str(x) for x in command], env=env, cwd=SOURCES,
                           stdout=stream, stderr=subprocess.STDOUT, timeout=300)
    step = {"step": name, "exit_code": p.returncode, "seconds": round(time.monotonic() - start, 3),
            "command": [str(x) for x in command]}
    steps.append(step)
    print({k: step[k] for k in ("step", "exit_code", "seconds")}, flush=True)
    output = (LOGS / (name + ".log")).read_text()
    assert (p.returncode != 0) if failure else (p.returncode == 0), output[-8000:]
    return output

for m in MODULES:
    run("fresh-" + m, [lean, "--root=" + str(SOURCES), "-o", SOURCES / (m + ".olean"), SOURCES / (m + ".lean")])

names = []
for m in TARGETS:
    names.extend("GUHodgeBridge." + n for n in re.findall(r"^(?:theorem|lemma)\s+(\w+)", (SOURCES / (m + ".lean")).read_text(), re.M))
assert len(names) == len(set(names)) == 53
audit = "\n".join("import " + m for m in TARGETS) + "\n" + "\n".join("#print axioms " + n for n in names) + "\n"
(SOURCES / "GraderAxioms.lean").write_text(audit)
out = run("axioms", [lean, SOURCES / "GraderAxioms.lean"])
axioms = {n: [a.strip() for a in deps.split(",") if a.strip()] for n, deps in
          re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", out)}
axioms.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", out)})
assert set(axioms) == set(names)
assert all(set(a) <= ALLOWED for a in axioms.values())

with ThreadPoolExecutor(max_workers=3) as executor:
    list(executor.map(lambda m: run("kernel-" + m, [lean.with_name("leanchecker"), m, "-v"]), MODULES))

# This is a separately generated client check, with the correct square and the
# exact asserted negation of the positive square both required to compile.
facts = """import HodgeChecks
import HodgeInterface
open GUHodgeBridge
example : e 2 I01 ≠ 0 := I01_form_nonzero
example : H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = -(e 2 I01) := H_square _
example : ¬ (H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = e 2 I01) := H_square_not_positive_I01
example (x : E 2) : coordinates 12 (H (by decide : 2+12=14) x) = GUOperatorAudit.linearCoeff mathlibStar2 (coordinates 2 x) := frozen_interface_represents x
"""
(SOURCES / "GraderFacts.lean").write_text(facts)
run("positive-client", [lean, SOURCES / "GraderFacts.lean"])

# Mutate the actual universal theorem statement in a separate complete source
# file. Its proof remains unchanged, so rejection tests the theorem's sign.
original_bridge = (SOURCES / "HodgeBridge.lean").read_text()
old = "theorem H_square (x : E 2) :\n    H (by decide : 12+2=14) (H (by decide : 2+12=14) x) = -x := by"
new = old.replace("= -x := by", "= x := by")
assert original_bridge.count(old) == 1
(SOURCES / "FalseHodgeBridge.lean").write_text(original_bridge.replace(old, new))
negative = run("false-source-square", [lean, SOURCES / "FalseHodgeBridge.lean"], failure=True)
assert "Type mismatch" in negative
assert "LinearMap.congr_fun hh x" in negative
assert "unknown module" not in negative.lower() and "unknown identifier" not in negative.lower()

# Also repeat the concrete nonzero-form rejection, independently of the
# builder's recorded runner and without modifying its input or log files.
false_client = """import HodgeChecks
open GUHodgeBridge
example : H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = e 2 I01 := by
  exact H_square (e 2 I01)
"""
(SOURCES / "FalseConcreteSquare.lean").write_text(false_client)
negative_client = run("false-concrete-square", [lean, SOURCES / "FalseConcreteSquare.lean"], failure=True)
assert "Type mismatch" in negative_client and "H_square" in negative_client
assert "unknown module" not in negative_client.lower() and "unknown identifier" not in negative_client.lower()

assert tree_hashes() == before_tree, "Builder artifact changed during independent replay"
assert all(sha(p) == expected[m] for m, p in originals.items())
assert all(sha(SOURCES / (m + ".lean")) == expected[m] for m in MODULES)
report = {
    "passed": True, "independent": True, "source_sha256": expected,
    "builder_files_preserved": True, "frozen_dependency_files_preserved": True,
    "builder_tree_sha256_before_after": before_tree,
    "builder_manifest_entries_checked": manifest_checks,
    "fresh_modules": MODULES, "target_theorem_count": len(names), "axioms": axioms,
    "steps": steps, "negative_source_mutation_rejected": True,
    "negative_concrete_square_rejected": True, "positive_client_passed": True,
    "lean": subprocess.check_output([str(lean), "--version"], env=env, text=True).strip(),
    "mathlib_manifest_revision": revision, "dependency_paths": dependency_paths,
    "scope": "Fresh target and local dependency sources and oleans; separate leanchecker replay of five modules; pinned prebuilt Mathlib reused, not rebuilt. Builder files and frozen dependencies unchanged."
}
(HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ["passed", "target_theorem_count", "builder_files_preserved", "negative_source_mutation_rejected", "negative_concrete_square_rejected"]}), flush=True)
