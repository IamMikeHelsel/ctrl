"""Actual Lean stdout spoof against the original audit parser; negative fixture only."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions required")

root = Path(__file__).resolve().parent
source_path = root / "inventor_audit_negative.lean"
source = source_path.read_text()
namespace = "LeanControls.Generated.InventorAuditNegative."
declarations = [namespace + d for d in re.findall(r"^theorem (\w+)", source, re.M)]
assert declarations == [namespace + "payload"]
audit = "\n".join("#print axioms " + d for d in declarations) + "\n"
checked_path = root / "inventor_audit_checked_negative.lean"
checked_path.write_text(source + "\n" + audit)
command = ["lake", "env", "lean", str(checked_path)]
run = subprocess.run(
    command,
    cwd="/Users/mike/Dev/ctrl/lean",
    capture_output=True,
    text=True,
    timeout=120,
    check=False,
)
log = run.stdout + run.stderr
(root / "inventor_audit_negative.log").write_text(log)
assert run.returncode == 0, log
# Exact parsing logic copied from the read-only original verify_benchmarks.py.
records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
empty = re.findall(r"'([^']+)' does not depend on any axioms", log)
axioms = {n: sorted({a.strip() for a in ax.split(",") if a.strip()}) for n, ax in records}
actual_record = dict(axioms)
assert namespace + "forbiddenAuditFixture" in actual_record[namespace + "payload"]
axioms.update({n: [] for n in empty})
allowed = {"propext", "Classical.choice", "Quot.sound"}
accepted = set(axioms) == set(declarations) and all(set(ax) <= allowed for ax in axioms.values())
assert accepted
assert axioms == {namespace + "payload": []}
# A duplicate-aware parser rejects this exact output, but cannot in general
# authenticate arbitrary producer-controlled stdout merely by regex syntax.
all_names = [name for name, _ in records] + empty
duplicate_rejected = len(all_names) != len(set(all_names))
assert duplicate_rejected
out = {
    "fixture_is_deliberately_invalid_for_acceptance": True,
    "lean_exit_code": run.returncode,
    "command": command,
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "checked_source_sha256": hashlib.sha256(checked_path.read_bytes()).hexdigest(),
    "actual_kernel_report": actual_record,
    "spoofed_empty_records": empty,
    "original_parser_final_map": axioms,
    "original_parser_accepts": accepted,
    "duplicate_aware_parser_rejects_this_fixture": duplicate_rejected,
    "boundary": "Lean correctly reports the forbidden axiom. Only the external "
    "audit parser is fooled. Requires producer control over generated "
    "Lean source/stdout; not a claim current fixed generator emits it. "
    "No theorem in this negative fixture is promoted or accepted.",
}
(root / "inventor_audit_probe.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
