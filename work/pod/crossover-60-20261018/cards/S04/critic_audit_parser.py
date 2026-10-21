"""Inspect independently compiled deliberately rejected axiom fixture output."""

import contextlib
import hashlib
import io
import json
import os
import re
import runpy
from pathlib import Path

P = Path(__file__).parent
text = (P / "critic_audit_negative.log").read_text()
assert "error:" not in text
records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
name = "LeanControls.Generated.InventorAuditNegative.payload"
assert records == [(name, "LeanControls.Generated.InventorAuditNegative.forbiddenAuditFixture")]
assert empty == [name]
parsed = {n: sorted({a.strip() for a in axes.split(",") if a.strip()}) for n, axes in records}
kernel = dict(parsed)
parsed.update({n: [] for n in empty})
assert parsed == {name: []}
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert all(set(a) <= allowed for a in parsed.values())
# The separate whole-project check_audit.py rejects this same stream.
box = P / "critic_check_audit_fixture"
(box / "evidence").mkdir(parents=True, exist_ok=True)
(box / "Audit.lean").write_text("#print axioms " + name + "\n")
(box / "evidence/axioms.log").write_text(text)
source = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/scripts/check_audit.py"
)
old = Path.cwd()
try:
    os.chdir(box)
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            runpy.run_path(str(source), run_name="__main__")
        except AssertionError:
            project_rejected = True
        else:
            project_rejected = False
finally:
    os.chdir(old)
assert project_rejected
out = {
    "status": "negative fixture reproduced, NOT an accepted mathematical result",
    "actual_Lean_compile_exit": 0,
    "kernel_dependency_report": kernel,
    "untrusted_spoofed_empty_record": empty,
    "benchmark_dictionary_parser_result": parsed,
    "benchmark_parser_wrongly_accepts": True,
    "whole_project_check_audit_rejects_same_log": True,
    "duplicate_rejecting_parser_rejects": len(records) + len(empty)
    != len(set([n for n, _ in records] + empty)),
    "checked_source_sha256": hashlib.sha256(
        (P / "critic_audit_negative.lean").read_bytes()
    ).hexdigest(),
    "scope": "Requires control over generated Lean source/stdout; current fixed JSON producer is not shown exploitable. Lean reports forbidden axiom correctly. No accepted theorem or proof count includes this fixture.",
}
(P / "critic_audit_parser.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
