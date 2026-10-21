"""Read-only replay of the archived independent exact enclosure review."""

import copy
import hashlib
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/filter-enclosure-08/grader/independent_enclosure.py"
)
d = runpy.run_path(str(SOURCE), run_name="critic_readonly_import")
before = d["integrity"]()
phases = json.loads(d["REF"].read_text())
cert = json.loads((d["B"] / "enclosure.json").read_text())
joins = d["check_reference"](phases)
phase_checks = d["audit_primary_certificate"](phases, cert)
rejected = []
for mutation in ["dynamics", "initial_filter_state", "phase_timestamp"]:
    bad = copy.deepcopy(cert)
    rec = bad["cases"][0]["phases"][0]
    if mutation == "dynamics":
        rec["matrix"][2][3] = str(F(rec["matrix"][2][3]) + 1)
    elif mutation == "initial_filter_state":
        rec["initial_grid_intervals"][3] = [str(10**600), str(10**600)]
    else:
        rec["start"] = "1/1000"
    try:
        d["audit_primary_certificate"](phases, bad)
    except AssertionError:
        rejected.append(mutation)
    else:
        raise ValueError("accepted corrupted " + mutation)
cases = []
for row in cert["cases"]:
    cases.append(
        d["run_case"](
            row["law"],
            F(row["k"]),
            F(row["witness_time"]),
            phases,
            row["position_error_enclosure_m"],
        )
    )
if d["integrity"]() != before:
    raise ValueError("historical source changed")
result = {
    "old_reviewer_source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "original_files_unchanged": True,
    "reference_joins": joins,
    "primary_phase_checks": phase_checks,
    "negative_controls_rejected": rejected,
    "cases": cases,
    "counterchecks": d["counterchecks"](),
    "scope": "Fresh replay of distinct historical reviewer algorithm, not a new Lean proof",
}
Path(__file__).with_name("critic_old_enclosure_replay.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print(
    json.dumps(
        {"intervals": [r["displayed_interval"] for r in cases], "negative_controls": rejected},
        indent=2,
    )
)
