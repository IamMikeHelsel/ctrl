"""Actual restricted source inventory plus zero-leakage-boundary checks."""

import hashlib
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
SRC = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/scripts/sync_audit.py"
)


def load(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


mod = load("critic_source_inventory", SRC)
box = P / "critic_inventory_fixture"
(box / "LeanControls").mkdir(parents=True, exist_ok=True)
fixture = (P / "pm_inventory.lean").read_bytes()
(box / "LeanControls/Probe.lean").write_bytes(fixture)
mod.PROJECT = box
modules, rows = mod.inventory()
assert [r["name"] for r in rows] == ["S04Inventory.visible"]
log = (P / "critic_pm_inventory_lean.log").read_text()
expected = ["S04Inventory.visible", "S04Inventory.indented", "S04Inventory.attributed"]
assert all("'" + n + "'" in log for n in expected) and "error:" not in log
source = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
checker = load("critic_original_expected", source / "check.py")
model = json.loads((source / "model.json").read_bytes())
witness = (F(1), F(0), F(0))
decisions = {}
for stage in ["baseline", "trial", "separated"]:
    decisions[stage] = {}
    for sign in ["nonnegative_d", "nonpositive_d"]:
        cs = checker.expected(model, stage, sign)
        decisions[stage][sign] = all(checker.dot(a, witness) <= b for a, b in cs)
assert all(decisions[s][b] for s in ["baseline", "trial"] for b in decisions[s])
assert not any(decisions["separated"].values())
out = {
    "status": "pass",
    "inventory_source_sha256": hashlib.sha256(SRC.read_bytes()).hexdigest(),
    "compiled_fixture_declarations": expected,
    "inventory_declarations": [r["name"] for r in rows],
    "zero_d_boundary": decisions,
    "scope": "Actual utility omits valid indented/attributed syntax; current historical audit completeness was not scanned. Sign cover may overlap safely atd0.",
}
(P / "critic_inventory.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
