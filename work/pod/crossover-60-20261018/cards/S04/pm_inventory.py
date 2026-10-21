"""Exercise actual source inventory on an isolated valid Lean syntax fixture."""

import hashlib
import importlib.util
import json
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/scripts/sync_audit.py"
)
spec = importlib.util.spec_from_file_location("s04_inventory", SOURCE)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
fixture = (HERE / "pm_inventory.lean").read_bytes()
with tempfile.TemporaryDirectory(prefix="s04-inventory-") as temp:
    project = Path(temp)
    (project / "LeanControls").mkdir()
    (project / "LeanControls" / "Probe.lean").write_bytes(fixture)
    module.PROJECT = project
    modules, records = module.inventory()
expected = ["S04Inventory.visible", "S04Inventory.indented", "S04Inventory.attributed"]
actual = [r["name"] for r in records]
assert actual == ["S04Inventory.visible"]
result = {
    "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "fixture_sha256": hashlib.sha256(fixture).hexdigest(),
    "compiler_expected_names": expected,
    "inventory_names": actual,
    "omitted_names": sorted(set(expected) - set(actual)),
    "scope": "Actual inventory execution; compiler acceptance recorded separately. The utility documents its restricted syntax; not a kernel failure or a claim existing declarations are omitted.",
}
(HERE / "pm_inventory.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
