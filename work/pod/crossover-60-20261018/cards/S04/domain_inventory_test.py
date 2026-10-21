"""Read-only source inventory probe; own synthetic project, no source modifications."""

import hashlib
import importlib.util
import json
from pathlib import Path

CARD = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/scripts/sync_audit.py"
)
spec = importlib.util.spec_from_file_location("source_inventory", SOURCE)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.PROJECT = CARD / "domain_inventory_fixture"
modules, records = module.inventory()
expected = {"Fixture.indented_public", "Fixture.attributed_public", "Fixture.plain_public"}
actual = {r["name"] for r in records}
assert actual == {"Fixture.plain_public"}
report = {
    "source": str(SOURCE),
    "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "modules": modules,
    "expected_public": sorted(expected),
    "inventoried_public": sorted(actual),
    "omitted_public": sorted(expected - actual),
    "claim": "Source regex omission on a valid toy module; not evidence of omitted unsafe current theorems.",
}
(CARD / "domain_inventory_result.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
