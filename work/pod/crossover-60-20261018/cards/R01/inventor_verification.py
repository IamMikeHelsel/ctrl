"""Bind the isolated Lean primitive to the inspected original source formula."""

import hashlib
import json
import re
from pathlib import Path

here = Path(__file__).parent
source = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/certificate-03/builder/Kernel.lean"
)
local = here / "inventor_duplicate.lean"
original, copied = source.read_text(), local.read_text()


def body(text, name):
    pattern = rf"def {name}\b[^:=]*(?::[^=]*)?:=\s*(.*?)(?=\n(?:noncomputable )?def |\n(?:lemma|theorem) |\Z)"
    match = re.search(pattern, text, re.S)
    assert match is not None
    return re.sub(r"\s+", "", match.group(1))


assert body(original, "P") == body(copied, "P")
assert body(original, "F0") == body(copied, "F0")
log = (here / "inventor_duplicate.log").read_text()
assert log.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 5
assert "sorryAx" not in log
result = {
    "original_primitive_source": str(source),
    "original_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "local_lean_sha256": hashlib.sha256(local.read_bytes()).hexdigest(),
    "P_and_F0_bodies_equal_after_whitespace_normalization": True,
    "lean_command": "lake env lean /Users/mike/Dev/ctrl/work/pod/crossover-60-20261018/cards/R01/inventor_duplicate.lean",
    "lean_working_directory": "/Users/mike/Dev/ctrl/lean",
    "toolchain": Path("/Users/mike/Dev/ctrl/lean/lean-toolchain").read_text().strip(),
    "kernel_exit_code": 0,
    "audited_declarations": 5,
    "axioms": ["propext", "Classical.choice", "Quot.sound"],
    "initial_path_error": "First invocation used a relative output path from lean/; file creation and replay failed. Corrected to absolute path before the successful replay; not a failed mathematical claim.",
    "limits": "Standalone primitive instantiation and interval implication; does not replay original plant proof, verify transport, or establish physical trajectory existence.",
}
(here / "inventor_verification.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
