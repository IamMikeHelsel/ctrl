"""Prepare a fresh 44 proof workspace; never modify an existing checkout or run."""

import argparse
import hashlib
import json
import shutil
from pathlib import Path, PurePosixPath


def prepare(destination, factory, contracts=None):
    here = Path(__file__).resolve().parent
    root = Path(destination).resolve()
    factory = Path(factory).resolve()
    if root.exists():
        raise ValueError("Destination already exists; no overwrite or reseal")
    core = factory / "core/loop.py"
    if not core.is_file():
        raise ValueError("Expected the existing 44 core/loop.py")
    contracts = Path(contracts).resolve() if contracts else here / "contracts.json"
    tasks = json.loads(contracts.read_text())
    if not isinstance(tasks, list) or not 1 <= len(tasks) <= 5:
        raise ValueError("Use one to five bounded contracts per workspace")
    ids, files = set(), set()
    for task in tasks:
        for field in ("id", "file", "domain", "imports", "statement", "purpose", "hint"):
            if not isinstance(task.get(field), str) or not task[field].strip():
                raise ValueError(f"Missing contract field: {field}")
        path = PurePosixPath(task["file"])
        if path.is_absolute() or ".." in path.parts or any(p.startswith(".") for p in path.parts):
            raise ValueError("Unsafe proof path")
        if task["id"] in ids or task["file"] in files:
            raise ValueError("Duplicate task id or proof file")
        if not all(c.isalnum() or c == "-" for c in task["id"]):
            raise ValueError("Unsafe task id")
        ids.add(task["id"])
        files.add(task["file"])
    for name in ("control", "acceptance", "tasks", "reference", "project/proofs", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    shutil.copy2(core, root / "control/loop.py")
    shutil.copy2(here / "backend.py", root / "control/backend.py")
    shutil.copy2(here / "supervise.py", root / "control/supervise.py")
    shutil.copy2(here / "check.py", root / "acceptance/check.py")
    shutil.copy2(contracts, root / "acceptance/contracts.json")
    shutil.copy2(factory / "LICENSE", root / "reference/44-LICENSE")
    queue = []
    for stage, task in enumerate(tasks, 1):
        (root / "project" / task["file"]).write_text("")
        queue.append(
            {
                "id": task["id"],
                "class": task["domain"],
                "stage": stage,
                "depends": [],
                "files": [task["file"]],
                "prompt": task["purpose"]
                + "\nFrozen Lean Prop:\n"
                + task["statement"]
                + "\nReturn only the tactic body AFTER 'unfold statement'. Begin with intro as needed."
                + " No by wrapper, imports, declarations, comments, options or escape hatches.\n"
                + task["hint"],
            }
        )
    (root / "tasks/queue.json").write_text(json.dumps(queue, indent=2) + "\n")
    (root / "tasks/adapter.json").write_text('{"context_suffixes": [".txt"]}\n')
    (root / "tasks/contract.txt").write_text(
        "Produce Lean 4.33.1 tactic bodies for exact frozen statements. Mathlib is imported. "
        "Only the given proof text file may change. The checker wraps your body under "
        "theorem solution : statement and audits its axioms. No sorry/admit/axiom/native_decide, "
        "no declarations, comments, unsafe execution or set_option. "
        "Return JSON files map as instructed. Research helper only; no novelty or physical claim.\n"
    )
    (root / "project/.gitignore").write_text("")
    provenance = {
        "factory_source": str(core),
        "factory_sha256": hashlib.sha256(core.read_bytes()).hexdigest(),
        "contracts_sha256": hashlib.sha256(contracts.read_bytes()).hexdigest(),
        "authorship": "Codex authored contracts, hints and adapter; proof bodies await local inference.",
        "scope": f"{len(tasks)} bounded helper proofs; all 60 ideas indexed separately. Original timed campaign unchanged.",
    }
    (root / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    return provenance


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination")
    parser.add_argument("--factory", required=True)
    parser.add_argument("--contracts", help="Optional reviewed JSON batch of one to five contracts")
    args = parser.parse_args()
    print(json.dumps(prepare(args.destination, args.factory, args.contracts), indent=2))
