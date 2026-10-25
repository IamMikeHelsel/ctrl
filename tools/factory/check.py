"""Frozen-statement, proof-body-only Lean acceptance for the local 44 loop."""

import json
import os
import re
import subprocess
import sys
import textwrap
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|opaque|implemented_by|native_decide|unsafe|"
    r"set_option|run_tac|run_elab|elab|macro|syntax|initialize|import|"
    r"namespace|section|end|theorem|lemma|def|abbrev|instance|attribute)\b|#|/-|-/|--"
)


def assemble(task, proof):
    if not proof.strip() or FORBIDDEN.search(proof):
        raise ValueError(
            "Only a tactic body is accepted; declarations/comments/escape hatches forbidden"
        )
    # Accept the conventional term wrapper without changing any proposition or tactic.
    proof = textwrap.dedent(proof).strip()
    if proof.splitlines()[0].strip() == "by":
        proof = textwrap.dedent("\n".join(proof.splitlines()[1:])).strip()
    if not proof:
        raise ValueError("Empty proof body")
    body = "\n".join("  " + line for line in proof.splitlines())
    return (
        task["imports"]
        + "\nset_option maxHeartbeats 400000\n"
        + "namespace Factory\n"
        + "def statement : Prop :=\n"
        + task["statement"]
        + "\n"
        + "theorem solution : statement := by\n  unfold statement\n"
        + body
        + "\n"
        + "example : statement := solution\n"
        + "#print axioms solution\nend Factory\n"
    )


def audit(output):
    if "warning:" in output or "sorryAx" in output:
        raise ValueError("Lean warning or untrusted axiom")
    found = re.findall(r"'Factory.solution' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    if not found and "'Factory.solution' does not depend on any axioms" in output:
        return []
    if len(found) != 1:
        raise ValueError("Expected exactly one solution axiom audit")
    axioms = {name.strip() for name in found[0].split(",") if name.strip()}
    if not axioms <= STANDARD_AXIOMS:
        raise ValueError(f"Nonstandard axioms: {sorted(axioms - STANDARD_AXIOMS)}")
    return sorted(axioms)


def main():
    stage = int(sys.argv[1])
    task = json.loads(Path("/acceptance/contracts.json").read_text())[stage - 1]
    proof = (Path("/project") / task["file"]).read_text()
    source = Path("/build") / f"stage-{stage}.lean"
    source.write_text(assemble(task, proof))
    cp = subprocess.run(
        ["/toolchain/bin/lean", str(source)],
        capture_output=True,
        text=True,
        timeout=90,
        env=os.environ,
    )
    output = cp.stdout + cp.stderr
    print(output, end="")
    if cp.returncode:
        raise SystemExit(cp.returncode)
    print(json.dumps({"axioms": audit(output), "statement_bound": True}))
    print(f"ACCEPTANCE_STAGE_{stage}_PASS")


if __name__ == "__main__":
    main()
