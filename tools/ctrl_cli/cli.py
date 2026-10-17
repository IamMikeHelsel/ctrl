#!/usr/bin/env python3
"""
ctrl CLI: Developer velocity, rapid verification, and search acceleration suite
for formal controls, estimation, vision, and Lean 4 proofs.
"""

import sys
import argparse
import subprocess
from pathlib import Path

# ANSI Color Codes
BOLD = "\033[1m"
GREEN = "\033[32m"
BLUE = "\033[34m"
CYAN = "\033[36m"
YELLOW = "\033[33m"
RED = "\033[31m"
MAGENTA = "\033[35m"
DIM = "\033[2m"
RESET = "\033[0m"

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
TOOLS_DATA_DIR = REPO_ROOT / "tools" / "data"


def print_banner():
    banner = rf"""{BOLD}{CYAN}
       _       _ 
  ___ | |_ _ _| |
 / __|| __| '__| |   Lean 4 Formal Systems & Control Theory
| (__ | |_| |  | |   Machine-Checked Estimation, Controls & Vision
 \___| \__|_|  |_|   v1.0.0
{RESET}"""
    print(banner)


def run_check(args):
    """Run proof verification and axiom check."""
    cmd = [str(SCRIPTS_DIR / "check.sh")]
    if args.fast:
        cmd.append("-f")
    if args.file:
        cmd.append(args.file)

    print(f"{BOLD}{BLUE}▶ Running verification...{RESET} {' '.join(cmd)}")
    res = subprocess.run(cmd, cwd=str(REPO_ROOT))
    sys.exit(res.returncode)


def run_scratch(args):
    """Run rapid isolated lemma scratch checker."""
    cmd = [str(SCRIPTS_DIR / "scratch_check.sh")]
    if args.strict:
        cmd.append("--strict")
    if args.imports:
        cmd.extend(["-i", args.imports])
    if args.code:
        cmd.extend(["-c", args.code])
    if args.file:
        cmd.append(args.file)

    res = subprocess.run(cmd, cwd=str(REPO_ROOT))
    sys.exit(res.returncode)


def run_search(args):
    """Search Mathlib and Lean symbols using Loogle."""
    cmd = [str(SCRIPTS_DIR / "loogle.sh")]
    if args.limit:
        cmd.extend(["-n", str(args.limit)])
    if args.module:
        cmd.extend(["-m", args.module])
    if args.json:
        cmd.append("--json")
    cmd.append(args.query)

    res = subprocess.run(cmd, cwd=str(REPO_ROOT))
    sys.exit(res.returncode)


def run_triage(args):
    """Execute rapid bounty screening against awards PRs and plby/lean-proofs."""
    from .triage import run_bounty_filter

    run_bounty_filter(args, REPO_ROOT, TOOLS_DATA_DIR)


def run_tactics(args):
    """Show available ControlTactics macros and lemmas."""
    print(
        f"\n{BOLD}{CYAN}=== ControlsLean.Tactics.ControlTactics Reference ==={RESET}\n"
    )
    categories = [
        (
            "Quadratic Form Reductions",
            [
                (
                    "quad_transpose",
                    "quad Mᵀ x = quad M x",
                    "Invariance under matrix transpose",
                ),
                ("quad_skew", "Mᵀ = -M → quad M x = 0", "Skew-symmetric vanishing"),
                (
                    "quad_fromBlocks_diag",
                    "quad (fromBlocks A 0 0 D) [u; v] = quad A u + quad D v",
                    "Block decoupling",
                ),
                (
                    "quad_fromBlocks_symm",
                    "quad (fromBlocks A B Bᵀ D) [u; v] = quad A u + 2*(u ⬝ᵥ (B *ᵥ v)) + quad D v",
                    "Symmetric blocks",
                ),
                (
                    "posDef_iff_quad_pos",
                    "Matrix.PosDef M ↔ Mᵀ = M ∧ ∀ x ≠ 0, 0 < quad M x",
                    "PosDef equivalence",
                ),
            ],
        ),
        (
            "Riccati & Parallel Sum Formulations",
            [
                (
                    "inv_parallel_sum",
                    "(P * R / (P + R))⁻¹ = P⁻¹ + R⁻¹",
                    "Precision harmonic addition",
                ),
                (
                    "riccati_lft_form",
                    "P * R / (P + R) + Q = ((R + Q) * P + Q * R) / (P + R)",
                    "Normalized LFT form",
                ),
                (
                    "riccati_lft_sub",
                    "riccati P₁ - riccati P₂ = R² * (P₁ - P₂) / ((P₁ + R)(P₂ + R))",
                    "Geometric contraction factor",
                ),
                (
                    "riccati_fixed_iff_quadratic",
                    "riccati P = P ↔ P² - Q P - Q R = 0",
                    "DARE fixed point",
                ),
            ],
        ),
        (
            "Discrete Lyapunov Stability Chaining",
            [
                (
                    "lyapunov_geometric_iterate",
                    "V (f x) ≤ ρ * V x → V (f^[k] x₀) ≤ ρ^k * V x₀",
                    "Arbitrary map contraction",
                ),
                (
                    "quad_lyapunov_geometric",
                    "quad P (A *ᵥ x) ≤ ρ * quad P x → quad P ((A^k) *ᵥ x₀) ≤ ρ^k * quad P x₀",
                    "LTI system quadratic contraction",
                ),
                (
                    "quad_lyapunov_step",
                    "quad P (A *ᵥ x) - quad P x = - quad (P - Aᵀ * P * A) x",
                    "Discrete Lyapunov step",
                ),
            ],
        ),
        (
            "Automated Macros",
            [
                (
                    "quad_simp",
                    "Simplifies block quadratic forms, matrix transposes, and scalings",
                    "Tactic",
                ),
                (
                    "riccati_lft_norm",
                    "Normalizes parallel sums and rational Riccati terms",
                    "Tactic",
                ),
                (
                    "posdef_to_quad",
                    "Converts Matrix.PosDef hypotheses to dotProduct and quad goals",
                    "Tactic",
                ),
            ],
        ),
    ]

    for cat_name, items in categories:
        print(f"{BOLD}{YELLOW}▶ {cat_name}:{RESET}")
        for name, form, desc in items:
            print(
                f"  {GREEN}{name:<28}{RESET} {CYAN}{form:<46}{RESET} {DIM}# {desc}{RESET}"
            )
        print()


def run_playbook(args):
    """View the proof engineering playbook."""
    playbook_file = REPO_ROOT / "docs" / "playbook.md"
    if not playbook_file.exists():
        print(f"{RED}Error: playbook not found at {playbook_file}{RESET}")
        sys.exit(1)

    with open(playbook_file, "r") as f:
        print(f.read())


def run_status(args):
    """Show library build and verification status."""
    print_banner()
    audit_file = REPO_ROOT / "scripts" / "Audit.lean"
    theorems = []
    if audit_file.exists():
        with open(audit_file) as f:
            for line in f:
                if line.startswith("#print axioms"):
                    theorems.append(line.strip().split()[-1])

    lean_files = list((REPO_ROOT / "ControlsLean").glob("**/*.lean"))

    print(f"{BOLD}Repository Status:{RESET}")
    print(
        f"  • Modules:              {GREEN}{len(lean_files)}{RESET} files in ControlsLean/"
    )
    print(
        f"  • Headline Theorems:    {GREEN}{len(theorems)}{RESET} registered in scripts/Audit.lean"
    )
    print(f"  • Lean Toolchain:       {CYAN}leanprover/lean4:v4.36.0-rc1{RESET}")
    print(
        f"  • Axiom Policy:         {GREEN}Strict (propext, Classical.choice, Quot.sound only){RESET}"
    )
    print()

    print(f"{BOLD}Registered Headline Theorems:{RESET}")
    for i, thm in enumerate(theorems, 1):
        print(f"  {DIM}{i:2d}.{RESET} {thm}")
    print()


def run_loop(args):
    """Run local LLM proof loop with fast scratchpad auto-correction."""
    from .loop import run_loop_cli

    run_loop_cli(args)


def main():
    parser = argparse.ArgumentParser(
        prog="ctrl",
        description="ctrl CLI: Acceleration suite for Lean 4 formal control theory & estimation.",
    )
    subparsers = parser.add_subparsers(dest="command", help="Available subcommands")

    # Command: loop
    p_loop = subparsers.add_parser(
        "loop", help="Local LLM proof loop with fast scratchpad auto-correction"
    )
    p_loop.add_argument(
        "goal", nargs="?", help="Lean theorem/lemma to prove or file containing theorem"
    )
    p_loop.add_argument("-f", "--file", help="Path to file containing theorem")
    p_loop.add_argument(
        "-m",
        "--model",
        default="qwen2.5-coder:7b",
        help="Ollama model (default: qwen2.5-coder:7b)",
    )
    p_loop.add_argument(
        "-u",
        "--url",
        default="http://localhost:11434",
        help="Ollama base URL (default: http://localhost:11434)",
    )
    p_loop.add_argument(
        "-i",
        "--imports",
        default="ControlsLean",
        help="Lean module imports (default: ControlsLean)",
    )
    p_loop.add_argument(
        "-t",
        "--max-tries",
        type=int,
        default=3,
        help="Max auto-correction tries per lemma (default: 3)",
    )
    p_loop.add_argument(
        "--temperature",
        type=float,
        default=0.1,
        help="Model sampling temperature (default: 0.1)",
    )
    p_loop.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Lean elaboration timeout per try in seconds (default: 60.0)",
    )
    p_loop.add_argument(
        "--benchmark",
        action="store_true",
        help="Run canonical benchmark suite across ControlsLean lemmas",
    )
    p_loop.add_argument(
        "--json",
        action="store_true",
        help="Output benchmark or loop result in JSON format",
    )
    p_loop.add_argument(
        "-v", "--verbose", action="store_true", help="Enable verbose iteration logging"
    )

    # Command: check
    p_check = subparsers.add_parser(
        "check", help="Verify proof library, check axioms, and scan for escape hatches"
    )
    p_check.add_argument(
        "file", nargs="?", help="Specific .lean file to check (default: all)"
    )
    p_check.add_argument(
        "-f",
        "--fast",
        action="store_true",
        help="Fast mode: skip Lake rebuild and audit",
    )

    # Command: scratch
    p_scratch = subparsers.add_parser(
        "scratch", help="Rapid sub-second isolated lemma checking"
    )
    p_scratch.add_argument("file", nargs="?", help="Scratch file path")
    p_scratch.add_argument("-c", "--code", help="Inline Lean code string to check")
    p_scratch.add_argument(
        "-i",
        "--imports",
        default="ControlsLean",
        help="Module imports (default: ControlsLean)",
    )
    p_scratch.add_argument(
        "-s", "--strict", action="store_true", help="Reject sorry/admit"
    )

    # Command: search
    p_search = subparsers.add_parser(
        "search", help="Semantic & type-directed search across Mathlib (via Loogle)"
    )
    p_search.add_argument(
        "query", help="Loogle query, e.g. 'Matrix.PosDef', '(x : ℝ) : 0 < Real.exp x'"
    )
    p_search.add_argument(
        "-n", "--limit", type=int, default=5, help="Maximum results to return"
    )
    p_search.add_argument("-m", "--module", help="Filter by module prefix")
    p_search.add_argument("--json", action="store_true", help="Output results as JSON")

    # Command: triage
    p_triage = subparsers.add_parser(
        "triage", help="Ultra-fast bounty screening (JSP, Erdős, Conjectures)"
    )
    p_triage.add_argument(
        "candidates", nargs="*", help="Candidates (IDs, file paths, or stdin)"
    )
    p_triage.add_argument(
        "-s",
        "--status",
        choices=["solved", "open", "all"],
        default="solved",
        help="Filter status",
    )
    p_triage.add_argument(
        "-v", "--verbose", action="store_true", help="Show rejection reasons"
    )
    p_triage.add_argument(
        "--strict",
        action="store_true",
        help="Zero-competition mode (reject closed PRs too)",
    )
    p_triage.add_argument("--json", action="store_true", help="JSON output format")
    p_triage.add_argument(
        "-m", "--markdown", action="store_true", help="Markdown table output format"
    )
    p_triage.add_argument(
        "--ids-only", action="store_true", help="Output only surviving IDs"
    )

    # Command: tactics
    subparsers.add_parser(
        "tactics", help="List and inspect ControlsLean tactics and helper macros"
    )

    # Command: playbook
    subparsers.add_parser(
        "playbook", help="Print the Lean 4 Controls proof engineering playbook"
    )

    # Command: status
    subparsers.add_parser(
        "status", help="Show verified modules, registered axioms, and toolchain info"
    )

    args = parser.parse_args()

    if not args.command:
        print_banner()
        parser.print_help()
        sys.exit(0)

    handlers = {
        "loop": run_loop,
        "check": run_check,
        "scratch": run_scratch,
        "search": run_search,
        "triage": run_triage,
        "tactics": run_tactics,
        "playbook": run_playbook,
        "status": run_status,
    }

    handlers[args.command](args)


if __name__ == "__main__":
    main()
