# Inner Loop & Verification Guide for Lean 4 Control Theory

This document describes the inner loop developer experience, cache safeguards, scratch lemma verification, and semantic search tooling in `ctrl`.

---

## 1. Lake Cache Safeguard (`scripts/ensure_cache.sh`)

### Problem
Mathlib 4 is massive (~5,000+ compiled modules, 7+ GB of build artifacts). When creating a new Git worktree (e.g. `git worktree add ../ctrl-claude-controls`) or a new clone, `.lake` is not cloned because `.lake` is git-ignored.

In early experiments, running `lake build` in an unlinked worktree triggered a near-disaster where Lake started re-downloading and attempting to re-compile Mathlib from scratch, exhausting CPU, memory, and time.

### Solution & Mechanics
`scripts/ensure_cache.sh` implements an automated pre-flight safeguard:
1. **Verification**: Checks if `.lake/packages/mathlib` exists.
2. **Broken Symlink Cleanup**: Detects if `.lake` is a dangling symlink (e.g. pointing to a removed directory) and cleans it up.
3. **Automated Discovery**: Searches candidate parent and sibling locations for an existing populated Mathlib cache:
   - Git worktree root (`git rev-parse --git-common-dir`)
   - `/Users/mike/lean-work/ControlsLean/.lake`
   - `../ControlsLean/.lake`
   - `../ctrl/.lake`
4. **Auto-Symlinking**: If a populated cache is found, it automatically links `.lake` to that cache (`ln -sfn <candidate> .lake`).
5. **Fail-Safe Gate**: If no populated cache is found anywhere, it halts immediately with exit code 1 and actionable remediation instructions, preventing any runaway `lake build` unless explicitly overridden via `ALLOW_FRESH_LAKE_BUILD=1`.

This safeguard is integrated directly into `scripts/check.sh` and `scripts/scratch_check.sh`.

---

## 2. Fast Scratch Inner Loop (`scripts/scratch_check.sh` & `--fast`)

### Problem
Proof engineering in Lean 4 requires rapid iteration: testing whether a lemma statement elaborates, whether hypotheses are consistent, and whether intermediate tactics close subgoals. Running a full `lake build` or full axiom audit across 10+ modules on every minor edit introduces unnecessary latency.

### Fast Scratch Runner (`scripts/scratch_check.sh`)
`scripts/scratch_check.sh` runs `lake env lean` directly on isolated files or snippets without building downstream dependencies.

#### Features
- **Zero Module Recompilation**: Directly elaborates the target file.
- **Auto-Ignored Scratch Files**: All scratch files in `scratch/` are pre-configured in `.gitignore`.
- **Flexible Input**: Supports file arguments, standard input, or inline `-c` snippets.
- **Scratchpad-Friendly**: Permits `sorry` and `admit` by default during active proof search, clearly reporting the count of open subgoals. Passes exit code 0 if elaboration succeeds.
- **Strict Mode (`-s, --strict`)**: Fails if any `sorry` or `admit` remains.
- **Execution Timing**: Reports elaboration time (typically 1–3s).

#### Examples
```bash
# 1. Check an isolated scratch file
scripts/scratch_check.sh scratch/my_lemma.lean

# 2. Check an inline snippet with an import
scripts/scratch_check.sh -i ControlsLean.Controls.Hurwitz2 -c "#check ControlsLean.Controls.IsHurwitz2"

# 3. Pipe a proof under construction via stdin
scripts/scratch_check.sh << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Pow.Real

lemma test_square_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x
EOF

# 4. Strict check (fails if sorry is present)
scripts/scratch_check.sh --strict scratch/my_lemma.lean
```

### Fast Option in `scripts/check.sh` (`--fast` / `-f`)
`scripts/check.sh` now supports a `--fast` flag:
```bash
# Check a single file quickly:
scripts/check.sh --fast ControlsLean/Controls/Hurwitz2.lean

# Check all library files without rebuilding whole lake graph or running axiom audit:
scripts/check.sh --fast
```

---

## 3. Semantic & Type Search in Mathlib (`loogle`)

### Research Findings

#### 1. Canonical Repository & Toolchain Compatibility
- The upstream repository is **`https://github.com/nomeata/loogle`** (authored by Joachim Breitner, hosted in collaboration with the Lean FRO).
  *(Note: `pit-claudel/loogle` does not exist; Clément Pit-Claudel is known for interactive proof UI tools like `company-coq`, but Loogle is maintained by Joachim Breitner).*
- Loogle is built for Lean 4 and Mathlib. It compiles cleanly with `leanprover/lean4:v4.36.0-rc1`.

#### 2. Trade-off Analysis: `lakefile.toml` Dependency vs. API Wrapper

| Dimension | Option A: `lakefile.toml` Dependency | Option B: Public Loogle API / `scripts/loogle.sh` |
|---|---|---|
| **Configuration** | `[[require]] name = "loogle"` in `lakefile.toml` | Zero config change to `lakefile.toml` |
| **Manifest Pollution** | Adds Loogle + transitive packages to `lake-manifest.json` | Clean git status, no lockfile changes |
| **Local Indexing Overhead** | **High**: Building local Mathlib `.loogle-index` requires parsing 100k+ declarations, taking 3–5 min and >4 GB RAM | **Zero**: Sub-second queries (200–400 ms) |
| **Offline Capability** | Yes (after local index is built) | Requires internet access |
| **Agent Usability** | Needs `lake exe loogle` with index management | Instantly callable via `scripts/loogle.sh "<query>"` |

**Recommendation**: Use `scripts/loogle.sh` as the primary search workflow for agents and developers. It provides instant, formatted results with docstrings and module paths without polluting `lakefile.toml` or loading multi-gigabyte memory indexes.

If offline local binary execution is ever strictly required:
```bash
# Standalone local build (outside lakefile.toml):
git clone https://github.com/nomeata/loogle ~/.local/share/loogle
cp /Users/mike/lean-work/ctrl/lean-toolchain ~/.local/share/loogle/
(cd ~/.local/share/loogle && lake build)

# Local query:
lake env ~/.local/share/loogle/.lake/build/bin/loogle --module Mathlib "Matrix.PosDef"
```

#### 3. Using `scripts/loogle.sh`

`scripts/loogle.sh` queries the live Mathlib search index and pretty-prints results:

```bash
# 1. Search by name or prefix
scripts/loogle.sh "Matrix.PosDef"

# 2. Search by equality or rewrite pattern
scripts/loogle.sh "Real.sqrt _ * Real.sqrt _"

# 3. Search by type / proposition signature
scripts/loogle.sh "(x : ℝ) : 0 < Real.exp x"

# 4. Search by target goal shape
scripts/loogle.sh "⊢ _ + 0 = _"

# 5. Limit results and filter by module
scripts/loogle.sh --limit 5 --module "Mathlib.LinearAlgebra" "PosDef"

# 6. Output raw JSON for programmatic agent processing
scripts/loogle.sh --json "Controllable"
```

---

## 4. Verification Workflow Summary

| Task | Command | Speed |
|---|---|---|
| Verify cache link | `scripts/ensure_cache.sh` | < 0.1s |
| Test isolated scratch snippet | `scripts/scratch_check.sh -c "..."` | ~1–3s |
| Test scratch file | `scripts/scratch_check.sh scratch/test.lean` | ~1–3s |
| Fast check single library file | `scripts/check.sh --fast ControlsLean/Controls/Hurwitz2.lean` | ~3s |
| Full build, sorry check & axiom audit | `scripts/check.sh` | ~7–10s |
| Search Mathlib declarations/types | `scripts/loogle.sh "<query>"` | ~0.3s |
