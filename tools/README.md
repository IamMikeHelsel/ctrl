# `ctrl` Acceleration Tools Suite

A command-line interface and automation toolkit designed to speed up Lean 4 formalization, inner-loop proof verification, Mathlib discovery, and open-problem triage.

---

## Quickstart

Run `./ctrl` from the repository root:
```bash
./ctrl --help
```

---

## Commands

### 1. `ctrl check [file] [-f]`
Verify proofs, check axioms, and scan for escape hatches (`sorry`, `admit`, `axiom`).
```bash
# Verify whole library (build + strict axiom audit)
./ctrl check

# Verify single file
./ctrl check ControlsLean/Controls/Gramian.lean

# Fast single-file check (bypass Lake replay & audit)
./ctrl check -f ControlsLean/Controls/PolePlacement.lean
```
*Built-in safeguard:* Automatically discovers and links Lake caches (`.lake`) in worktrees or clones, aborting before any runaway Mathlib rebuild can occur.

---

### 2. `ctrl scratch [-c "code" | file] [-s]`
Rapid sub-second isolated lemma sandbox. Test ideas without compiling whole files.
```bash
# Inline snippet testing
./ctrl scratch -c "example : 1 + 1 = 2 := by rfl"

# Check scratch file allowing sorry during exploration
./ctrl scratch scratch/my_test.lean

# Strict mode: fail if sorry/admit is present
./ctrl scratch -s scratch/my_test.lean
```

---

### 3. `ctrl search <query> [-n limit]`
Semantic & type-directed search across Mathlib via Loogle (responds in 200–400ms without local index overhead).
```bash
# Search by theorem/definition name
./ctrl search "Matrix.PosDef"

# Search by type proposition
./ctrl search "(x : ℝ) : 0 < Real.exp x"

# Search by goal pattern
./ctrl search "⊢ _ + 0 = _"
```

---

### 4. `ctrl triage [candidates...] [-v]`
Ultra-fast bounty screening against `TheJustinSunPrize/awards` PRs and `plby/lean-proofs` (screens 294 problems in **0.18s**).
```bash
# Screen default solved catalog
./ctrl triage

# Screen specific candidates with detailed conflict breakdown
./ctrl triage -v JSP-000078 JSP-000264 JSP-001059

# Strict zero-competition mode (rejects closed PRs too)
./ctrl triage --strict
```

---

### 5. `ctrl tactics`
Interactive cheat sheet and documentation for `ControlsLean.Tactics.ControlTactics` (Lyapunov geometric chaining, Riccati LFTs, parallel sum inversions, quadratic forms).
```bash
./ctrl tactics
```

---

### 6. `ctrl playbook`
Displays the Lean 4 Proof Engineering Playbook (`docs/playbook.md`) with solutions to high-frequency gotchas.
```bash
./ctrl playbook
```

---

### 7. `ctrl status`
Displays repository health, registered headline theorems (40 verified), toolchain revisions, and axiom hygiene.
```bash
./ctrl status
```

---

### 8. `ctrl synergy` — cross-domain unlock lens
Weighted graph over the idea catalog (`docs/AGENT_IDEA_INDEX.json`) and research candidates (`docs/SYNERGY_WEIGHTS.json`). Answers "what does X unlock", "what should an agent pick up next", and "which strong domain pairs have no concrete project yet". Every subcommand takes `--json` for agent consumption.
```bash
./ctrl synergy matrix                      # domain x domain unlock weights
./ctrl synergy unlock CTRL-01              # out-edges, in-edges, two-hop reach
./ctrl synergy rank -c -k industrialize    # rank research candidates of one kind
./ctrl synergy rank -g "legged robot safety kernel" -d codegen_certification -n 10
./ctrl synergy next -b 12                  # greedy plan within 12 engineer-weeks
./ctrl synergy gaps                        # strong domain edges with 0 idea edges
./ctrl synergy path ROBO-01 EST-01         # best weighted chain between ideas
./ctrl synergy validate                    # schema + referential integrity
python3 -m unittest discover -s tools/tests
```
Scoring recipe and coefficients live in `docs/SYNERGY_WEIGHTS.json` under `scoring`; edit the JSON, not the code, to retune. Research candidates follow the schema documented in `docs/RESEARCH_FRONTIER_2026-10.md`.
