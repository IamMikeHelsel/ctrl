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

## Theorem explainers (`tools/explainer/`)

Plain-language pages for proved theorems, with build-time MathML, an SVG diagram and two
manim animations. Workflow and writing rules: `.claude/skills/theorem-explainer/SKILL.md`.
Pages live in `site/explainers/<slug>/`.

```bash
# animations (LaTeX with sansmath + dvisvgm, ffmpeg, Inter font)
uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
  tools/explainer/render.py discrete-lyapunov
# page, index and content checks (node for KaTeX)
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py --all
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py --all --check
```
