# ctrl — Formal Control Theory, Estimation & Vision in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.36.0--rc1-brightgreen)](https://github.com/leanprover-community/mathlib4)
[![Axiom Audit](https://img.shields.io/badge/Axioms-Standard%20Only-success)](scripts/Audit.lean)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**`ctrl`** (`https://github.com/IamMikeHelsel/ctrl`) is a verified library of formal, machine-checked mathematics in modern control theory, robotic state estimation, and projective computer vision, built on Lean 4 and Mathlib.

Every declaration in `ctrl` is 100% `sorry`-free, contains zero custom axioms or unverified escape hatches, and every public headline theorem is programmatically audited to depend solely on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Library Architecture & Modules

The library is organized under the top-level namespace `ControlsLean` and root file `ControlsLean.lean`, comprising **12 verified modules** spanning control engineering, estimation, vision, and proof automation:

```text
ctrl/
├── ctrl                             # Unified CLI runner (./ctrl check, scratch, search, triage, loop)
├── ControlsLean/
│   ├── Vision/
│   │   ├── Epipolar.lean            # Two-view calibrated epipolar geometry & essential matrix
│   │   └── Homography.lean          # Planar projective collineations, duality & plane motion
│   ├── Controls/
│   │   ├── Hurwitz2.lean            # Second-order continuous-time Hurwitz polynomial stability
│   │   ├── Reachability.lean        # Subspace reachability & invariance without Cayley–Hamilton
│   │   ├── DiscreteLyapunov.lean    # Discrete-time Lyapunov stability without matrix symmetry
│   │   ├── Gramian.lean             # Controllability Gramian & minimum-energy steering
│   │   ├── PolePlacement.lean       # Canonical state-feedback pole placement & deadbeat control
│   │   └── Observer.lean            # Luenberger state observers & Separation Principle decoupling
│   ├── Estimation/
│   │   ├── ScalarKalman.lean        # Scalar minimum-variance Kalman filter & Riccati contraction
│   │   ├── InformationFilter.lean   # Multi-dimensional Sherman–Morrison–Woodbury & precision update
│   │   └── RiccatiConvergence.lean  # Scalar Riccati iterates converge geometrically to steady state
│   └── Tactics/
│       └── ControlTactics.lean      # Specialized macros, block quadratic forms & Lyapunov chaining
├── tools/                           # Unified developer acceleration suite
│   ├── ctrl                         # Executable CLI
│   ├── ctrl_cli/                    # Python driver (check, scratch, search, triage, tactics, loop, flags)
│   ├── data/                        # Snapshots for sub-second bounty triage
│   └── README.md                    # Developer tooling documentation
├── scripts/
│   ├── check.sh                     # Full build, cache safeguard & automated axiom auditor
│   ├── scratch_check.sh             # Rapid sub-second isolated lemma sandbox
│   ├── loogle.sh                    # 300ms semantic/type Mathlib lemma lookup
│   ├── ensure_cache.sh              # Worktree cache auto-discovery & safeguard
│   ├── Audit.lean                   # Programmatic #print axioms check on 45 headline theorems
│   ├── sync.sh                      # Google Drive backup synchronization
│   └── bounty_triage.sh             # Formal mathematics bounty triage utility
└── docs/
    ├── playbook.md                  # Proof engineering playbook & gotchas guide
    ├── INNER_LOOP.md                # Fast verification and inner loop guide
    ├── landscape.md                 # 3-way landscape survey (ctrl vs LeanForControl vs Mathlib)
    ├── architecture.md              # Design principles, matrix representations & proof idioms
    ├── roadmap.md                   # Prioritized roadmap of near, medium, and long-term targets
    └── proposals/                   # Standalone technical research proposals with full citations
        ├── 01_planar_homography.md
        ├── 02_controllability_gramian.md
        ├── 03_information_filter.md
        └── 04_pole_placement_deadbeat.md
```

---

## Audited Headline Theorems (45 Total)

All 45 headline theorems are registered in `scripts/Audit.lean` and checked by `scripts/check.sh`:

| Discipline | Module | Core Mathematical Content | Key Audited Theorems |
|---|---|---|---|
| **Computer Vision** | `Vision/Epipolar.lean` | Calibrated two-view geometry; essential matrix $E = [t]_\times R$; coplanar incidence over general fields. | `epipolar_constraint`<br>`det_essential` |
| **Computer Vision** | `Vision/Homography.lean` | Projective collineations $H \in \mathrm{GL}(3, K)$; contragredient line transformations; collinearity invariance via determinant scaling; planar scene two-view correspondence. | `lineTransform_dotProduct`<br>`det_homography_three_points`<br>`collinear_homography`<br>`plane_homography_constraint` |
| **Control Theory** | `Controls/Hurwitz2.lean` | Routh–Hurwitz stability criterion for monic degree-2 real polynomials; physical mass-spring-damper stability. | `isHurwitz2_iff` |
| **Control Theory** | `Controls/Reachability.lean` | Finite-dimensional subspace stabilization at $k = \mathrm{dim}(V)$ without Cayley–Hamilton; explicit state steering; state-feedback reachability invariance. | `reach_eq_reach_finrank`<br>`controllable_iff_finrank`<br>`Controllable.exists_steer`<br>`controllable_feedback` |
| **Control Theory** | `Controls/DiscreteLyapunov.lean` | Discrete-time Lyapunov asymptotic stability without requiring matrix symmetry on $P$; geometric rate of trajectory contraction. | `tendsto_pow_mulVec_zero`<br>`PosDef.tendsto_pow_mulVec_zero` |
| **Control Theory** | `Controls/Gramian.lean` | Discrete-time finite-horizon Controllability Gramian $W_k = \sum_{i=0}^{k-1} A^i B B^\top (A^i)^\top$; unconditional symmetry; positive semidefiniteness; Kalman–Ho–Narendra exact minimum-energy steering. | `term_transpose`<br>`gramian_transpose`<br>`quad_gramian_term`<br>`gramian_steer` |
| **Control Theory** | `Controls/PolePlacement.lean` | State-feedback synthesis in controllable canonical companion systems; deadbeat nilpotent control $(A - B K_{db})^2 = 0$; exact 2-step trajectory extinction; Hurwitz eigenvalue stabilization. | `closedLoop_eq`<br>`deadbeat_gain`<br>`deadbeat_nilpotent`<br>`deadbeat_trajectory_zero`<br>`hurwitz_stabilization` |
| **Control Theory** | `Controls/Observer.lean` | Luenberger state observers; input-invariant error dynamics $e_{k+1} = (A - LC) e_k$; error propagation $e_k = (A - LC)^k e_0$; block upper-triangular closed loop; Separation Principle characteristic polynomial decoupling. | `observer_error_step`<br>`observer_error_pow`<br>`closed_loop_separation_block`<br>`closed_loop_separation_det`<br>`closed_loop_separation_charpoly` |
| **State Estimation** | `Estimation/ScalarKalman.lean` | Optimal scalar Kalman gain minimizing posterior variance; harmonic precision additivity; discrete Riccati contraction mapping; fixed-point uniqueness. | `postVar_eq_opt_iff`<br>`inv_postVarOpt`<br>`riccati_fixed_unique` |
| **State Estimation** | `Estimation/InformationFilter.lean` | Ring-general Sherman–Morrison–Woodbury matrix inversion identity; mutual two-sided inverse equivalence between Kalman covariance update and Information matrix update $Y^+ = Y + C^\top R^{-1} C$. | `woodbury_right_inv`<br>`woodbury_left_inv`<br>`woodbury_isInverse`<br>`kalman_information_equivalence` |
| **State Estimation** | `Estimation/RiccatiConvergence.lean` | Geometric convergence of discrete scalar Riccati iterates $|P_{k+1} - S| \le (R/(Q+R))^{2k} |P_1 - S|$ from any $P_0 \ge 0$; steady-state Kalman gain limit. | `abs_riccati_iterate_sub_le`<br>`tendsto_riccati_iterate`<br>`tendsto_gain_riccati_iterate` |
| **Proof Tactics** | `Tactics/ControlTactics.lean` | Block quadratic form reductions; transpose/skew invariance; bidirectional `PosDef` to `quad` equivalences; parallel sum inversion; discrete Lyapunov chaining macros. | `posDef_iff_quad_pos`<br>`quad_fromBlocks`<br>`quad_transpose`<br>`inv_parallel_sum`<br>`riccati_lft_form`<br>`riccati_fixed_iff_quadratic`<br>`lyapunov_geometric_mulVec`<br>`quad_lyapunov_geometric` |

---

## Novelty & Comparative Positioning

1. **Comparison with Mathlib**:
   - Mathlib contains extensive foundational linear algebra, real/complex analysis, and topological groups, but has **no modules** for linear control systems, reachability analysis, Lyapunov stability, state estimation, Kalman filtering, or multi-view projective vision.
   - `ctrl` builds directly on Mathlib's matrix, ring, and topological modules while introducing foundational applied engineering mathematics.

2. **Comparison with `LeanForControl`** (Hespanha & Khalil):
   - `LeanForControl` specializes in single-input single-output (SISO) transfer functions and frequency-domain Bode/Nyquist methods in earlier Lean versions.
   - `ctrl` operates natively in Lean 4 on state-space multi-input multi-output (MIMO) formulations, proves reachability coordinate-free without relying on the Cayley–Hamilton theorem, requires no artificial symmetry on Lyapunov matrices $P$, and formalizes robotic estimation and vision algorithms absent in existing libraries.

3. **Generalization Beyond Textbooks**:
   - The epipolar and homography formulations hold over an arbitrary field $K$ and arbitrary $R$ (not restricted to $\mathrm{SO}(3)$ or $\mathbb{R}$).
   - The Sherman–Morrison–Woodbury inversion identity is proved for arbitrary non-commutative associative rings $R$, immediately specializing to finite matrix rings $M_{n \times n}(\mathbb{R})$ as well as infinite-dimensional operator algebras.

---

## Research Proposals & Documentation Suite

Detailed mathematical write-ups and novelty assessments are available in `docs/`:

- **[`docs/landscape.md`](docs/landscape.md)**: A systematic landscape survey comparing `ctrl`, `LeanForControl`, and Mathlib across 67 modules, toolchain divergence, and formalization voids.
- **[`docs/architecture.md`](docs/architecture.md)**: Design principles including our 3-tier representation strategy (coordinate-free linear maps, ring-general algebraic lemmas, and concrete `Fin n` matrices) and proof conventions.
- **[`docs/roadmap.md`](docs/roadmap.md)**: Prioritized roadmap of near, medium, and long-term milestones (Luenberger observers, Separation Principle, discrete algebraic Riccati equations, Kalman–Bucy filters, and 8-point algorithms).
- **[`docs/proposals/01_planar_homography.md`](docs/proposals/01_planar_homography.md)**: Research write-up on planar projective homographies with Hartley & Zisserman citations.
- **[`docs/proposals/02_controllability_gramian.md`](docs/proposals/02_controllability_gramian.md)**: Research write-up on discrete Controllability Gramians with Kalman, Ho, & Narendra citations.
- **[`docs/proposals/03_information_filter.md`](docs/proposals/03_information_filter.md)**: Research write-up on ring-level Woodbury identities and Information filtering with Anderson & Moore citations.
- **[`docs/proposals/04_pole_placement_deadbeat.md`](docs/proposals/04_pole_placement_deadbeat.md)**: Research write-up on deadbeat control and pole placement with Ackermann and Åström & Murray citations.
- **[`BOUNTIES.md`](BOUNTIES.md)**: Framework for triaging formal mathematics prize conjectures (Erdős problems, Justin Sun Prize, DeepMind Formal Conjectures).

---

## Verification & Build Instructions

### Prerequisites
- Lean 4 toolchain: `leanprover/lean4:v4.36.0-rc1` (managed via `elan`).
- Mathlib build cache: Shared via `.lake` symlink (`~7.2 GB`).

### Fast Local Verification
```bash
# Add elan to PATH if not already loaded
export PATH="$HOME/.elan/bin:$PATH"

# Run the complete verification suite (builds all modules, checks sorry/admit/axioms, audits headline theorems)
bash scripts/check.sh

# Verify a single module in rapid mode (~1.5s - 2.5s)
bash scripts/check.sh ControlsLean/Vision/Homography.lean
bash scripts/check.sh --fast ControlsLean/Controls/Gramian.lean

# Fast inner-loop scratch runner for isolated lemmas & proof sketches
./scripts/scratch_check.sh scratch/test.lean
./scripts/scratch_check.sh -i ControlsLean.Controls.Hurwitz2 -c "#check ControlsLean.Controls.IsHurwitz2"

# Semantic & type-based search in Mathlib using Loogle
./scripts/loogle.sh "Matrix.PosDef"
./scripts/loogle.sh "Real.sqrt _ * Real.sqrt _"
./scripts/loogle.sh "(x : ℝ) : 0 < Real.exp x"
```

### Expected Output
```text
Build completed successfully (4920 jobs).
Axiom audit passed for headline theorems: 37
OK: 10 file(s) checked, no sorry/admit/axiom
```

---

## Git Hygiene & Cache Management

The repository includes pre-flight safeguards to protect local build caches (~7.2 GB):
- **Lake Cache Safeguard (`scripts/ensure_cache.sh`)**: When creating new Git worktrees or fresh clones, `.lake` is not cloned by Git. The safeguard automatically detects populated sibling caches (in the worktree parent or `ControlsLean/.lake`) and auto-symlinks `.lake`, preventing catastrophic re-compilation of Mathlib from scratch.
- **Git Ignore**: `.lake` and `/.lake` are excluded so that symlinked build directories are never staged to Git. Scratch directories (`scratch/`, `scratch_*`) and binary/hash artifacts (`*.olean`, `*.ilean`, `*.c`, `*.hash`) are completely ignored.
- **Detailed Documentation**: See [docs/INNER_LOOP.md](docs/INNER_LOOP.md) for complete details on the inner loop experience, scratch testing, and Loogle usage.

## Research notebook

The [controls and mathematics notebook](research-notebook/README.md) preserves the independent
controls, Erdős, and Geometric Unity work: proof sources, paper drafts, source research,
verification logs, comparisons, and Manim explanations. It keeps its original toolchain pins and
proof scope separate from the root library. A [hash-checked sync tool](tools/sync_research_notebook.py)
keeps later work from remaining only in a chat workspace.
