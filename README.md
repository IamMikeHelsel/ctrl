# ctrl — Formal Control Theory, Estimation, Vision & Bounties in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.36.0--rc1-brightgreen)](https://github.com/leanprover-community/mathlib4)
[![Modules](https://img.shields.io/badge/Modules-25%20Verified-success)](ControlsLean.lean)
[![Axiom Audit](https://img.shields.io/badge/Axioms-139%20Theorems%20Standard%20Only-success)](scripts/Audit.lean)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**`ctrl`** (`https://github.com/IamMikeHelsel/ctrl`) is a verified library of formal, machine-checked mathematics in modern control theory, robotic state estimation, projective computer vision, and formal mathematics bounties, built on Lean 4 and Mathlib.

Every declaration in `ctrl` is 100% `sorry`-free, contains zero custom axioms or unverified escape hatches, and every public headline theorem (**139 audited theorems** across **25 modules**) is programmatically audited to depend solely on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Erdős lab: bounty formalization pipeline (`erdos/`, `erdos` CLI)

A separate Lake project, [`erdos/`](erdos/), holds machine-checked solutions to Erdős problems.
It pins DeepMind's Formal Conjectures (`d9ce556`, Lean v4.33.1) so challenge statements are copied
verbatim from the community source. It has to be a separate project because FC's toolchain differs
from ControlsLean's.

Every solution proves a frozen, human-approved `Challenge.ErdosNNN.statement : Prop`. A
uv-managed CLI checks the build, forbidden tokens, axioms, the `Expr.const` binding to the
statement, and that the challenge hasn't changed since approval:

```sh
uv sync && uv run erdos doctor          # Mac + DGX Spark toolchains
uv run erdos targets --tab formalize    # scored targets (data/erdos/)
uv run erdos check --all               # verified so far: Erdős #261, #834 (part ii), #931
uv run erdos spark prove NNN            # local Leanstral prover on the Spark
```

Docs: [docs/erdos-lab/](docs/erdos-lab/README.md) covers the architecture, the CLI contract, the
dev → test → improve loop with its subagents in `.claude/agents/`, machine setup and targets.

---

## Library Architecture & Modules (25 Verified Modules)

The library is organized under the top-level namespace `ControlsLean` and root file `ControlsLean.lean`, comprising **25 verified modules** spanning control engineering, estimation, vision, proof automation, and formal math bounties:

```text
ctrl/
├── ctrl                                 # Unified CLI runner (./ctrl check, scratch, search, triage, loop, status)
├── ControlsLean/
│   ├── Vision/
│   │   ├── Epipolar.lean                # Two-view calibrated epipolar geometry & essential matrix
│   │   ├── Homography.lean              # Planar projective collineations, duality & plane motion
│   │   ├── HomographyUniqueness.lean    # Four-point projective frame rigidity & PGL(3,K) uniqueness
│   │   ├── EightPoint.lean              # Eight-point algorithm & Kronecker rank-8 uniqueness
│   │   └── Triangulation.lean           # Two-view ray triangulation, closed-form depths & cheirality
│   ├── Controls/
│   │   ├── Hurwitz2.lean                # Second-order continuous-time Hurwitz polynomial stability
│   │   ├── Jury2.lean                   # Second-order discrete-time Jury / Schur polynomial stability
│   │   ├── Reachability.lean            # Subspace reachability & invariance without Cayley–Hamilton
│   │   ├── Observability.lean           # Coordinate-free observability duality & output injection
│   │   ├── DiscreteLyapunov.lean        # Discrete-time Lyapunov stability without matrix symmetry
│   │   ├── ConverseLyapunov.lean        # Converse DT Lyapunov, Stein telescoping & infinite series
│   │   ├── SmallGain.lean               # Nonlinear & linear discrete-time small-gain theorems
│   │   ├── Gramian.lean                 # Controllability Gramian & minimum-energy steering
│   │   ├── Companion.lean               # Companion matrices, characteristic polynomials & canonical form
│   │   ├── PolePlacement.lean           # Second-order canonical pole placement & deadbeat control
│   │   ├── PolePlacementGeneral.lean    # General-n single-input pole placement (Ackermann / canonical)
│   │   ├── Observer.lean                # Luenberger state observers & Separation Principle decoupling
│   │   └── MPCFeasibility.lean          # Constrained MPC recursive feasibility & CLF value descent
│   ├── Estimation/
│   │   ├── ScalarKalman.lean            # Scalar minimum-variance Kalman filter & Riccati contraction
│   │   ├── InformationFilter.lean       # Multi-dimensional Sherman–Morrison–Woodbury & precision update
│   │   ├── RiccatiConvergence.lean      # Scalar Riccati iterates converge geometrically to steady state
│   │   ├── AlphaBeta.lean               # Steady-state α–β filter & the Kalata relation
│   │   └── KalmanOptimality.lean        # Multivariate Bucy–Joseph covariance & MMSE trace optimality
│   ├── Tactics/
│   │   └── ControlTactics.lean          # Specialized macros, block quadratic forms & Lyapunov chaining
│   └── Bounty/
│       └── ErdosBounties.lean           # Uncontested Erdős solutions & counterexamples (#261, #931, #951, #143, #834)
├── tools/                               # Unified developer acceleration suite
│   ├── ctrl                             # Executable CLI
│   ├── ctrl_cli/                        # Python driver (check, scratch, search, triage, tactics, loop, flags)
│   ├── data/                            # Snapshots for sub-second bounty triage
│   └── README.md                        # Developer tooling documentation
├── scripts/
│   ├── check.sh                         # Full build, cache safeguard & automated axiom auditor
│   ├── scratch_check.sh                 # Rapid sub-second isolated lemma sandbox
│   ├── loogle.sh                        # 300ms semantic/type Mathlib lemma lookup
│   ├── ensure_cache.sh                  # Worktree cache auto-discovery & safeguard
│   ├── Audit.lean                       # Programmatic #print axioms check on 139 headline theorems
│   ├── sync.sh                          # Google Drive backup synchronization
│   └── bounty_triage.sh                 # Formal mathematics bounty triage utility
└── docs/
    ├── playbook.md                      # Proof engineering playbook & gotchas guide
    ├── INNER_LOOP.md                    # Fast verification and inner loop guide
    ├── landscape.md                     # 3-way landscape survey (ctrl vs LeanForControl vs Mathlib)
    ├── architecture.md                  # Design principles, matrix representations & proof idioms
    ├── roadmap.md                       # Prioritized roadmap of completed, medium, and long-term targets
    └── proposals/                       # Standalone technical research proposals with full citations
        ├── 00_integrated_pr_modules.md
        ├── 01_planar_homography.md
        ├── 02_controllability_gramian.md
        ├── 03_information_filter.md
        ├── 04_pole_placement_deadbeat.md
        ├── 05_converse_lyapunov.md
        ├── 06_homography_uniqueness.md
        ├── 07_mpc_recursive_feasibility.md
        ├── 08_multivariate_kalman_optimality.md
        └── 09_uncontested_erdos_bounties.md
```

---

## Audited Headline Theorems (139 Total Across 25 Modules)

All 139 headline theorems are registered in [`scripts/Audit.lean`](scripts/Audit.lean) and verified by [`scripts/check.sh`](scripts/check.sh):

| Discipline | Module | Core Mathematical Content | Key Audited Theorems |
|---|---|---|---|
| **Computer Vision** | `Vision/Epipolar.lean` | Calibrated two-view geometry; essential matrix $E = [t]_\times R$; coplanar incidence over general fields. | `epipolar_constraint`<br>`det_essential` |
| **Computer Vision** | `Vision/Homography.lean` | Projective collineations $H \in \mathrm{GL}(3, K)$; contragredient line transformations; collinearity invariance; planar scene two-view correspondence. | `lineTransform_dotProduct`<br>`det_homography_three_points`<br>`collinear_homography`<br>`plane_homography_constraint` |
| **Computer Vision** | `Vision/HomographyUniqueness.lean` | Four-point projective frame rigidity in $\mathbb{P}^2(K)$; uniqueness of homographies up to scale from 4 correspondences in general position. | `eq_diagonal_of_fixes_basis`<br>`eq_smul_one_of_fixes_canonical_frame`<br>`homography_unique_four_points`<br>`two_homographies_eq_smul_of_four_points`<br>`homography_rigidity_of_general_position` |
| **Computer Vision** | `Vision/EightPoint.lean` | Longuet-Higgins 8-point linear system; Kronecker constraint matrix rank-8 kernel uniqueness up to scale. | `finrank_ker_constraintMatrix`<br>`eq_smul_of_rank_eq_eight`<br>`essential_satisfies_constraints`<br>`eq_smul_essential` |
| **Computer Vision** | `Vision/Triangulation.lean` | Exact two-view ray triangulation; closed-form depth recovery; uniqueness under non-parallel rays; cheirality ($z_1, z_2 > 0$). | `depth₁_eq`, `depth₂_eq`<br>`depths_unique`<br>`scene_closedForm`<br>`exists_depths_iff`, `cheirality` |
| **Control Theory** | `Controls/Hurwitz2.lean` | Routh–Hurwitz stability criterion for monic degree-2 real polynomials; mass-spring-damper stability. | `isHurwitz2_iff` |
| **Control Theory** | `Controls/Jury2.lean` | Discrete-time Jury / Schur stability criterion for degree-2 polynomials: roots inside open unit disk iff $|b| < 1 \land |a| < 1 + b$. | `isSchur2_iff`<br>`isSchur2_iff_jury` |
| **Control Theory** | `Controls/Reachability.lean` | Finite-dimensional subspace stabilization at $k = \dim(V)$ without Cayley–Hamilton; state steering; feedback invariance. | `reach_eq_reach_finrank`<br>`controllable_iff_finrank`<br>`Controllable.exists_steer`<br>`controllable_feedback` |
| **Control Theory** | `Controls/Observability.lean` | Coordinate-free observability via dual annihilators; $(A, C)$ observable iff $(A^\top, C^\top)$ controllable; output-injection invariance. | `unobs_eq_dualCoannihilator_reach`<br>`observable_iff_controllable_dual`<br>`unobs_eq_unobs_finrank`<br>`observable_outputInjection` |
| **Control Theory** | `Controls/DiscreteLyapunov.lean` | Discrete-time Lyapunov asymptotic stability without requiring matrix symmetry on $P$; geometric trajectory contraction. | `tendsto_pow_mulVec_zero`<br>`PosDef.tendsto_pow_mulVec_zero` |
| **Control Theory** | `Controls/ConverseLyapunov.lean` | Converse DT Lyapunov theorem; finite Stein telescoping $A^\top P_N A - P_N = (A^N)^\top Q A^N - Q$; nilpotent and infinite-series PosDef Lyapunov solutions. | `stein_telescoping`<br>`posDef_lyapunovSum`<br>`converse_lyapunov_nilpotent`<br>`converse_lyapunov_of_tendsto`<br>`tendsto_pow_mulVec_zero_of_converse_lyapunov` |
| **Control Theory** | `Controls/SmallGain.lean` | Nonlinear and linear discrete-time small-gain theorems ($\gamma_1 \gamma_2 < 1$); interconnected boundedness & global asymptotic stability. | `small_gain`<br>`small_gain_bounded`<br>`small_gain_linear` |
| **Control Theory** | `Controls/Gramian.lean` | Discrete-time finite-horizon Controllability Gramian $W_k$; symmetry; PSD quadratic form; Kalman–Ho–Narendra minimum-energy steering. | `term_transpose`<br>`gramian_transpose`<br>`quad_gramian_term`<br>`gramian_steer` |
| **Control Theory** | `Controls/Companion.lean` | Companion matrices; characteristic polynomial identity; rank-1 feedback shifts coefficients directly; canonical controllability. | `charpoly_companion`<br>`charpoly_companion_feedback`<br>`exists_feedback_charpoly_eq`<br>`controllable_companion` |
| **Control Theory** | `Controls/PolePlacement.lean` | Second-order companion feedback synthesis; deadbeat nilpotent control $(A - B K_{\mathrm{db}})^2 = 0$; 2-step extinction; Hurwitz stabilization. | `closedLoop_eq`<br>`deadbeat_nilpotent`<br>`deadbeat_trajectory_zero`<br>`hurwitz_stabilization` |
| **Control Theory** | `Controls/PolePlacementGeneral.lean` | General-$n$ single-input Ackermann / canonical-basis pole placement for any controllable pair $(A, b)$ and target monic degree-$n$ polynomial. | `top_le_span_canonVec`<br>`toMatrix_canonBasis`<br>`charpoly_add_vecMulVec_eq`<br>`pole_placement` |
| **Control Theory** | `Controls/Observer.lean` | Luenberger state observers; input-invariant error dynamics $e_{k+1} = (A - LC) e_k$; Separation Principle characteristic polynomial decoupling. | `observer_error_step`<br>`observer_error_pow`<br>`closed_loop_separation_det`<br>`closed_loop_separation_charpoly` |
| **Control Theory** | `Controls/MPCFeasibility.lean` | Constrained receding-horizon Model Predictive Control; warm-start shift recursive feasibility; eternal closed-loop constraint satisfaction; CLF value descent. | `mpc_recursive_feasibility_step`<br>`mpc_closed_loop_feasible`<br>`mpc_value_descent`<br>`mpc_optimal_value_descent`<br>`mpc_closed_loop_cost_bound` |
| **State Estimation** | `Estimation/ScalarKalman.lean` | Optimal scalar Kalman gain minimizing posterior variance; harmonic precision additivity; discrete Riccati contraction mapping; fixed-point uniqueness. | `postVar_eq_opt_iff`<br>`inv_postVarOpt`<br>`riccati_fixed_unique` |
| **State Estimation** | `Estimation/InformationFilter.lean` | Ring-general Sherman–Morrison–Woodbury matrix inversion identity; two-sided inverse equivalence between Kalman covariance and Information filter update. | `woodbury_right_inv`<br>`woodbury_left_inv`<br>`woodbury_isInverse`<br>`kalman_information_equivalence` |
| **State Estimation** | `Estimation/RiccatiConvergence.lean` | Geometric convergence of discrete scalar Riccati iterates $|P_{k+1} - S| \le (R/(Q+R))^{2k} |P_1 - S|$ from any $P_0 \ge 0$; steady-state gain limit. | `abs_riccati_iterate_sub_le`<br>`tendsto_riccati_iterate`<br>`tendsto_gain_riccati_iterate` |
| **State Estimation** | `Estimation/AlphaBeta.lean` | Steady-state $\alpha\text{–}\beta$ tracking filter; algebraic Riccati reduction; the Kalata relation $\beta^2 / (1 - \alpha) = T^4 \sigma_w^2 / \sigma_v^2$. | `AlphaBeta.riccatiMap_eq_iff`<br>`AlphaBeta.kalata`<br>`AlphaBeta.exists_gains`<br>`AlphaBeta.exists_steadyState` |
| **State Estimation** | `Estimation/KalmanOptimality.lean` | Multivariate Bucy–Joseph stabilized covariance update; matrix completion of squares; Loewner PSD dominance; global MMSE trace optimality $\operatorname{tr}(P^+(K^*)) \le \operatorname{tr}(P^+(K))$. | `josephCov_transpose`<br>`josephCov_completion_of_squares`<br>`quad_josephCov_le`<br>`trace_josephCov_le`<br>`trace_josephCov_le_of_psd` |
| **Proof Tactics** | `Tactics/ControlTactics.lean` | Block quadratic form reductions; transpose/skew invariance; bidirectional `PosDef` to `quad` equivalences; parallel sum inversion; Lyapunov chaining. | `posDef_iff_quad_pos`<br>`quad_fromBlocks`<br>`inv_parallel_sum`<br>`riccati_lft_form`<br>`quad_lyapunov_geometric` |
| **Math Bounties** | `Bounty/ErdosBounties.lean` | Uncontested Erdős / JSP formalizations: Erdős #261 (Borwein–Loring identity & infinite solutions), #931 (symmetric $k_1=k_2=3$ prime-factor counterexamples), #951 (Beurling prime separation), #143 (1-separated logarithmic density), #834 (Li's 3-critical hypergraph). | `erdos_261_borwein_loring`<br>`erdos_261_parts_i`<br>`erdos_931_counterexample_symmetric_2_7`<br>`erdos_931_additional_condition_nonempty`<br>`erdos_951_isBeurlingPrimes`<br>`erdos_143_ncard_le_floor`<br>`erdos_834_parts_ii` |

---

## Verification & Build Instructions

```bash
export PATH="$HOME/.elan/bin:$PATH"

# Full build, escape-hatch ban, and 139-theorem axiom audit
bash scripts/check.sh

# Fast single-file verification (~1.5s - 2.5s)
bash scripts/check.sh ControlsLean/Controls/ConverseLyapunov.lean

# Sub-second bounty competition screening
./ctrl triage -s solved -v
./ctrl status
```
