# ctrl 
## Control Theory, Robotics, State Estimation, Vision & Open Math Research in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.36.0--rc1-brightgreen)](https://github.com/leanprover-community/mathlib4)
[![ControlsLean Modules](https://img.shields.io/badge/ControlsLean-55%20Verified%20Modules-success)](ControlsLean.lean)
[![Axiom Audit](https://img.shields.io/badge/Axiom%20Audit-445%20Headline%20Theorems-success)](scripts/Audit.lean)
[![Robotics Runtime](https://img.shields.io/badge/Robotics%20Runtime-48%20%40lean__theorem%20Kernels%20%7C%20C99%20%7C%20MuJoCo-informational)](docs/STATUS_AND_ROADMAP.md)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**`ctrl`** (`https://github.com/IamMikeHelsel/ctrl`) is a machine-checked Lean 4 library and executable verification lab for **modern control theory, robotics kinematics & dynamics, state estimation, projective computer vision, and open mathematical problems** (Erdős problems & the Byers–Nash $n=6$ skew-Hamiltonian conjecture).

Every theorem in `ctrl` is **100% `sorry`-free**, contains **zero `admit` or custom `axiom` declarations**, and is programmatically audited to depend strictly on Lean 4's three standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Executive Maturity Matrix: What's Ready, What Worked, What's Promising & What's In Work

| Tier | Status | Scope & Where It Lives | Key Highlights |
| :--- | :---: | :--- | :--- |
| **1. Ready to Use (Production-Verified)** | **READY** | `ControlsLean/` (**55 modules**, **15,260 LOC**, **906 theorems**, **445 audited headline theorems**) + `src/ctrl/robotics/` (**48 `@lean_theorem` Python functions**, **C99 & IEC 61131-3 ST codegen**, **4 MuJoCo 3.16.0 benchmarks**) | Full LQR/DARE/CARE/LQG/Kalman–Bucy, $H_\infty$ Bounded Real Lemma, ISS Peter–Paul envelopes, Backstepping & Sontag CLF, Slotine–Li manipulator tracking, $SO(3)/SE(3)$/Quaternion/PlanarArm/Unicycle kinematics, POMDP Smallwood–Sondik convexity, 3D Lorentz-cone CBF & ZMP allocation, 8-point/Homography/ICP vision, and **community-service formalizations of 25 published Erdős problem results**. |
| **2. What Worked (Verified Breakthroughs & Quantitative Gains)** | **PROVED + BENCHMARKED** | Closed-loop MuJoCo 3.16.0 benchmarks (`mujoco_benchmarks.py`), C99/PLC codegen (`codegen.py`), and spectral-free matrix proof techniques | **`-39.4%` peak tracking error vs. tuned high-gain CTC** (`-99.6%` vs. nominal low-gain PD) via $H_\infty$+ISS+Sontag CLF; **`-4.1%` total / `-22.47%` dynamic Joule loss** (theoretical `-18.33%`) via optimal septic trajectories ($\eta=-11$); **zero tip-over** 3D quadruped emergency braking (`28 ns` C99 filter); **zero camera retreat** in 6-DOF $SE(3)$ visual servoing; **$8.88 \times 10^{-16}$** C99-vs-Python parity. |
| **3. Promising Frontiers (90%+ Proved in Lean 4 + Exact $\mathbb{Q}$ Certificates)** | **HIGH PROMISE** | `lean/Research/ByersNash*.lean`, `Erdos885*.lean`, `Covering*.lean` (`crossover-research-2026-10-19` branch) | **Byers–Nash $n=6$ (`MF-13`)**: Unconditional rank $\le 4$ exclusion + 8-involution Haar identity + 15D Parseval decomposition of $\mathbb{K}_6$ + 10/10 non-Common-$T$ exact rational $LDL^\top \succ 0$ certificates ($s(A)^2 \in [1.1509, 3.4292] > 1$). **Erdős #885**: All 14 Class 1 & Class 2 genus-2 Jacobians proved absolutely simple ($\operatorname{End}(J_{\overline{\mathbb{Q}}}) = \mathbb{Z}$) + Cassels–Flynn & Cantor division-by-2 reductions. **Erdős #273**: Exact 23-smooth Euler product crossover $\frac{323323}{110592} < 3 < \frac{7436429}{2433024}$. |
| **4. Still In Work (Active Next Steps)** | **IN WORK** | `docs/STATUS_AND_ROADMAP.md` §4 | (a) Analytical cross-term closure between 1D $W_{pq}$-commuting ($J$) and 3D $W_{pq}$-anticommuting ($\{I_2,F,G\}$) off-diagonal blocks for $n=6$ Byers–Nash; (b) $p$-adic Coleman / Chabauty rank-1 annihilator formalization for $k=5$ Erdős #885; (c) Whole-body $SE(3)$ geometric tracking & multi-contact MPC integration in MuJoCo. |

---

## 1. What's Ready to Use Today

### 1.1 `ControlsLean`: 55 Machine-Checked Lean 4 Modules (445 Audited Headline Theorems)

```text
ctrl/
├── ControlsLean.lean                        # Root import (55 verified modules, 15,260 LOC, 906 theorems)
├── ControlsLean/
│   ├── Controls/                            # 27 Modules: Linear, Optimal, Robust & Nonlinear Control
│   │   ├── Hurwitz2.lean, Hurwitz3.lean     # 2nd- and 3rd-order Routh–Hurwitz continuous-time stability
│   │   ├── Jury2.lean                       # 2nd-order discrete-time Jury / Schur unit-disk stability
│   │   ├── Reachability.lean                # Subspace stabilization at k = dim(V) without Cayley–Hamilton
│   │   ├── Observability.lean               # Dual annihilator observability & output-injection invariance
│   │   ├── Gramian.lean                     # Controllability Gramian & Kalman–Ho–Narendra min-energy steering
│   │   ├── Companion.lean                   # Companion matrices & rank-1 characteristic polynomial shift
│   │   ├── PolePlacement.lean               # 2D companion pole placement & 2-step nilpotent deadbeat control
│   │   ├── PolePlacementGeneral.lean        # General-n single-input Ackermann / canonical pole placement
│   │   ├── DiscreteLyapunov.lean            # Discrete-time Stein Lyapunov stability without symmetry
│   │   ├── ConverseLyapunov.lean            # Converse DT Lyapunov theorem & infinite-series construction
│   │   ├── SchurLyapunov.lean               # Schur spectral contraction & infinite-horizon summability
│   │   ├── LQR.lean                         # Discrete LQR Bellman operator & Joseph completion of squares
│   │   ├── DAREExistence.lean               # Loewner monotone Riccati convergence & DARE existence
│   │   ├── DAREUniqueness.lean              # Stabilizing DARE uniqueness & closed-loop comparison
│   │   ├── LQROptimality.lean               # Infinite-horizon LQR optimality & cost-to-go convergence
│   │   ├── DAREDetectable.lean              # Spectral-free detectable DARE/LQR/Kalman & return-difference margins
│   │   ├── DAREBellman.lean                 # DARE Bellman residual, LQR completion of squares & closed-loop decay
│   │   ├── Observer.lean                    # Luenberger state observers & polynomial Separation Principle
│   │   ├── LQG.lean                         # Output-feedback LQG block-triangular asymptotic stability
│   │   ├── BoundedRealHInf.lean             # Minimal-hypothesis LQG & H_inf Bounded Real Lemma / l2-gain
│   │   ├── ISS.lean                         # Square-root-free matrix Peter–Paul identity & Stein-to-ISS bounds
│   │   ├── SmallGain.lean                   # Nonlinear & linear discrete-time small-gain theorems
│   │   ├── BarrierPassivity.lean            # Discrete-time Control Barrier Functions & passivity telescoping
│   │   ├── BacksteppingCLF.lean             # Strict-feedback n-step integrator backstepping & Sontag's CLF
│   │   ├── MPCFeasibility.lean              # Constrained receding-horizon MPC recursive feasibility & descent
│   │   └── IterativeLearning.lean           # Lifted Iterative Learning Control (ILC) & Arimoto convergence
│   ├── Estimation/                          # 10 Modules: Kalman Filtering, CARE, Least Squares & POMDPs
│   │   ├── ScalarKalman.lean                # Scalar MMSE Bayes update & harmonic precision additivity
│   │   ├── RiccatiConvergence.lean          # Scalar Riccati geometric contraction & steady-state limit
│   │   ├── InformationFilter.lean           # Ring-general Sherman–Morrison–Woodbury & Information equivalence
│   │   ├── AlphaBeta.lean                   # Steady-state α–β tracker & the Kalata tracking index relation
│   │   ├── KalmanOptimality.lean            # Multivariate Bucy–Joseph covariance & MMSE trace optimality
│   │   ├── SteadyStateKalman.lean           # Dual estimator DARE & steady-state Kalman gain
│   │   ├── KalmanBucy.lean                  # Continuous-time CARE, HJB calculus & Kalman–Bucy optimality
│   │   ├── KalmanBucyFilter.lean            # Kalman–Bucy covariance generator, DRE completion of squares & CARE
│   │   ├── LeastSquares.lean                # Normal equations, weighted LS & Sherman–Morrison recursive LS
│   │   └── POMDPBelief.lean                 # Bayesian belief simplex, PWLC convexity & Smallwood–Sondik backup
│   ├── Robotics/                            # 6 Modules: Lie Groups, Manipulators, Quaternions & Mobile Robots
│   │   ├── SO3Rodrigues.lean                # so(3) cubic identity & closed-form Rodrigues rotation theorem
│   │   ├── SE3Kinematics.lean               # 6x6 SE(3) twist adjoint functoriality & rigid kinematic ODE
│   │   ├── QuaternionRotation.lean          # Unit-quaternion SO(3) action, double cover & 1/2 q*omega ODE
│   │   ├── PlanarArm.lean                   # 2-link planar arm Jacobian, law of cosines & annulus IK
│   │   ├── Unicycle.lean                    # Differential-drive bijection, exact arc odometry & Kanayama CLF
│   │   └── ManipulatorTracking.lean         # Slotine–Li passivity & adaptive manipulator trajectory tracking
│   ├── Vision/                              # 8 Modules: Projective, Epipolar & Point-Cloud Geometry
│   │   ├── Epipolar.lean                    # Essential matrix E = [t]_x R & Longuet-Higgins constraint
│   │   ├── EssentialConstraints.lean        # Demazure cubic constraint 2 E E^T E - tr(E E^T) E = 0 & twist pair
│   │   ├── EightPoint.lean                  # 8-point Kronecker rank-8 kernel uniqueness up to scale
│   │   ├── Homography.lean                  # Planar collineation H = R + d^-1 t n^T & line duality
│   │   ├── HomographyUniqueness.lean        # 4-point projective frame rigidity & PGL(3,K) uniqueness
│   │   ├── CrossRatio.lean                  # Projective cross-ratio invariance, Möbius maps & harmonic ranges
│   │   ├── Triangulation.lean               # Exact two-view stereo depth triangulation & cheirality
│   │   └── Registration.lean                # Kabsch / ICP point-cloud registration centroid & trace reduction
│   ├── Tactics/
│   │   └── ControlTactics.lean              # Custom matrix_symm, quad_nonneg, loewner_mono & Riccati LFTs
│   └── Bounty/                              # 3 Modules: 25 Solved Erdős Problems & Counterexamples
│       ├── ErdosBounties.lean               # Erdős #261, #931, #951, #143, #834, #995, #1055, #1073, #1113...
│       ├── ErdosNewInsights.lean            # Erdős #370, #645 (universal 2-coloring <= 47), #493, #275, #873, #1125
│       └── ErdosWave2.lean                  # Erdős #1148, #1179, #1187, #311, #367, #455
├── scripts/
│   ├── check.sh                             # Full build, escape-hatch ban & 445-theorem axiom auditor
│   ├── Audit.lean                           # Programmatic #print axioms check on all 445 headline theorems
│   ├── scratch_check.sh                     # Sub-second isolated lemma sandbox
│   └── loogle.sh                            # 300ms semantic/type Mathlib lemma search
└── docs/
    ├── STATUS_AND_ROADMAP.md                # Comprehensive guide: Ready vs. Promising vs. In-Work
    ├── IDEA_PORTFOLIO_AND_SYNERGIES.md      # Domain-organized idea catalog, novelty/applicability & synergy graph
    ├── AGENT_IDEA_INDEX.json                # Machine-readable JSON index for autonomous agent review
    ├── SYNERGY_WEIGHTS.json                 # Weighted domain/idea unlock graph + research candidates (`./ctrl synergy`)
    ├── RESEARCH_FRONTIER_2026-10.md         # Scouted problems to explore / productionize / industrialize
    ├── architecture.md                      # Design principles, matrix representations & proof idioms
    ├── landscape.md                         # 3-way survey (ctrl vs LeanForControl vs Mathlib)
    ├── playbook.md                          # Proof engineering playbook & gotchas guide
    └── proposals/                           # Technical research proposals (00 through 09)
```

---

## 2. What's Worked: Key Mathematical & Engineering Breakthroughs

### 2.1 Spectral-Free Matrix Control & Estimation Proofs
Standard textbooks rely on complex Jordan canonical forms or Perron–Frobenius spectral theory to prove DARE uniqueness, LQG stability, and ISS bounds—machinery that is notoriously brittle to formalize. What **worked cleanly in Lean 4**:
1. **Forced-Observer Zero-Step Escape (`DAREDetectable.lean`)**: Proved Kwakernaak–Sivan detectable DARE Schur stability (`dare_schur_of_detectable`) and uniqueness (`dare_unique_of_detectable`) for positive semidefinite $Q = C^\top C \succeq 0$ without eigenvalues by inducting along the unforced trajectory whenever stage dissipation vanishes.
2. **Square-Root-Free Matrix Peter–Paul Identity (`ISS.lean`)**: Bypassed matrix square roots $P^{1/2}$ entirely via the exact algebraic identity:
   $$(x+y)^\top P (x+y) + \varepsilon\, x^\top P x - (1+\varepsilon)\, x^\top P x - \left(1+\varepsilon^{-1}\right) y^\top P y = \varepsilon^{-1}(\varepsilon x - y)^\top P (\varepsilon x - y) \ge 0,$$
   yielding explicit discrete-time ISS sublevel invariants (`quad_iss_of_stein_explicit`, `iss_invariant_sublevel`).
3. **Indefinite $H_\infty$ Minimax Completion of Squares (`BoundedRealHInf.lean`)**: Formalized the discrete-time Bounded Real Lemma and worst-case disturbance gain $w_k^* = (M_\gamma(P))^{-1} B^\top P A x_k$ via a saddle-point completion of squares (`hinf_stage_completion_of_squares`, `hinf_l2_gain_bound`, `hinf_worstCase_disturbance_tight`).
4. **Closed-Form 3D Conic Duality for Multi-Contact Robotics (`LorentzConeCBF.lean` & `ManipulatorTracking.lean`)**: Proved that a 4-contact bilinear ZMP + proportional shear allocator realizes arbitrary 3D forces inside second-order Lorentz friction cones with **identically zero 3D Euler torque** ($\dot{L} = 0$), and proved Slotine–Li passivity tracking ($\dot{V} = -s^\top K_D s$) without inverting $M(q)$.

### 2.2 Quantitative Controls & Robotics Performance Impact (MuJoCo 3.16.0 & C99/PLC Codegen)

In the `crossover-research-2026-10-19` branch (`src/ctrl/robotics/`), **48 Python functions** are bound via `@lean_theorem` to **223 Lean 4 theorems**, emitted to **zero-heap C99 and IEC 61131-3 Structured Text**, and benchmarked in closed loop in **MuJoCo 3.16.0**:

| Closed-Loop Benchmark / Target | Baseline | Lean-Verified Controller | Measured Gain |
| :--- | :--- | :--- | :--- |
| **6-DOF Arm Disturbance & Impact Rejection** (`run_arm6dof_disturbance_iss_hinf_benchmark`) | **Strong Baseline**: Tuned high-gain CTC ($K_p=416, K_d=42$): Peak err $0.0271\,\text{rad}$ (Nominal low-gain PD: $4.038\,\text{rad}$) | Verified $H_\infty$ + Backstepping + Sontag CLF ($\gamma_{\text{cert}} = 0.20$): Peak err **$0.0164\,\text{rad}$**, $\ell_2$-gain **$0.00246$** | **`-39.42%` peak error vs. tuned CTC** (**`-39.59%` RMS**; `-99.59%` vs. nominal PD) |
| **6-DOF Arm Electromechanical Energy** (`run_arm6dof_septic_energy_benchmark`) | Classical 5th-order Minimum-Jerk ($\eta = 0$): $E_{\text{dyn}} = 773.18\,\text{J}$ | Optimal 7th-order Septic ($\eta^* = -11$): $E_{\text{dyn}} = 599.45\,\text{J}$ | **`-4.10%` total $\int\|\tau\|^2 dt$** (gravity-dominated) / **`-22.47%` dynamic Joule loss** (theoretical `-18.33%`) |
| **3D 4-Contact Quadruped Emergency Braking** (`run_quadruped_zmp_cbf_benchmark`) | Unshielded forward lunge toward wall at $x_{\lim} = 1.20\,\text{m}$ (tips over / slips) | 3D Lorentz-Cone CBF + Bilinear ZMP Allocator ($a_{\max} = \min(\mu, W/h_G) g$) | **Stops at $1.1920\,\text{m} < 1.20\,\text{m}$**, $100\%$ inside Lorentz cone ($f_{z,\min} = 22.14\,\text{N}$), **zero pitch/roll** ($\|\omega\|_{\max} = 1.64 \times 10^{-15}\,\text{rad/s}$) |
| **6-DOF $SE(3)$ Visual Servoing** (`run_se3_visual_servoing_benchmark`) | Classical IBVS under $155^\circ$ optical-axis rotation (retreats $5.76\times$ to $12.67\,\text{m}$) | Homography-Based Visual Servoing (HBVS) with log-depth $\dot{d} = -\lambda d \ln(d/d^*)$ | **Eliminates camera-retreat pathology**: depth stays strictly monotone inside $[1.015\,\text{m}, 2.200\,\text{m}]$ |
| **C99 & IEC 61131-3 ST Codegen** (`compile_and_verify_c99_kernels`) | Python float64 reference kernels | `clang -std=c99 -O3 -Wall -Wextra -Werror` shared library (`ctypes`) | **`8.88e-16` max discrepancy** (1-ULP IEEE-754 double precision), zero heap allocation |

---

## 3. What Looks Promising & What's Still In Work

1. **Byers–Nash $n=6$ Skew-Hamiltonian Conjecture (`MF-13`)** (`lean/Research/ByersNash*.lean`):
   - **What Worked**: Proved orthogonal decoupling of $\mathcal{L}_A(X) = A^\top X + XA$ on $\mathbb{S}_n \oplus \mathbb{K}_n$, unconditional exclusion for $\operatorname{rank}(K) \le 4$, the 8-involution $(F,G)$-Klein Haar identity, the 15D Parseval decomposition of $\mathbb{K}_6$, and exact rational $LDL^\top \succ 0$ certificates for 10/10 non-Common-$T$ benchmark pairs ($s(A)^2 > 1$).
   - **In Work**: Analytical bounding of the cross-term between the 1D $W_{pq}$-commuting ($J$) and 3D $W_{pq}$-anticommuting ($\{I_2,F,G\}$) off-diagonal blocks when $\frac{1}{2}\|Y_{\text{off}}\|_F^2 > \frac{3}{4}\|Y_{\text{diag}}\|_F^2$.
2. **Erdős Problem #885 (Factor-Difference Sets & Genus-2 Chabauty)** (`lean/Research/Erdos885*.lean`):
   - **What Worked**: Proved that all 14 Class 1 & Class 2 genus-2 Jacobians have $\operatorname{End}(J_{\overline{\mathbb{Q}}}) = \mathbb{Z}$ (absolutely simple, ruling out elliptic-curve factor projections) and formalized degree-2 Mumford & 3-/5-point Cantor division-by-2 resultant squareness.
   - **In Work**: Formalizing the rank-1 Mordell–Weil generator certificate and $p$-adic Coleman integral root bound for $k=5$.
3. **Erdős Problem #273 ($p-1$ Covering Systems)** (`lean/Research/Covering*.lean`):
   - **What Worked**: Formalized theweighted CRT capacity engine and proved the exact 9-prime (23-smooth) Euler product threshold crossover $\frac{323323}{110592} < 3 < \frac{7436429}{2433024}$ (`smooth_covering_threshold_at_23`), proving that at least one prime $p \ge 23$ is mandatory in any $p-1$ covering system.
   - **In Work**: Extending branch-and-bound local obstruction certificates to higher smooth boxes.

---

## 4. Verification & Build Quick Start

```bash
export PATH="$HOME/.elan/bin:$PATH"

# Full build, escape-hatch ban, and 445-theorem axiom audit (55 modules)
bash scripts/check.sh

# Fast single-file verification (~1.5s - 2.5s)
bash scripts/check.sh ControlsLean/Controls/BoundedRealHInf.lean

# Sub-second bounty competition screening
./ctrl triage -s solved -v
./ctrl status
```

---

## 5. Documentation, Theorem Playbook & Web Presentation Guides

- **[`docs/THEOREM_AND_WEB_PRESENTATION_GUIDE.md`](docs/THEOREM_AND_WEB_PRESENTATION_GUIDE.md)** — **Theorem Authoring, Technical Narrative & Web Presentation Playbook**: How we structure constructive closed-form theorems in Lean 4, bridge the $\mathbb{R} \to \mathbb{Q} \to \text{C99} \to \text{MuJoCo}$ verification pipeline, write credible engineering claims against strong baselines, and design the web presentation (including reusable templates for private/internal portals).
- **[`docs/IDEA_PORTFOLIO_AND_SYNERGIES.md`](docs/IDEA_PORTFOLIO_AND_SYNERGIES.md)** — Domain-organized catalog of all mathematical and engineering ideas across 9 domains with novelty ratings, applicability ratings, and multi-module synergy blueprints.
- **[`docs/STATUS_AND_ROADMAP.md`](docs/STATUS_AND_ROADMAP.md)** — Comprehensive repository status, benchmark summaries, and active mathematical research roadmap.
- **[`docs/AGENT_IDEA_INDEX.json`](docs/AGENT_IDEA_INDEX.json)** — Machine-readable JSON index of all modules, theorems, Python kernels, C99 symbols, and synergy graphs for autonomous agents.
- **[`site/index.html`](site/index.html)** — Minimalist static web portal deployed to the `site` branch (`https://iammikehelsel.github.io/ctrl/`).
