# ctrl 
## Control Theory, Robotics, State Estimation, Vision & Open Math Research in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.36.0--rc1-brightgreen)](https://github.com/leanprover-community/mathlib4)
[![ControlsLean Modules](https://img.shields.io/badge/ControlsLean-55%20Verified%20Modules-success)](ControlsLean.lean)
[![Axiom Audit](https://img.shields.io/badge/Axiom%20Audit-445%20Headline%20Theorems-success)](scripts/Audit.lean)
[![Runtime status](https://img.shields.io/badge/Runtime-separate%20research%20checkout-informational)](site/adopt.html)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**`ctrl`** is a Lean 4 library for reasoning about controllers, state estimation, robotics and machine vision. Reuse a precise statement and its proof, then check that your model satisfies the hypotheses. The library also contains formalizations of published mathematical results and separate open research.

**What this checkout provides:** public Lean sources, build/audit scripts, documentation and saved research animations. Python robotics references, C99/IEC 61131-3 Structured Text generators and MuJoCo benchmark sources described below live in a separate research checkout; they are **not installed by cloning this branch**. A theorem-name binding or simulator result is not proof of executable or physical safety.

Start with [your existing library](site/consumers.html), the [adoption guide](site/adopt.html), [research pipeline](site/pipeline.html), or [novelty assessment](site/novelty.html), browse the [application examples](site/index.html#pillars), or read [CONTRIBUTING.md](CONTRIBUTING.md). The [combination guide](site/index.html#combinations) explains what additional work connects individual results into a system.

Run `scripts/check.sh` to build and audit the public control library. Headline declarations are checked against Lean's permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The Erdős lab uses its separate statement-binding checks below. These checks establish the stated mathematical results, not compiler correctness or hardware conformance.

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
uv run erdos targets --tab formalize    # scored targets (Drive: lean/erdos-data)
uv run erdos check --all               # verified so far: Erdős #261, #834 (part ii), #931
uv run erdos spark prove NNN            # local Leanstral prover on the Spark
```

Docs: [docs/erdos-lab/](docs/erdos-lab/README.md) covers the architecture, the CLI contract, the
dev → test → improve loop with its subagents in `.claude/agents/`, machine setup and targets.

---

## Availability and evidence

| Layer | Available here? | What it supports | What remains to do |
| :--- | :--- | :--- | :--- |
| **Lean control, estimation and vision results** | Public sources and audit | Mathematical implications with explicit hypotheses; see the module map below | Match the plant, dimensions, units, timing and uncertainty assumptions to your application |
| **Python and generated runtime kernels** | Separate research checkout | 48 registered functions: 42 domain functions, 4 benchmark entry points and 2 code-generation helpers; selected exact/numerical regression tests | Publish a reproducible runtime package, validate implementation/refinement and compile for the intended target |
| **Reported model benchmarks** | Saved animations and summaries here; runtime reproduction elsewhere | The reported MuJoCo cases include 39.4% lower peak tracking error versus a matched-pole CTC baseline and 4.1% lower total modeled motor loss; detailed task-specific values are below | Reproduce the exact environment; test comparable baselines, actuator limits and physical model conformance. These percentages are not general product guarantees |
| **Open mathematics and system integration** | Mixed public and research-branch artifacts; see the roadmap | Partial results, bounded certificates and proposed integrations | Close the named proof or implementation gaps. No percentage of an open problem being solved is asserted |

The website's 14 catalog families (11 documented-result families and 3 marked in work) are a navigation grouping, **not** a count of deployable functions. They are distinct from the separate runtime inventory of 42 domain functions. No layer above is labeled production-verified merely because its mathematics compiles.

---

## 1. Public Mathematical Components

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
    ├── architecture.md                      # Design principles, matrix representations & proof idioms
    ├── landscape.md                         # 3-way survey (ctrl vs LeanForControl vs Mathlib)
    ├── playbook.md                          # Proof engineering playbook & gotchas guide
    └── proposals/                           # Technical research proposals (00 through 09)
```

---

## 2. Proof Techniques and Reported Research Results

### 2.1 Spectral-Free Matrix Control & Estimation Proofs
Standard textbooks rely on complex Jordan canonical forms or Perron–Frobenius spectral theory to prove DARE uniqueness, LQG stability, and ISS bounds—machinery that is notoriously brittle to formalize. What **worked cleanly in Lean 4**:
1. **Forced-Observer Zero-Step Escape (`DAREDetectable.lean`)**: Proved Kwakernaak–Sivan detectable DARE Schur stability (`dare_schur_of_detectable`) and uniqueness (`dare_unique_of_detectable`) for positive semidefinite $Q = C^\top C \succeq 0$ without eigenvalues by inducting along the unforced trajectory whenever stage dissipation vanishes.
2. **Square-Root-Free Matrix Peter–Paul Identity (`ISS.lean`)**: Bypassed matrix square roots $P^{1/2}$ entirely via the exact algebraic identity:
   $$(x+y)^\top P (x+y) + \varepsilon\, x^\top P x - (1+\varepsilon)\, x^\top P x - \left(1+\varepsilon^{-1}\right) y^\top P y = \varepsilon^{-1}(\varepsilon x - y)^\top P (\varepsilon x - y) \ge 0,$$
   yielding explicit discrete-time ISS sublevel invariants (`quad_iss_of_stein_explicit`, `iss_invariant_sublevel`).
3. **Indefinite $H_\infty$ Minimax Completion of Squares (`BoundedRealHInf.lean`)**: Formalized the discrete-time Bounded Real Lemma and worst-case disturbance gain $w_k^* = (M_\gamma(P))^{-1} B^\top P A x_k$ via a saddle-point completion of squares (`hinf_stage_completion_of_squares`, `hinf_l2_gain_bound`, `hinf_worstCase_disturbance_tight`).
4. **Closed-Form 3D Conic Duality for Multi-Contact Robotics (`LorentzConeCBF.lean` & `ManipulatorTracking.lean`)**: Proved that a 4-contact bilinear ZMP + proportional shear allocator realizes arbitrary 3D forces inside second-order Lorentz friction cones with **identically zero 3D Euler torque** ($\dot{L} = 0$), and proved Slotine–Li passivity tracking ($\dot{V} = -s^\top K_D s$) without inverting $M(q)$.

### 2.2 Reported Research Benchmarks: Model and Runtime Scope

The separate `crossover-research-2026-10-19` checkout reports 48 registered Python functions (42 domain functions, 4 benchmarks and 2 code-generation helpers). Named Lean references provide traceability; they do not formally extract or verify the Python implementation. Selected kernels have generated C99/Structured Text and finite differential tests. The four MuJoCo cases below are **reported configured simulations**, not fresh runs from this public checkout or hardware measurements. A compiled C test does not validate an IEC compiler, PLC scan behavior or worst-case execution time.

Energy values depend on the stated motor/loss model. Lower modeled Joule loss is not a measured winding-temperature reduction; lower jerk is not a universal energy or vibration guarantee. Combined integrations must be tested rather than adding percentages from separate experiments.

| Closed-Loop Benchmark / Target | Baseline | Research Controller / Implementation | Reported Model Outcome |
| :--- | :--- | :--- | :--- |
| **6-DOF Arm Disturbance & Impact Rejection** (`run_arm6dof_disturbance_iss_hinf_benchmark`) | **Strong Baseline**: Tuned high-gain CTC ($K_p=416, K_d=42$): Peak err $0.0271\,\text{rad}$ (Nominal low-gain PD: $4.038\,\text{rad}$) | Modeled $H_\infty$ + Backstepping + Sontag CLF ($\gamma_{\text{cert}} = 0.20$): Peak err **$0.0164\,\text{rad}$**, $\ell_2$-gain **$0.00246$** | **`-39.42%` peak error vs. tuned CTC** (**`-39.59%` RMS**; `-99.59%` vs. nominal PD) |
| **6-DOF Arm Electromechanical Energy** (`run_arm6dof_septic_energy_benchmark`) | Classical 5th-order Minimum-Jerk ($\eta = 0$): $E_{\text{dyn}} = 773.18\,\text{J}$ | Selected seventh-degree motion profile ($\eta = -11$; inertial-term optimum): $E_{\text{dyn}} = 599.45\,\text{J}$ | **`-4.10%` total $\int\|\tau\|^2 dt$** (gravity-dominated) / **`-22.47%` dynamic Joule loss** (theoretical `-18.33%`) |
| **3D 4-Contact Quadruped Emergency Braking** (`run_quadruped_zmp_cbf_benchmark`) | Unshielded forward lunge toward wall at $x_{\lim} = 1.20\,\text{m}$ (tips over / slips) | 3D Lorentz-Cone CBF + Bilinear ZMP Allocator ($a_{\max} = \min(\mu, W/h_G) g$) | **Stops at $1.1920\,\text{m} < 1.20\,\text{m}$**, $100\%$ inside Lorentz cone ($f_{z,\min} = 22.14\,\text{N}$), **zero pitch/roll** ($\|\omega\|_{\max} = 1.64 \times 10^{-15}\,\text{rad/s}$) |
| **6-DOF $SE(3)$ Visual Servoing** (`run_se3_visual_servoing_benchmark`) | Classical IBVS under $155^\circ$ optical-axis rotation (retreats $5.76\times$ to $12.67\,\text{m}$) | Homography-Based Visual Servoing (HBVS) with log-depth $\dot{d} = -\lambda d \ln(d/d^*)$ | **In this simulation**: depth stays strictly monotone inside $[1.015\,\text{m}, 2.200\,\text{m}]$ |
| **C99 & IEC 61131-3 ST Codegen** (`compile_and_verify_c99_kernels`) | Python float64 reference kernels | `clang -std=c99 -O3 -Wall -Wextra -Werror` shared library (`ctypes`) | **`8.88e-16` maximum absolute discrepancy in reported finite C/Python tests**; not a universal ULP bound, program-equivalence proof or ST compiler result |

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
