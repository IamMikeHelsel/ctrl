# ctrl 
## Applied Math for Controls, Robotics, Simulation, Perception

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.36.0--rc1-brightgreen)](https://github.com/leanprover-community/mathlib4)
[![ControlsLean Modules](https://img.shields.io/badge/ControlsLean-55%20Verified%20Modules-success)](ControlsLean.lean)
[![Axiom Audit](https://img.shields.io/badge/Axiom%20Audit-445%20Headline%20Theorems-success)](scripts/Audit.lean)
[![Runtime status](https://img.shields.io/badge/Runtime-separate%20research%20checkout-informational)](site/adopt.html)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**`ctrl`** ([iammikehelsel.github.io/ctrl](https://iammikehelsel.github.io/ctrl/)) is an applied mathematics library for **controls, robotics, simulation, and perception**, backed by machine-checked proofs in Lean 4 (`ControlsLean/`, 55 modules, 445 audited headline theorems). Where a control, estimation, or contact-mechanics problem admits an exact completion of squares or conic projection, we state and prove the closed-form law in Lean 4, implement it in dual-mode Python (`float` + exact `Fraction`), emit fixed-loop C99 and IEC 61131-3 Structured Text, and benchmark it in MuJoCo 3.16.0 against tuned baselines.

- **Browse the interactive web portal**: **[iammikehelsel.github.io/ctrl](https://iammikehelsel.github.io/ctrl/)**
  - [4 Core Application Pillars & MuJoCo Rollouts](https://iammikehelsel.github.io/ctrl/#pillars) · [System Blueprints](https://iammikehelsel.github.io/ctrl/#combinations) · [End-User Library Map (ROS 2, MoveIt, OpenCV, MuJoCo)](site/consumers.html) · [Adoption Guide](site/adopt.html) · [60-Review Research Pipeline](site/pipeline.html) · [What Is New?](site/novelty.html) · [Synergy Lens](site/synergy.html)

---

## Architecture & Repository Layout

| Layer | Where It Lives | What It Provides | Scope & Verification Boundary |
| :--- | :--- | :--- | :--- |
| **1. Symbolic Theorems (Lean 4 over $\mathbb{R}/\mathbb{Q}$)** | `ControlsLean/` on `main` (**55 modules**, **445 audited headline theorems**) | Closed-form control, estimation, kinematics, and projective vision proofs (`0 sorry`, standard axioms only via `scripts/check.sh`). | Proves mathematical implications under stated model hypotheses; does not model IEEE-754 rounding or compiler behavior. |
| **2. Dual-Mode Python Reference** | `src/ctrl/robotics/` on `crossover-research-2026-10-19` (**48 `@lean_theorem` functions**: 42 domain + 4 benchmarks + 2 codegen helpers) | Reference implementations running on both IEEE-754 `float` and exact `fractions.Fraction` for zero-rounding rational regression tests. | Hand-written Python linked to Lean declarations by name and tested on rational/float grids (not formally extracted from Lean). |
| **3. Fixed-Loop C99 & IEC 61131-3 ST Codegen** | `src/ctrl/robotics/codegen.py` (**12 C99 functions**, **4 ST POUs**) | Zero-heap, solver-free C99 and PLC Structured Text kernels differential-tested against Python (`8.88e-16` max error on tested inputs). | Empirical differential parity on randomized inputs; target timing and PLC compiler behavior require target-specific validation. |
| **4. Multi-Body Physics Rollouts** | `src/ctrl/robotics/mujoco_benchmarks.py` + saved animations in `site/assets/` | 4 closed-loop MuJoCo 3.16.0 RK4 benchmarks comparing candidate laws against matched high-gain baselines (`-39.4%` impulse peak error vs. tuned CTC; `-22.5%` dynamic / `-4.1%` total modeled $I^2R$ loss). | Task- and model-specific simulation results; physical deployment requires plant identification and hardware testing. |

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

### 2.2 Closed-Loop MuJoCo 3.16.0 Benchmarks & Codegen Parity

On the `crossover-research-2026-10-19` branch (`src/ctrl/robotics/`), 48 Python functions are linked via `@lean_theorem` to 223 Lean 4 declarations, emitted to fixed-loop C99 and IEC 61131-3 Structured Text, and evaluated in closed loop in MuJoCo 3.16.0 against tuned baselines:

| Closed-Loop Benchmark / Target | Baseline | Candidate Law (`ctrl.robotics`) | Simulation Outcome |
| :--- | :--- | :--- | :--- |
| **6-DOF Arm Disturbance & Impact Rejection** (`run_arm6dof_disturbance_iss_hinf_benchmark`) | **Strong Baseline**: Tuned high-gain CTC ($K_p=416, K_d=42$): Peak err $0.0271\,\text{rad}$ (Nominal low-gain PD: $4.038\,\text{rad}$) | $H_\infty$ + Backstepping + Sontag CLF ($\gamma_{\text{cert}} = 0.20$): Peak err **$0.0164\,\text{rad}$**, $\ell_2$-gain **$0.00246$** | **`-39.42%` peak error vs. tuned CTC** (**`-39.59%` RMS**; `-99.59%` vs. nominal PD) |
| **6-DOF Arm Electromechanical Energy** (`run_arm6dof_septic_energy_benchmark`) | Classical 5th-order Minimum-Jerk ($\eta = 0$): $E_{\text{dyn}} = 773.18\,\text{J}$ | 7th-order septic profile ($\eta = -11$; inertial-term optimum): $E_{\text{dyn}} = 599.45\,\text{J}$ | **`-4.10%` total $\int\|\tau\|^2 dt$** (gravity-dominated) / **`-22.47%` dynamic Joule loss** (1D theory `-18.33%`) |
| **3D 4-Contact Quadruped Emergency Braking** (`run_quadruped_zmp_cbf_benchmark`) | Unshielded forward lunge toward wall at $x_{\lim} = 1.20\,\text{m}$ (tips over / slips) | 3D Lorentz-Cone CBF + Bilinear ZMP Allocator ($a_{\max} = \min(\mu, W/h_G) g$) | **Stops at $1.1920\,\text{m} < 1.20\,\text{m}$**, $100\%$ inside Lorentz cone ($f_{z,\min} = 22.14\,\text{N}$), **zero pitch/roll** ($\|\omega\|_{\max} = 1.64 \times 10^{-15}\,\text{rad/s}$) |
| **6-DOF $SE(3)$ Visual Servoing** (`run_se3_visual_servoing_benchmark`) | Classical IBVS under large optical-axis rotation (retreats $5.76\times$ to $12.67\,\text{m}$) | Homography-Based Visual Servoing (HBVS) with log-depth $\dot{d} = -\lambda d \ln(d/d^*)$ | **Eliminates optical-axis retreat**: depth stays monotone inside $[1.015\,\text{m}, 2.200\,\text{m}]$ |
| **C99 & IEC 61131-3 ST Codegen** (`compile_and_verify_c99_kernels`) | Python `float64` reference kernels | `clang -std=c99 -O3 -Wall -Wextra -Werror` shared library (`ctypes`) | **`8.88e-16` max discrepancy** across randomized differential tests, zero heap allocation |

### 2.3 Slotine–Li Adaptive Kernel for the Planar RR Arm (on `main`)

`src/ctrl/robotics/csrc/ctrl_slotine_li.c` implements `ctrl_slotine_li_torque`, a C99 kernel with no heap allocation. It computes $\tilde q = q - q_d$, $\dot q_r = \dot q_d - \Lambda\tilde q$, $s = \dot q - \dot q_r$, the regressor $Y(q,\dot q,\dot q_r,\ddot q_r)$, $\tau = Y\hat\theta - K_D s$ and $\dot{\hat\theta} = -\Gamma Y^\top s$. These are the definitions and sign conventions of `ManipulatorTracking.lean`. `ctrl.robotics.slotine_li` has the numpy reference and a `ctypes` binding, and `ctrl.robotics.planar_rr` has the arm model.

What is proved and what is only tested:

- **Lean** proves the instantaneous identity `slotine_li_adaptive_lyapunov_deriv`: if $M\dot s + Cs + K_D s = Y\tilde\theta$ (`hcl`), $\Gamma^{-1}\dot{\tilde\theta} = -Y^\top s$ (`hadapt`) and $\dot M - 2C$ is skew (`hskew`), then $\dot V = -s^\top K_D s$ for $V = \tfrac12 s^\top M s + \tfrac12\tilde\theta^\top\Gamma^{-1}\tilde\theta$. With $\hat\theta = \theta$ the corresponding result is `slotine_li_lyapunov_deriv`.
- **Not in Lean**: the rigid-body model. `PlanarArm.lean` proves kinematics only. The dynamics $M, C, g$ and the 5-parameter linear parameterization are the standard Lagrangian of the same `fk` geometry.
- **Tested** (`tests/test_slotine_li.py`, under 3 s):
  - The C kernel matches the numpy reference to $10^{-12}$ on random inputs.
  - $Y\theta = M\ddot q_r + C\dot q_r + g$ holds for every $\theta$.
  - $M$, $g$ and $C\dot q$ match the kinetic and potential energy of the `fk` geometry (by finite differences and Christoffel symbols).
  - `hskew`, `hcl` and `hadapt` hold for the closed loop.
  - $\dot V = -s^\top K_D s \le 0$ holds at random states.
  - A benchmark smoke run passes.
  - The cited Lean names exist in the Lean files.

**Payload-adaptation benchmark** (`uv run python -m ctrl.robotics.bench_slotine_li [--backend c]`). A 2-link arm in a vertical plane carries an unmodelled 2 kg tip payload and tracks a sum-of-sines reference for 40 s. The simulation is pure-numpy RK4 with dt = 1 ms. The initial joint offset is (0.3, −0.2) rad. Every controller starts from the payload-free parameters. Gains are $\Lambda = 4I$, $K_D = \mathrm{diag}(30, 15)$ and $\Gamma = 4I$.

| Controller | RMS $\|q - q_d\|$ (rad), whole run | RMS, last third | $\|\tilde\theta\|$ at 0 s → 40 s | Payload estimate |
| :--- | ---: | ---: | :---: | ---: |
| Slotine–Li adaptive | 0.0230 | 0.0021 | 4.64 → 0.28 | 1.91 kg |
| Slotine–Li with fixed $\hat\theta$ ($\Gamma = 0$, same gains) | 0.263 | 0.256 | 4.64 (fixed) | — |
| Computed torque with nominal parameters, $K_p = \lambda^2$, $K_v = 2\lambda$, $\lambda = 4$ | 1.28 | 1.32 | 4.64 (fixed) | — |
| Computed torque with nominal parameters, $\lambda = 10$ | 0.538 | 0.535 | 4.64 (fixed) | — |

The computed-torque rows are not gain-matched: their feedback stiffness $\hat M\lambda^2$ differs from Slotine–Li's $K_D\Lambda$. The fixed-$\hat\theta$ Slotine–Li row uses the same gains as the adaptive row.

**Lyapunov audit** of the adaptive run:
- $V$ never increases between steps, and it falls from 6.44 to 0.010.
- The pointwise residual $\dot V + s^\top K_D s$, computed from the simulated state, is at most $3\times10^{-14}$.
- The integrated balance $V(t) - V(0) + \int_0^t s^\top K_D s$ stays below $1.5\times10^{-4}$, which is RK4 and quadrature error.

A residual above round-off would mean that the kernel does not satisfy the theorem's hypotheses.

These are simulation results for one model, one reference trajectory and one gain set. They are not a hardware result.

---

## 3. Active Mathematical Frontiers & Community Formalizations

1. **Byers–Nash $n=6$ Skew-Hamiltonian Conditioning (`MF-13`)** (`lean/Research/ByersNash*.lean`):
   - **What Worked**: Proved orthogonal decoupling of $\mathcal{L}_A(X) = A^\top X + XA$ on $\mathbb{S}_n \oplus \mathbb{K}_n$, unconditional exclusion for $\operatorname{rank}(K) \le 4$, the 8-involution $(F,G)$-Klein Haar identity, the 15D Parseval decomposition of $\mathbb{K}_6$, and exact rational $LDL^\top \succ 0$ certificates for 10/10 non-Common-$T$ benchmark pairs ($s(A)^2 > 1$).
   - **In Work**: Analytical bounding of the cross-term between the 1D $W_{pq}$-commuting ($J$) and 3D $W_{pq}$-anticommuting ($\{I_2,F,G\}$) off-diagonal blocks.
2. **Community Formalizations (`erdos/` Lake Workspace & `ControlsLean/Bounty/`)**:
   - Alongside the control and robotics library, [`erdos/`](erdos/) (pinned to DeepMind's `formal-conjectures` `d9ce556`) and `ControlsLean/Bounty/` formalize published literature solutions and finite base cases (`uv run erdos check --all`; see [docs/erdos-lab/](docs/erdos-lab/README.md)).

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

# Slotine–Li C99 kernel: differential + Lyapunov tests, then the payload benchmark
uv run pytest tests/test_slotine_li.py
uv run python -m ctrl.robotics.bench_slotine_li --backend c
```

---

## 5. Documentation, Theorem Playbook & Web Presentation Guides

- **[`docs/THEOREM_AND_WEB_PRESENTATION_GUIDE.md`](docs/THEOREM_AND_WEB_PRESENTATION_GUIDE.md)** — **Theorem Authoring, Technical Narrative & Web Presentation Playbook**: How we structure constructive closed-form theorems in Lean 4, bridge the $\mathbb{R} \to \mathbb{Q} \to \text{C99} \to \text{MuJoCo}$ verification pipeline, write credible engineering claims against strong baselines, and design the web presentation (including reusable templates for private/internal portals).
- **[`docs/IDEA_PORTFOLIO_AND_SYNERGIES.md`](docs/IDEA_PORTFOLIO_AND_SYNERGIES.md)** — Domain-organized catalog of all mathematical and engineering ideas across 9 domains with novelty ratings, applicability ratings, and multi-module synergy blueprints.
- **[`docs/STATUS_AND_ROADMAP.md`](docs/STATUS_AND_ROADMAP.md)** — Comprehensive repository status, benchmark summaries, and active mathematical research roadmap.
- **[`docs/AGENT_IDEA_INDEX.json`](docs/AGENT_IDEA_INDEX.json)** — Machine-readable JSON index of all modules, theorems, Python kernels, C99 symbols, and synergy graphs for autonomous agents.
- **[`site/index.html`](site/index.html)** — Minimalist static web portal deployed to the `site` branch (`https://iammikehelsel.github.io/ctrl/`).
