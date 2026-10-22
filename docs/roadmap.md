# Prioritized Roadmap of Next Efforts and Bounty Triage

**Author**: `ctrl` Documentation & Architecture Team  
**Date**: October 2026  
**Repository**: `https://github.com/IamMikeHelsel/ctrl`  
**Toolchain**: Lean 4 `v4.36.0-rc1`

---

## 1. Vision and Phased Strategy

The mission of `ctrl` is to become the canonical, machine-checked Lean 4 library for modern cyber-physical systems, robotics, control engineering, and state estimation.

Our development trajectory progresses through three deliberate horizons:
- **Near-Term (Delivered Additions)**: High-leverage, self-contained formalizations across Vision, Controls, and Estimation, machine-checked with zero `sorry` and standard axioms.
- **Medium-Term (Core Engineering Foundations)**: The quintessential structures of modern control: state observers and the Separation Principle, algebraic Riccati equations (DARE), continuous Kalman–Bucy filters, and the 8-point algorithm.
- **Long-Term & Research Frontiers**: Advanced optimal and nonlinear control (MPC recursive feasibility, backstepping, POMDPs) coupled with systematic formalization of mathematical prize bounties (Justin Sun Prize, conjectures.io, Erdős problems).

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                 Phase 1: Near-Term Additions (Delivered)                    │
│  • Planar Homography & Collineation Duality                                 │
│  • Controllability Gramian & Minimum-Energy Steering                        │
│  • Woodbury Identity & Information Filter Equivalence                       │
│  • Second-Order Pole Placement & Deadbeat Control                           │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
┌──────────────────────────────────────┴──────────────────────────────────────┐
│                 Phase 2: Medium-Term Additions (In Progress)                │
│  • Luenberger State Observer & Separation Principle                         │
│  • Discrete-Time Algebraic Riccati Equation (DARE)                          │
│  • Continuous-Time Kalman–Bucy Differential Riccati Filter                  │
│  • Multi-View Essential Matrix SVD & 8-Point Algorithm                      │
│  • Discrete-Time Polynomial Jury Stability Criterion                        │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
┌──────────────────────────────────────┴──────────────────────────────────────┐
│                 Phase 3: Long-Term Horizons & Research Bounties             │
│  • Model Predictive Control (MPC) Recursive Feasibility                     │
│  • Nonlinear Integrator Backstepping & Control Lyapunov Functions           │
│  • Input-to-State Stability (ISS) via Comparison Functions                  │
│  • Partially Observable Markov Decision Processes (POMDPs)                  │
│  • Justin Sun Prize & Solved Erdős Formalizations (via BOUNTIES.md)         │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Near-Term Milestones: Delivered Additions

Four major additions have been formalized, integrated into `ControlsLean`, machine-checked with `scripts/check.sh`, audited for standard axioms in `scripts/Audit.lean`, and documented with research proposals in `docs/proposals/`:

### Milestone M3: Planar Homography & Collineation Duality (Machine Vision)
- **Module**: `ControlsLean/Vision/Homography.lean`
- **Proposal**: `docs/proposals/01_planar_homography.md`
- **Domain**: Projective Geometry & Computer Vision
- **Mathematical Significance**: In multi-view geometry, when scene points are coplanar, two-view epipolar geometry degenerates ($\det(E) = 0$ is no longer uniquely determined). Instead, the perspective projection induces an invertible planar homography $H \in \mathrm{GL}(3, K)$.
- **Key Headline Theorems**:
  - `det_homography_three_points`: For any 3 projective points $p, q, r \in K^3$, $\det [H p, H q, H r] = \det(H) \det [p, q, r]$.
  - `collinear_homography`: When $\det(H) \ne 0$, three points are collinear if and only if their homography images are collinear.
  - `lineTransform_dotProduct`: Under dual line transformation $l' = H^{-\top} l$, point-line incidence is invariant: $(H^{-\top} l)^\top (H p) = l^\top p$.
  - `plane_homography_constraint`: A physical 3D plane $n^\top X = d$ induces $H = R + \frac{1}{d} t n^\top$ such that $d_2 x_2 = H (d_1 x_1)$ for camera depths $d_1, d_2$.
- **Literature**: Hartley & Zisserman (2004), *Multiple View Geometry in Computer Vision*, Chapters 2 & 13.

### Milestone M4: Controllability Gramian & Minimum-Energy Steering (Controls)
- **Module**: `ControlsLean/Controls/Gramian.lean`
- **Proposal**: `docs/proposals/02_controllability_gramian.md`
- **Domain**: Optimal Control & Controllability
- **Mathematical Significance**: Qualitative reachability (whether a state can be reached) provides no measure of control effort. The Controllability Gramian $W_k = \sum_{i=0}^{k-1} A^i B B^\top (A^i)^\top$ quantifies control energy $\sum \|u_i\|^2$ and yields the optimal open-loop steering trajectory.
- **Key Headline Theorems**:
  - `gramian_transpose`: The Gramian is unconditionally symmetric ($W_k^\top = W_k$).
  - `quad_gramian_term`: Each summand satisfies $x^\top (A^i B B^\top (A^i)^\top) x = \| B^\top (A^i)^\top x \|^2 \ge 0$.
  - `gramian_steer`: If $W_k$ has right inverse $W_{\text{inv}}$, then applying the feedback control $u_i = B^\top (A^\top)^{k-1-i} W_{\text{inv}} x_1$ drives the system from $x_0 = 0$ to exactly $x_1$ in $k$ steps. Proven by index reversal using `Fin.revPerm` and `Equiv.sum_comp`.
- **Literature**: Kalman, Ho, & Narendra (1963); Hespanha (2018), *Linear Systems Theory*, Chapter 10.

### Milestone M5: Sherman–Morrison–Woodbury & Information Filter Equivalence (Estimation)
- **Module**: `ControlsLean/Estimation/InformationFilter.lean`
- **Proposal**: `docs/proposals/03_information_filter.md`
- **Domain**: State Estimation & Filtering
- **Mathematical Significance**: In Kalman filtering, the covariance update $P^+ = P - P C^\top (R + C P C^\top)^{-1} C P$ requires inverting an $m \times m$ matrix (measurement dimension). The Information filter updates the precision matrix $Y^+ = Y + C^\top R^{-1} C$, requiring only an $n \times n$ addition. Proving their mathematical equivalence requires the Sherman–Morrison–Woodbury matrix inversion lemma.
- **Key Headline Theorems**:
  - `woodbury_right_inv` & `woodbury_left_inv`: Verified for any associative ring $\alpha$ without coordinate indexing clutter:
    $$(A + U C V) (A^{-1} - A^{-1} U (C^{-1} + V A^{-1} U)^{-1} V A^{-1}) = 1.$$
  - `kalman_postVar_information_equiv`: Direct proof that $(P^{-1} + C^\top R^{-1} C)$ is the two-sided inverse of the Kalman posterior covariance $P^+$.
- **Literature**: Woodbury (1950); Anderson & Moore (1979), *Optimal Filtering*, Chapter 5; Kailath et al. (2000), *Linear Estimation*.

### Milestone M6: Second-Order Pole Placement & Deadbeat Control (Controls)
- **Module**: `ControlsLean/Controls/PolePlacement.lean`
- **Proposal**: `docs/proposals/04_pole_placement_deadbeat.md`
- **Domain**: Active Feedback Synthesis & Digital Control
- **Mathematical Significance**: Connects open-loop stability analysis to active controller design. In discrete-time systems, placing all closed-loop eigenvalues at the origin creates a nilpotent matrix $A_{cl}^n = 0$, driving every initial state to exact zero in $n$ steps (deadbeat response).
- **Key Headline Theorems**:
  - `closedLoop_eq`: Explicit companion form for closed loop $A - B K$.
  - `deadbeat_nilpotent`: Selecting gains $k_0 = -a_0, k_1 = -a_1$ yields $A_{cl}^2 = 0$.
  - `deadbeat_trajectory_zero`: For any initial condition $x_0 \in K^2$, $A_{cl}^2 x_0 = 0$.
  - `pole_placement_hurwitz`: Gains satisfying $a_0 + k_0 > 0$ and $a_1 + k_1 > 0$ guarantee continuous-time Hurwitz stability via `isHurwitz2_iff`.
- **Literature**: Ackermann (1972); Åström & Murray (2021), *Feedback Systems*, Chapter 8; Franklin, Powell, & Workman (1998), *Digital Control of Dynamic Systems*.

---

## 3. Medium-Term Roadmap: Core Engineering Foundations

The next phase of `ctrl` targets the central pillars of modern linear systems and estimation:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Medium-Term Milestones                            │
├─────────────────────────────────────────────────────────────────────────────┤
│ 1. Luenberger Observer & The Separation Principle                           │
│ 2. Discrete-Time Algebraic Riccati Equation (DARE)                          │
│ 3. Continuous-Time Kalman–Bucy Filter (Differential Riccati) — delivered ★ │
│ 4. Multi-View Geometry: 8-Point Algorithm & Essential Matrix SVD            │
│ 5. Discrete-Time Polynomial Jury Stability Criterion                        │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.1 Luenberger Observers & The Separation Principle
- **Objective**: Formalize full-order state observers $\hat{x}_{k+1} = A \hat{x}_k + B u_k + L(y_k - C \hat{x}_k)$ and prove the Separation Principle.
- **Mathematical Content**:
  1. Define estimation error $e_k = x_k - \hat{x}_k$.
  2. Prove error decoupling from control inputs: $e_{k+1} = (A - L C) e_k$ for any control sequence $u_k$.
  3. Under certainty-equivalence state feedback $u_k = -K \hat{x}_k$, the augmented state $\begin{bmatrix} x_k \\ e_k \end{bmatrix}$ obeys block upper-triangular dynamics:
     $$\begin{bmatrix} x_{k+1} \\ e_{k+1} \end{bmatrix} = \begin{bmatrix} A - B K & B K \\ 0 & A - L C \end{bmatrix} \begin{bmatrix} x_k \\ e_k \end{bmatrix}.$$
  4. Prove that the closed-loop characteristic polynomial factors:
     $$\det\left(s I - \begin{bmatrix} A - B K & B K \\ 0 & A - L C \end{bmatrix}\right) = \det(s I - (A - B K)) \cdot \det(s I - (A - L C)).$$
  5. Conclude that controller and observer gains $K$ and $L$ can be designed completely independently.
- **Target File**: `ControlsLean/Controls/ObserverSeparation.lean`
- **Primary Reference**: Luenberger (1971), *An Introduction to Observers*; Hespanha (2018), Chapter 14.

### 3.2 Discrete-Time Algebraic Riccati Equation (DARE)
- **Objective**: Formalize the steady-state solution of discrete-time linear quadratic optimal control (LQR) and Kalman filtering.
- **Mathematical Content**:
  - The matrix DARE operator:
    $$\mathcal{T}(P) = A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A + Q.$$
  - Prove that for controllable and observable pairs $(A, B)$ and $(A, Q^{1/2})$, $\mathcal{T}$ is a monotonic and contractive operator on the cone of positive semidefinite matrices.
  - Prove existence and uniqueness of the stabilizing solution $P_\infty \succ 0$ such that $A - B K$ is Schur stable, where $K = (R + B^\top P_\infty B)^{-1} B^\top P_\infty A$.
- **Target File**: `ControlsLean/Controls/DARE.lean`
- **Primary Reference**: Anderson & Moore (1979); Lancaster & Rodman (1995), *Algebraic Riccati Equations*.

### 3.3 Continuous-Time Kalman–Bucy Filter & Differential Riccati Equations ★ Delivered (algebraic core)
- **Module**: `ControlsLean/Estimation/KalmanBucy.lean`
- **Proposal**: `docs/proposals/11_kalman_bucy_dre.md`
- **Delivered**:
  - Continuous Bucy–Joseph filter generator
    $\mathcal{L}(K) = (A - K C) P + P (A - K C)^\top + Q + K R K^\top$.
  - Inverse-free optimal gain equation $K^* R = P C^\top$ and DRE reduction
    `filterGen_opt_eq_dre`: $\mathcal{L}(K^*) = A P + P A^\top - K^* R (K^*)^\top + Q$.
  - Matrix completion of squares `filterGen_completion_of_squares` and Loewner / instantaneous-trace
    optimality of the Kalman–Bucy gain (`quad_filterGen_le`, `trace_filterGen_le`).
  - CARE steady-state Lyapunov identity `care_lyapunov_identity`.
- **Deferred**: Existence/uniqueness of DRE trajectories, geometric convergence to the CARE
  fixed point, and continuous-time observer asymptotic stability via a continuous Lyapunov theorem.
- **Primary Reference**: Kalman & Bucy (1961), *New Results in Linear Filtering and Prediction Theory*.

### 3.4 Multi-View Geometry: Eight-Point Algorithm & Essential Matrix SVD
- **Objective**: Extend `Vision/Epipolar.lean` to camera motion estimation from point correspondences.
- **Mathematical Content**:
  - Formulate Longuet-Higgins' (1981) linear system: each point correspondence $(x_1, x_2)$ defines a linear constraint $(x_2 \otimes x_1)^\top \operatorname{vec}(E) = 0$.
  - Prove that 8 point correspondences in general position determine $E$ up to scale.
  - Formalize the Faugeras–Maybank algebraic characterization: a $3 \times 3$ real matrix $E$ is an essential matrix iff:
    $$2 E E^\top E - \operatorname{tr}(E E^\top) E = 0 \quad \text{and} \quad \det(E) = 0.$$
  - Factorization of $E$ into four rigid pose solutions $(R, t)$ with chirality verification ($Z > 0$).
- **Target File**: `ControlsLean/Vision/EightPoint.lean`
- **Primary Reference**: Longuet-Higgins (1981); Faugeras & Luong (2001), Chapter 5.

### 3.5 Discrete-Time Polynomial Jury Stability Criterion
- **Objective**: Formalize the discrete-time counterpart to `Hurwitz2.lean`.
- **Mathematical Content**:
  - Root characterization for quadratic polynomials $z^2 + a z + b = 0$.
  - Prove the exact `iff` condition for roots lying strictly inside the open unit disk $\{z \in \mathbb{C} \mid |z| < 1\}$:
    $$|b| < 1 \quad \text{and} \quad |a| < 1 + b.$$
  - Extend to degree 3 and provide recurrence tables for degree $n$.
- **Target File**: `ControlsLean/Controls/Jury2.lean`
- **Primary Reference**: Jury, E. I. (1964), *Theory and Application of the z-Transform Method*.

---

## 4. Long-Term Horizons & Research Frontiers

Beyond linear systems and classical vision lies the frontier of modern safety-critical robotics:

### 4.1 Model Predictive Control (MPC) Recursive Feasibility & Stability
- Formalize receding-horizon constrained optimization:
  $$\min_{\{u_k\}} \sum_{k=0}^{N-1} (x_k^\top Q x_k + u_k^\top R u_k) + x_N^\top P x_N \quad \text{s.t.} \quad x_k \in \mathcal{X}, u_k \in \mathcal{U}, x_N \in \mathcal{X}_f.$$
- Prove **recursive feasibility**: if an initial feasible trajectory exists, the receding-horizon optimization remains feasible for all future time steps under a control invariant terminal set $\mathcal{X}_f$.
- Prove asymptotic stability using the optimal value function $V_N^*(x)$ as a Lyapunov function.
- **Reference**: Rawlings, Mayne, & Diehl (2017), *Model Predictive Control: Theory, Computation, and Design*.

### 4.2 Nonlinear Integrator Backstepping & Control Lyapunov Functions (CLFs)
- Formalize constructive nonlinear feedback for strict-feedback systems:
  $$\dot{x}_1 = f_1(x_1) + g_1(x_1) x_2, \qquad \dot{x}_2 = f_2(x_1, x_2) + g_2(x_1, x_2) u.$$
- Iteratively construct control Lyapunov functions $V(x) = \frac{1}{2} x_1^2 + \frac{1}{2}(x_2 - \alpha_1(x_1))^2$ with virtual control $\alpha_1(x_1)$ to synthesize globally asymptotically stabilizing control laws.
- **Reference**: Krstić, Kanellakopoulos, & Kokotović (1995), *Nonlinear and Adaptive Control Design*.

### 4.3 Input-to-State Stability (ISS)
- Bridge `LeanForControl`'s comparison function library (Classes $\mathcal{K}$, $\mathcal{KL}$) with external disturbance bounds:
  $$\|x(t)\| \le \beta(\|x_0\|, t) + \gamma\left(\sup_{0 \le \tau \le t} \|w(\tau)\|\right).$$
- Prove Sontag's characterization: existence of an ISS Lyapunov function is equivalent to the ISS trajectory bound.
- **Reference**: Sontag, E. D. (1989), *Smooth stabilization implies coprime factorization*.

### 4.4 Partially Observable Markov Decision Processes (POMDPs)
- Formalize stochastic belief state update:
  $$b_{k+1}(s') \propto \sum_s P(s' \mid s, a_k) O(y_{k+1} \mid s') b_k(s).$$
- Prove that the optimal value function $V^*(b)$ is piecewise linear and convex (PWLC) in the belief simplex.
- **Reference**: Kaelbling, Littman, & Cassandra (1998), *Planning and acting in partially observable stochastic domains*.

---

## 5. Formal Mathematics Bounty & Prize Triage

The formalized mathematics ecosystem has entered an era of funded prize competitions. As documented in `BOUNTIES.md`, formalizing mathematical solutions can secure research bounties and grants:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            Major Bounty Programs                            │
├─────────────────────────────────────────────────────────────────────────────┤
│ 1. Justin Sun Prize (JSP): 30% formalizer share for verified Lean solves     │
│ 2. conjectures.io: Bounties for open conjectures (DeepMind Formal Conjectures)│
│ 3. Renaissance / XTX AI for Math Fund: $100k–$1M tool and dataset grants   │
│ 4. Palomar Registry (Lean FRO + ICARM): Citable machine-checked records     │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 5.1 The Justin Sun Prize (JSP) Opportunity
- **Rules**: The Justin Sun Prize awards verified Lean 4 solutions to mathematical problems, paying the formalizer separately from the mathematician (legacy 70% solver / 30% formalizer split).
- **Key Advantage**: A formalizer can claim a problem that has already been mathematically solved in the published literature, provided they produce a complete, machine-checked Lean 4 proof.
- **Strict Verification Rules**:
  - Only Lean 4 proofs qualify.
  - Zero `sorry`, zero `admit`, strictly standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
  - Stating literature lemmas as custom `axiom` declarations results in immediate rejection.
  - **Priority Rule**: Priority is established by the earliest public commit SHA in a public GitHub repository.

### 5.2 DeepMind Formal Conjectures & Erdős Problem Pipeline
The DeepMind `formal-conjectures` repository contains 1,137 formal Erdős problem statements. Crucially:
- **680 problems are tagged `research solved`**, meaning the mathematical proof is published, but the Lean 4 formalization remains `sorry`.
- These 680 solved-but-unformalized problems represent our prime targets for formalization bounties.

#### Automated Triage via `scripts/bounty_triage.sh`
To systematically select high-yield targets, the repository includes `scripts/bounty_triage.sh`, which:
1. Synchronizes with `google-deepmind/formal-conjectures`.
2. Filters for problems marked `research solved` whose proof is still `sorry`.
3. Sorts candidate problems by statement length (shorter statements frequently correlate with elementary linear algebraic, geometric, or combinatorial proofs).

#### Target Qualification Workflow
```
[Triage Output] ──> [Literature Check] ──> [JSP Bank Check] ──> [Formalize] ──> [Public Commit SHA]
(bounty_triage.sh)   (ErdosProblems.com)    (JSP PR Backlog)    (ControlsLean)    (Claim Priority)
```
1. Run `bash scripts/bounty_triage.sh` to identify top 5 candidate problems.
2. Confirm the published mathematical proof on `erdosproblems.com` and verify the problem is listed in the JSP problem bank (`problems/`).
3. Search the JSP PR backlog to confirm no competing formalization has been submitted.
4. Formalize the problem in `ControlsLean/Bounty/ErdosNNN.lean` matching the upstream statement verbatim.
5. Verify with `scripts/check.sh` and push immediately to `origin/main` to pin the 40-character commit SHA for legal priority.
6. Submit to the Justin Sun Prize and the Palomar registry.
