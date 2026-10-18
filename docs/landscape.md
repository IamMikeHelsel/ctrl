# Comparative Landscape of Formal Control Theory, Estimation, and Computer Vision in Lean 4

**Author**: `ctrl` Documentation & Architecture Team  
**Date**: October 2026  
**Repository**: `https://github.com/IamMikeHelsel/ctrl`  
**Toolchain**: Lean 4 `v4.36.0-rc1` (with Mathlib rev `625d8914`)  
**Reference Codebases**:
- `ControlsLean` (Seed repository at `/Users/mike/lean-work/ControlsLean`)
- `LeanForControl` (Reference repository at `/Users/mike/Dev/LeanForControl`)
- `Mathlib4` (Lean Community Mathematical Library)

---

## 1. Executive Summary

Interactive theorem proving (ITP) has achieved extraordinary milestones in pure mathematics—from the formalization of Fermat's Last Theorem foundations and the Liquid Tensor Experiment to the classification of finite simple groups. However, cyber-physical systems, control engineering, robotic perception, and state estimation have historically remained almost completely untouched by formal verification in Lean 4.

Engineering systems operate under physical safety constraints, rigorous stability requirements, and real-time computation bounds. When flight controllers, autonomous vehicle perception pipelines, or surgical robotics fail due to subtle mathematical oversights or unhandled edge cases, the consequences are catastrophic. Machine-checking the underlying theory—from stability proofs and Kalman filter optimality to multi-view epipolar geometry—provides absolute mathematical certainty that these foundational models are free from hidden defects.

This document presents a comprehensive comparative survey across the three key codebases shaping formal control theory in Lean 4:
1. **`Mathlib`**: Upstream foundation containing general algebra, topology, and local differential equations, but containing zero domain-specific control theory, estimation, or vision.
2. **`LeanForControl`**: A large-scale (67 modules) academic library focusing on continuous/discrete LTI/LTV linear systems (based on Hespanha's *Linear Systems Theory*) and nonlinear ODE stability (based on Khalil's *Nonlinear Systems*).
3. **`ctrl` / `ControlsLean`**: A pragmatic, highly modular library that unifies the cyber-physical triad: **Controls & Stability**, **Estimation & Filtering**, and **Machine Vision & Projective Geometry**.

---

## 2. The Three Ecosystem Pillars

```
                     ┌─────────────────────────────────────────────────────────┐
                     │                         Mathlib                         │
                     │  (General Linear Algebra, Normed Spaces, Local ODEs)    │
                     └────────────────────────────┬────────────────────────────┘
                                                  │
                        ┌─────────────────────────┴────────────────────────┐
                        ▼                                                  ▼
      ┌───────────────────────────────────┐              ┌───────────────────────────────────┐
      │          LeanForControl           │              │               ctrl                │
      │       (Hespanha & Khalil)         │              │  (Controls, Estimation, Vision)   │
      ├───────────────────────────────────┤              ├───────────────────────────────────┤
      │ • 67 source modules               │              │ • Consolidated modular library    │
      │ • Lean v4.30.0-rc2                │              │ • Lean v4.36.0-rc1                │
      │ • Peano–Baker state transitions   │              │ • Coordinate-free reachability    │
      │ • PBH Hautus controllability      │              │ • Controllability Gramian & steer │
      │ • Continuous/discrete Lyapunov eq │              │ • Asymmetric Lyapunov stability   │
      │ • LaSalle, Chetaev, Linearization │              │ • Second-order Hurwitz & Deadbeat │
      │ • Comparison functions (K, KL)    │              │ • Scalar & Information Kalman     │
      │ ✗ 0 Estimation / Filtering        │              │ • Sherman–Morrison–Woodbury       │
      │ ✗ 0 Computer Vision / Projective  │              │ • Epipolar & Planar Homography    │
      └───────────────────────────────────┘              └───────────────────────────────────┘
```

### 2.1 Upstream Foundation: Mathlib

Mathlib is the central mathematical repository of the Lean community. It provides world-class abstractions for pure mathematics:
- **Linear Algebra**: `Matrix m n α`, `LinearMap R M M₂`, `Submodule R M`, determinants (`Matrix.det`), cross products on `Fin 3` (`Mathlib.LinearAlgebra.CrossProduct`), and bilinear forms.
- **Definiteness & Quadratic Forms**: `Matrix.PosDef` and `Matrix.PosSemidef` are formalized in `Mathlib.LinearAlgebra.Matrix.PosDef`. However, Mathlib's definitions strictly impose `M.IsHermitian` (or matrix symmetry in the real case).
- **Spectral Theory**: Characteristic polynomials (`Matrix.charpoly`), eigenvalues (`Matrix.hasEigenvalue`), the Cayley–Hamilton theorem (`Matrix.aeval_self_charpoly`), and Banach algebra spectral radius via Gelfand's formula. Mathlib lacks general Jordan canonical forms (only Jordan–Chevalley $f = s + n$) and Schur triangularization ($A = U T U^*$).
- **Analysis & Ordinary Differential Equations**: Mathlib provides local Picard–Lindelöf existence on compact intervals (`Mathlib.Analysis.ODE.PicardLindelof`) under restrictive Lipschitz step constraints ($L \cdot \Delta t \le a - r$). It does not include global ODE continuation, comparison lemmas, or dynamical systems beyond topological flows.

### 2.2 Academic Deep Foundation: `LeanForControl`

Developed by Anand Gokhale et al., `LeanForControl` is a 67-file formalization structured around standard graduate textbooks: João P. Hespanha's *Linear Systems Theory* (2009/2018) and Hassan K. Khalil's *Nonlinear Systems* (2002).

**Key Architectural Assets**:
- **State Transition Matrix**: Proves convergence of the continuous Peano–Baker series $\Phi(t, t_0) = I + \int_{t_0}^t A(\sigma_1)\,d\sigma_1 + \dots$ and proves variation of constants $x(t) = \Phi(t, t_0) x_0 + \int_{t_0}^t \Phi(t, \tau) B(\tau) u(\tau)\,d\tau$.
- **Controllability & Observability**: Defines concrete matrices $\mathcal{C}(A, B) \in \mathbb{K}^{n \times nm}$ and $\mathcal{O}(A, C) \in \mathbb{K}^{pn \times n}$, proving the Popov–Belevitch–Hautus (PBH / Hautus) rank tests and exact duality.
- **Kalman 4-Sector Decomposition**: Formalizes the canonical decomposition over $\mathbb{C}$ into controllable/uncontrollable and observable/unobservable coordinates.
- **Axiom-Free Lyapunov Equations**: Proves existence and uniqueness of solutions to $P A + A^\top P = -Q$ (for Hurwitz $A$) and $A^\top P A - P = -Q$ (for Schur $A$).
- **Nonlinear Stability Theory**: Comprehensive comparison function library (Classes $\mathcal{K}, \mathcal{K}_\infty, \mathcal{KL}, \mathcal{L}$), glued global Picard–Lindelöf continuation, LaSalle's invariance principle, Barbashin–Krasovskii theorems, and both branches of Lyapunov's indirect method (linearization).

**Limitations of `LeanForControl`**:
- **Complete Absence of Estimation & Filtering**: Exactly zero files on Kalman filtering, state estimation, covariance propagation, or Riccati equations.
- **Complete Absence of Computer Vision**: Exactly zero files on multi-view geometry, cameras, epipolar constraints, or homographies.
- **No Controller Synthesis**: Focuses exclusively on stability analysis; lacks pole placement, Ackermann formulas, deadbeat control, and LQR/LQG synthesis.
- **Stale Toolchain**: Pinned to `v4.30.0-rc2`, preventing direct interoperability with modern Mathlib without significant porting effort.

### 2.3 The `ctrl` Repository

The `ctrl` library (originating from `ControlsLean`) is designed to be the unified, lightweight, and modern Lean 4 library for cyber-physical systems. Rather than attempting to formalize an entire textbook linearly, `ctrl` focuses on high-leverage foundational results across the three core disciplines:
1. **Vision**: Projective geometry, calibrated epipolar geometry, essential matrices, planar homographies, and line-point collineation duality.
2. **Estimation**: Optimal Bayesian filtering, scalar and multivariate Kalman filtering, covariance vs. information filter equivalence via the Sherman–Morrison–Woodbury theorem, and Riccati contractive dynamics.
3. **Controls**: Coordinate-free reachability without Cayley–Hamilton, controllability Gramians and minimum-energy steering, deadbeat control, and discrete Lyapunov stability without matrix symmetry.

---

## 3. Side-by-Side Capability Matrix

The following matrix compares formalization coverage across all three libraries:

| Mathematical Capability / Theorem | `Mathlib` | `LeanForControl` | `ctrl` (Our Library) | Notes & Formal Differences |
|---|:---:|:---:|:---:|---|
| **Lean Toolchain** | Continuous | `v4.30.0-rc2` | `v4.36.0-rc1` | `ctrl` tracks modern stable Lean 4 |
| **Axiom Footprint** | Standard | Standard | Standard | Exclusively `[propext, Classical.choice, Quot.sound]` |
| **Two-View Epipolar Geometry** | ❌ None | ❌ None | **Full** | Calibrated $x_2^\top E x_1 = 0$, $E = [t]_\times R$, $\det(E) = 0$, $t^\top E = 0$ |
| **Planar Homography & Collineation** | ❌ None | ❌ None | **Full** | Line duality $l' = H^{-\top} l$, collinearity preservation, plane-induced motion |
| **Cross Product Matrix (`skew`)** | ❌ None | ❌ None | **Full** | $[t]_\times v = t \times_3 v$, $[t]_\times^\top = -[t]_\times$, $\det([t]_\times) = 0$ |
| **Scalar Kalman Filter Optimality** | ❌ None | ❌ None | **Full** | Optimal gain $K = P / (P + R)$, uniqueness via completing the square |
| **Information Filter Precision Additivity** | ❌ None | ❌ None | **Full** | Scalar $(P^+)^{-1} = P^{-1} + R^{-1}$ |
| **Sherman–Morrison–Woodbury Identity** | ❌ None | ❌ None | **Full** | Ring-general $(A + UCV)^{-1} = A^{-1} - A^{-1}U(C^{-1} + VA^{-1}U)^{-1}VA^{-1}$ |
| **Multivariate Information Equivalence** | ❌ None | ❌ None | **Full** | $(P^+)^{-1} = P^{-1} + C^\top R^{-1} C$ via Woodbury identity |
| **Riccati Equation Fixed Point & Contraction**| ❌ None | ❌ None | **Full** | Unique positive fixed point on $(0, \infty)$, strict Lipschitz contraction factor |
| **Reachability Subspace Definition** | ❌ None | Matrix powers | **Coordinate-Free**| Recursive submodule chain $R_{k+1} = \mathrm{range}(B) \sqcup A(R_k)$ |
| **Reachability Chain Stabilization** | ❌ None | Cayley–Hamilton | **Dimension Counting**| Stabilization at $k = \dim V$ purely via finite dimension monotonicity |
| **Feedback Invariance of Reachability** | ❌ None | ❌ None | **Full** | $\mathrm{reach}(A + B F, B, k) = \mathrm{reach}(A, B, k)$ for any linear feedback $F$ |
| **Controllability State Steering Theorem**| ❌ None | Rank property | **Constructive**| Steers between arbitrary $x_0, x_f$ in exactly $\dim V$ steps |
| **Controllability Gramian ($W_k$)** | ❌ None | ❌ None | **Full** | $W_k = \sum A^i B B^\top (A^i)^\top$, symmetry $W_k^\top = W_k$, quadratic form |
| **Minimum-Energy Control Formula** | ❌ None | ❌ None | **Full** | $u_i = B^\top (A^\top)^{k-1-i} W_k^{-1} x_1$ proven via index reversal |
| **State-Feedback Pole Placement** | ❌ None | ❌ None | **Full** | 2D canonical companion form Ackermann placement |
| **Deadbeat Control & Nilpotence** | ❌ None | ❌ None | **Full** | $A_{cl}^2 = 0$ and 2-step exact trajectory extinction $A_{cl}^2 x_0 = 0$ |
| **Hurwitz Stability (Degree 2)** | ❌ None | ❌ None | **Full** | Exact iff criterion: $s^2 + as + b$ Hurwitz $\iff a > 0 \land b > 0$ |
| **Hurwitz Stability (Matrix Spectrum)** | ❌ None | **Full** | ❌ None | $\mathrm{Re}(\lambda) < 0$, spectral shift, exponential envelopes |
| **Discrete Lyapunov Stability** | ❌ None | Lyapunov Series | **Unit Sphere** | Geometric decay $A^k x_0 \to 0$ without matrix symmetry |
| **Continuous Lyapunov Equation** | ❌ None | **Full** | ❌ None | Unique $P \succ 0$ solving $PA + A^\top P = -Q$ for Hurwitz $A$ |
| **Discrete Lyapunov Equation** | ❌ None | **Full** | Partial | Converse Stein series in `ConverseLyapunov`; DARE/LQR Bellman identity in `DARE` |
| **Discrete Algebraic Riccati (DARE / LQR)** | ❌ None | ❌ None | **Full (algebraic)** | Inverse-free completion of squares `M(K)=𝒯(P)−P+(K−K*)ᵀS(K−K*)`; closed-loop stability |
| **PBH (Hautus) Rank Tests** | ❌ None | **Full** | ❌ None | Rank tests for controllability and observability over $\mathbb{C}$ |
| **Kalman 4-Sector Canonical Decomposition**| ❌ None | **Full** | ❌ None | Coordinate transformation isolating $x_{co}, x_{cuo}, x_{uo}, x_{uuo}$ |
| **Continuous Peano–Baker Series** | ❌ None | **Full** | ❌ None | State transition matrix $\Phi(t, t_0)$ solving $\dot{\Phi} = A(t)\Phi$ |
| **Nonlinear ODE Global Continuation** | Local only | **Full** | ❌ None | Glued Picard–Lindelöf for globally Lipschitz vector fields |
| **LaSalle Invariance Principle** | ❌ None | **Full** | ❌ None | Forward invariance of $\omega$-limit sets and convergence to largest invariant set |
| **Chetaev Instability & Linearization** | ❌ None | **Full** | ❌ None | Both branches of Lyapunov's indirect method (stable and unstable) |

---

## 4. Architectural and Stylistic Comparison

### 4.1 Representation of State and Vector Spaces

A fundamental design decision in formal linear algebra is the choice of representation:

1. **Coordinate-Free Vector Spaces (`V →ₗ[K] V`, `Submodule K V`)**:
   - *Used in*: `ctrl` (`ControlsLean/Controls/Reachability.lean`).
   - *Advantages*: Clean, dimension-independent, free of indexing arithmetic, applies to infinite-dimensional spaces where applicable.
   - *Disadvantages*: Does not readily expose entry-wise matrix algorithms (e.g. numerical matrix inversion, singular values).
2. **Concrete Matrix Types (`Matrix (Fin n) (Fin m) K`)**:
   - *Used in*: `ctrl` (`Epipolar.lean`, `Homography.lean`, `PolePlacement.lean`), `LeanForControl` (`Controllability.lean`).
   - *Advantages*: Exact alignment with textbook engineering equations; enables explicit computation tactics (`fin_cases`, `simp`, `ring`).
   - *Disadvantages*: Dependent type friction when working with dimensions like $n + m$ or concatenating block rows/columns.
3. **Generic Fintypes (`Matrix X X K` with `[Fintype X]`)**:
   - *Used in*: `ctrl` (`Gramian.lean`, `DiscreteLyapunov.lean`), `LeanForControl` (`Stability/`).
   - *Advantages*: Eliminates natural number arithmetic; transposes, powers, and traces are completely symmetric.
   - *Disadvantages*: Less natural for rectangular systems ($n \times m$ where $n \ne m$).

**Synthesis**: The `ctrl` codebase adopts a **hybrid multi-tier representation**: coordinate-free linear maps for structural theorems (subspace stabilization, feedback invariance), generic fintypes for quadratic forms and energy Gramians, and concrete `Fin n` coordinates for geometric/estimation algorithms.

### 4.2 Proof Strategies: Cayley–Hamilton vs. Finite Dimension Counting

A prime case study in proof architecture is the stabilization of the reachable subspace:
$$\mathcal{R}_k = \sum_{i=0}^{k-1} A^i \mathrm{range}(B).$$

- **The `LeanForControl` Strategy (Cayley–Hamilton)**:
  `LeanForControl` proves that $\mathcal{R}_k$ stops growing at $k = n$ by showing that $A^n$ is a linear combination of $\{I, A, \dots, A^{n-1}\}$ via the Cayley–Hamilton theorem (`pow_card_eq_neg_sum_charpoly_coeff A`). This requires pulling in Mathlib's characteristic polynomial machinery, commutativity assumptions, and polynomial ring algebras.
- **The `ctrl` Strategy (Dimension Counting)**:
  `ctrl` defines reachability as an ascending chain of submodules:
  $$R_0 = \bot, \qquad R_{k+1} = \mathrm{range}(B) \sqcup A(R_k).$$
  Because $R_k \le R_{k+1}$, if $R_k \ne R_{k+1}$, their dimensions in `K` must strictly increase: $\dim(R_{k+1}) \ge \dim(R_k) + 1$. In a vector space of finite dimension $n = \mathrm{finrank}(K, V)$, this strict increase can happen at most $n$ times. Therefore, $R_n = R_{n+1}$, which by immediate induction implies $R_k = R_n$ for all $k \ge n$.
- **Architectural Takeaway**: The dimension counting approach works over **any arbitrary field $K$**, requires zero characteristic polynomial machinery, is entirely coordinate-free, and yields the state-feedback invariance $\mathrm{reach}(A + BF, B) = \mathrm{reach}(A, B)$ directly.

### 4.3 Matrix Symmetry in Lyapunov Stability

In classical textbook linear systems, Lyapunov stability is often presented using symmetric positive definite matrices: $V(x) = x^\top P x$ with $P = P^\top \succ 0$.
Mathlib reflects this in `Matrix.PosDef`, which explicitly defines:
```lean
def PosDef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M *ᵥ x)
```
However, in physical systems, numerical algorithms, and multi-agent coordination, asymmetric matrices often arise whose quadratic forms are strictly positive: $x^\top P x > 0$ for all $x \ne 0$, even though $P \ne P^\top$.

In `ctrl` (`ControlsLean/Controls/DiscreteLyapunov.lean`), we discard the artificial symmetry constraint:
- Define `quad M x := x ⬝ᵥ (M *ᵥ x)`.
- Use the topological compactness of the Euclidean unit sphere (`Metric.isCompact_sphere`) and the Extreme Value Theorem (`ContinuousOn.exists_isMinOn`) to establish sharp uniform quadratic bounds:
  $$c \|x\|^2 \le x^\top P x \le C \|x\|^2, \qquad c > 0, C > 0.$$
- Prove contraction $V(A x) \le \rho V(x)$ with $\rho = \max(1 - c/C, 0) < 1$, guaranteeing asymptotic stability $A^k x_0 \to 0$ for **any** matrix $P$ satisfying the Lyapunov inequality, symmetric or asymmetric.
- Provide a zero-overhead compatibility bridge `PosDef.tendsto_pow_mulVec_zero` for users working with Mathlib's symmetric `Matrix.PosDef`.

---

## 5. Formalization Voids in the Lean 4 Ecosystem

Our comparative survey reveals five major formalization voids across the Lean 4 ecosystem that `ctrl` is systematically addressing:

### Void 1: Estimation, Filtering, and Stochastic Control
Neither Mathlib nor `LeanForControl` has formalizations of:
- Multivariate Kalman filter covariance prediction and measurement update.
- The Joseph stabilized covariance update formula:
  $$P^+ = (I - K C) P (I - K C)^\top + K R K^\top \succeq 0.$$
- Gauss–Markov theorem and Best Linear Unbiased Estimator (BLUE).
- Continuous-time Kalman–Bucy filter and Differential Riccati Equations (DRE).
- Discrete-time Algebraic Riccati Equation (DARE) stabilizing solutions.

### Void 2: Projective Geometry and Computer Vision
Computer vision has been completely overlooked by the ITP community:
- Two-view geometry (fundamental matrix, essential matrix SVD characterization).
- Planar homography group $\mathrm{PGL}(3, \mathbb{R})$ and camera calibration.
- The Eight-Point Algorithm (Longuet-Higgins, 1981) and chirality constraints.
- Epipolar line incidence and intersection properties.

### Void 3: Active Feedback Synthesis and Digital Control
`LeanForControl` focuses entirely on passive stability analysis. Void areas include:
- Ackermann's formula for state-feedback pole placement.
- Deadbeat control (finite-time state extinction via nilpotence).
- Luenberger state observers and the Separation Principle.
- Discrete-time polynomial stability criteria (Jury stability tests).

### Void 4: Frequency Domain and Operator Theory
Control engineering relies heavily on frequency-domain methods:
- Resolvent operators $(sI - A)^{-1}$ and transfer function matrices $G(s) = C(sI - A)^{-1}B + D$.
- Bode and Nyquist stability criteria.
- Positive real systems and the Kalman–Yakubovich–Popov (KYP) Lemma.

### Void 5: Modern Constrained and Optimal Control
- Model Predictive Control (MPC) recursive feasibility and stability.
- Control Barrier Functions (CBFs) for forward invariance and safety certificates.
- Linear Quadratic Regulator (LQR) infinite-horizon optimality.

---

## 6. Literature Foundations

The mathematical formulations across `ctrl` are grounded in the following foundational literature:

1. **Ackermann, J.** (1972). *Der Entwurf linearer Regelungssysteme im Zustandsraum*. Regelungstechnik und Prozess-Datenverarbeitung, 20(7): 297–300. (Pole placement formula).
2. **Anderson, B. D. O., & Moore, J. B.** (1979). *Optimal Filtering*. Prentice-Hall. (Information filters and Riccati equations).
3. **Brockett, R. W.** (1970). *Finite Dimensional Linear Systems*. John Wiley & Sons. (Controllability Gramians).
4. **Faugeras, O., & Luong, Q.-T.** (2001). *The Geometry of Multiple Images*. MIT Press. (Projective properties of planes and epipolar geometry).
5. **Franklin, G. F., Powell, J. D., & Workman, M. L.** (1998). *Digital Control of Dynamic Systems* (3rd ed.). Addison-Wesley. (Deadbeat control).
6. **Hartley, R., & Zisserman, A.** (2004). *Multiple View Geometry in Computer Vision* (2nd ed.). Cambridge University Press. (Planar homography, line collineations).
7. **Hespanha, J. P.** (2018). *Linear Systems Theory* (2nd ed.). Princeton University Press. (Controllability Gramians, Lyapunov equations, state observers).
8. **Kailath, T., Sayed, A. H., & Hassibi, B.** (2000). *Linear Estimation*. Prentice Hall. (Information filters, Woodbury identity).
9. **Kalman, R. E.** (1960). *A New Approach to Linear Filtering and Prediction Problems*. Journal of Basic Engineering, 82(1): 35–45. (Kalman filter).
10. **Kalman, R. E., Ho, Y. C., & Narendra, K. S.** (1963). *Controllability of Linear Dynamical Systems*. Contributions to Differential Equations, 1(2): 189–213. (Controllability Gramian steering).
11. **Khalil, H. K.** (2002). *Nonlinear Systems* (3rd ed.). Prentice Hall. (Lyapunov and comparison theory).
12. **Sherman, J., & Morrison, W. J.** (1950). *Adjustment of an Inverse Matrix to Changes in a Specified Column or Row of the Original Matrix*. Annals of Mathematical Statistics, 21(1): 124–127.
13. **Woodbury, M. A.** (1950). *Inverting modified matrices*. Memorandum Report 42, Statistical Research Group, Princeton University.
