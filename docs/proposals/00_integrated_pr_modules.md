# Integrated Open PR & Worktree Modules (Issues #4, #5, #8, #9, #13, #15, #17)

## Overview
This document summarizes the 8 `sorry`-free Lean 4 modules integrated from the sibling worktrees (`ctrl-claude-*`, corresponding to open PRs #11, #12, #14, #16, #18, #19, #20, #21) into `ControlsLean`. Every module compiles cleanly under `lake env lean` with zero `sorry`, `admit`, or custom `axiom` declarations, and all headline theorems depend exclusively on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. `ControlsLean.Controls.Jury2` — Second-Order Jury Stability Test (Issue #5, PR #11)
- **File**: `ControlsLean/Controls/Jury2.lean`
- **Mathematical Content**:
  Formalizes Schur stability (`IsSchur2 a b`) for second-order discrete-time characteristic polynomials $p(z) = z^2 + a z + b$ over $\mathbb{C}$ (all roots satisfy $\|z\| < 1$).
  - `isSchur2_of_jury`: Sufficiency of $|b| < 1$ and $|a| < 1 + b$.
  - `isSchur2_iff`: Complete characterization $\mathrm{IsSchur2}(a, b) \iff |b| < 1 \land |a| < 1 + b$.
  - `isSchur2_iff_jury`: Textbook Jury form $p(1) > 0 \land p(-1) > 0 \land |p(0)| < 1$.
  - `IsSchur2.abs_lt_two`: Necessary bound $|a| < 2$.
  - `isSchur2_deadbeat`: Deadbeat polynomial $z^2$ is Schur stable (`IsSchur2 0 0`).
- **Literature References**:
  - Jury, E. I. (1964). *Theory and Application of the z-Transform Method*. Wiley.
  - Åström, K. J., & Wittenmark, B. (1997). *Computer-Controlled Systems: Theory and Design* (3rd ed.). Prentice Hall, Chapter 3.

---

## 2. `ControlsLean.Vision.EightPoint` — Eight-Point Algorithm Uniqueness (Issue #9, PR #12)
- **File**: `ControlsLean/Vision/EightPoint.lean`
- **Mathematical Content**:
  Formalizes the exact linear-algebraic core of Longuet-Higgins' eight-point algorithm over an arbitrary field $K$.
  - `vec3` and `constraintMatrix`: Row-major vectorization of $3 \times 3$ matrices and the $n \times 9$ Kronecker constraint matrix $M_{i,(a,b)} = x_{2,i}(a)\, x_{1,i}(b)$.
  - `constraintMatrix_mulVec_apply` & `mem_ker_constraintMatrix_iff`: $M \operatorname{vec}(E) = 0 \iff \forall i,\, x_{2,i}^\top E x_{1,i} = 0$.
  - `finrank_ker_constraintMatrix`: Rank–nullity implies $\dim \ker(M) = 1$ when $\operatorname{rank}(M) = 8$.
  - `eq_smul_of_rank_eq_eight`: Any two solutions in the kernel are scalar multiples when $\operatorname{rank}(M) = 8$.
  - `essential_satisfies_constraints` & `eq_smul_essential`: The true essential matrix $E = [t]_\times R$ lies in the kernel for valid two-view correspondences ($d_{2,i} \ne 0$), and every nonzero solution is a nonzero scalar multiple of $[t]_\times R$.
- **Literature References**:
  - Longuet-Higgins, H. C. (1981). A computer algorithm for reconstructing a scene from two projections. *Nature*, 293(5828), 133–135.
  - Hartley, R., & Zisserman, A. (2004). *Multiple View Geometry in Computer Vision* (2nd ed.). Cambridge University Press, Section 11.2.

---

## 3. `ControlsLean.Controls.Observability` — Observability & Kalman Duality (Issue #4, PR #14)
- **File**: `ControlsLean/Controls/Observability.lean`
- **Mathematical Content**:
  Formalizes coordinate-free discrete-time observability for $x_{k+1} = A x_k + B u_k$, $y_k = C x_k$ over any field $K$, avoiding Cayley–Hamilton by transporting stabilization through module duality.
  - `unobs A C k`: Unobservable subspace $\bigcap_{i < k} \ker(C A^i)$ and its recursive characterization `unobs_succ`: $N_{k+1} = \ker C \cap A^{-1}(N_k)$.
  - `unobs_eq_dualCoannihilator_reach`: Exact duality $N_k(A, C) = (R_k(A^*, C^*))^\top$ via `Submodule.dualCoannihilator`.
  - `observable_iff_controllable_dual`: **Kalman Duality Theorem**: $(A, C)$ is observable iff $(A^*, C^*)$ is controllable.
  - `unobs_eq_unobs_finrank`: Stabilization of the unobservable subspace at $k = \dim_K V$.
  - `observable_iff_forall` & `Observable.eq_of_output_eq`: Initial state uniqueness from $\dim_K V$ output measurements under arbitrary known inputs.
  - `unobs_outputInjection` & `observable_outputInjection`: Invariance of observability under output injection $A \mapsto A + L C$.
- **Literature References**:
  - Kalman, R. E. (1960). On the general theory of control systems. *IRE Transactions on Automatic Control*, 4(3), 110.
  - Wonham, W. M. (1985). *Linear Multivariable Control: A Geometric Approach* (3rd ed.). Springer, Chapter 3.
  - Sontag, E. D. (1998). *Mathematical Control Theory* (2nd ed.). Springer, Chapter 6.

---

## 4. `ControlsLean.Vision.Triangulation` — Two-View Triangulation & Cheirality (Issue #13, PR #16)
- **File**: `ControlsLean/Vision/Triangulation.lean`
- **Mathematical Content**:
  Formalizes exact two-view depth recovery, existence/uniqueness of ray intersection, and cheirality for $d_2 x_2 = R(d_1 x_1) + t$.
  - `smul_cross_eq_of_scene` & `smul_cross_eq_of_scene'`: Elimination of $d_2$ and $d_1$ by taking cross products with $x_2$ and $R x_1$.
  - `depth₁_eq`, `depth₂_eq`, `depths_unique`: Closed-form depth formulas and uniqueness whenever rays are non-parallel ($x_2 \times R x_1 \ne 0$).
  - `scene_closedForm` & `exists_depths_iff`: For non-parallel rays, a depth pair $(d_1, d_2)$ solving $d_2 x_2 = R(d_1 x_1) + t$ exists iff the epipolar constraint $x_2^\top E x_1 = 0$ holds.
  - `cheirality`: Replacing $t$ with $-t$ preserves $E$ up to sign (`essential_neg`) and negates both depths, so positive depths ($d_1 > 0, d_2 > 0$) uniquely disambiguate the translation sign.
- **Literature References**:
  - Longuet-Higgins, H. C. (1981). A computer algorithm for reconstructing a scene from two projections. *Nature*, 293, 133–135.
  - Hartley, R., & Zisserman, A. (2004). *Multiple View Geometry in Computer Vision* (2nd ed.). Cambridge University Press, Sections 9.6 and 12.2.
  - Ma, Y., Soatto, S., Košecká, J., & Sastry, S. S. (2004). *An Invitation to 3-D Vision*. Springer, Chapter 5.

---

## 5. `ControlsLean.Controls.SmallGain` — Discrete-Time Small-Gain Theorem (Issue #15, PR #18)
- **File**: `ControlsLean/Controls/SmallGain.lean`
- **Mathematical Content**:
  Formalizes the discrete-time small-gain theorem on sequences $\mathbb{N} \to E$ in seminormed groups using truncated supremum norms $\|u\|_k = \max_{i \le k} \|u_i\|$ (`truncNorm`).
  - `truncNorm`, `HasGain`, `Causal`: Truncated signal norms, finite-gain operators with affine bias $\|G u\|_k \le \gamma \|u\|_k + \beta$, and causality (`Causal.truncNorm_eq`).
  - `small_gain_left`, `small_gain_right`, `small_gain`: For interconnected systems $e_1 = u_1 + G_2 e_2$, $e_2 = u_2 + G_1 e_1$ with $\gamma_1 \gamma_2 < 1$, proves explicit truncated-norm bounds:
    $$\|e_1\|_k \le \frac{\|u_1\|_k + \gamma_2 \|u_2\|_k + \beta_2 + \gamma_2 \beta_1}{1 - \gamma_1 \gamma_2}.$$
  - `small_gain_bounded`: Bounded-input bounded-output (BIBO) stability for all time $i \in \mathbb{N}$.
  - `HasGain.linear_zero_bias` & `small_gain_linear`: Any $\mathbb{R}$-linear operator with finite gain $\gamma$ and bias $\beta$ has gain $\gamma$ with zero bias ($\beta = 0$) by homogeneity scaling.
- **Literature References**:
  - Zames, G. (1966). On the input-output stability of time-varying nonlinear feedback systems — Part I: Conditions derived using concepts of loop gain, conicity, and positivity. *IEEE Transactions on Automatic Control*, 11(2), 228–238.
  - Desoer, C. A., & Vidyasagar, M. (1975). *Feedback Systems: Input-Output Properties*. Academic Press, Chapter III.
  - Khalil, H. K. (2002). *Nonlinear Systems* (3rd ed.). Prentice Hall, Section 5.4.

---

## 6. `ControlsLean.Estimation.AlphaBeta` — Steady-State $\alpha$–$\beta$ Filter & Kalata Relation (Issue #17, PR #19)
- **File**: `ControlsLean/Estimation/AlphaBeta.lean`
- **Mathematical Content**:
  Formalizes the steady-state discrete-time Kalman filter for a constant-velocity target tracker ($F = \begin{bmatrix} 1 & T \\ 0 & 1 \end{bmatrix}$, $H = \begin{bmatrix} 1 & 0 \end{bmatrix}$) under Bar-Shalom's discrete white-noise acceleration process covariance $Q = q g g^\top$ with $g = [T^2/2, T]^\top$.
  - `riccatiMap_eq_iff`: Equivalences between the $2 \times 2$ matrix algebraic Riccati fixed-point equation and the entrywise system `IsSteadyState`.
  - `gain_quadratic`: The steady-state gains $\alpha = p_{11}/(p_{11}+r)$ and $\beta = T p_{12}/(p_{11}+r)$ satisfy $\alpha^2 = (2 - \alpha)\beta - \beta^2/4$.
  - `beta_sq_div`: Tracking index identity $\beta^2 / (1 - \alpha) = \lambda^2 = q T^4 / r$.
  - `kalata`: For any positive semidefinite steady-state covariance with $p_{11} > 0$, $0 < \alpha < 1$, $0 < \beta \le 2\alpha$, and $\beta = 2(2 - \alpha) - 4\sqrt{1 - \alpha}$.
  - `isSteadyState_of_gains`, `exists_gains`, `exists_steadyState`: Closed-form existence of gains and a strictly positive-definite steady-state covariance for every $T, q, r > 0$ via $u = \sqrt{1 - \alpha}$ (`kalataU`).
- **Literature References**:
  - Kalata, P. R. (1984). The tracking index: A generalized parameter for $\alpha$-$\beta$ and $\alpha$-$\beta$-$\gamma$ target trackers. *IEEE Transactions on Aerospace and Electronic Systems*, AES-20(2), 174–182.
  - Bar-Shalom, Y., Li, X. R., & Kirubarajan, T. (2001). *Estimation with Applications to Tracking and Navigation*. Wiley, Sections 6.3 and 6.5.

---

## 7. `ControlsLean.Controls.Companion` — Companion Matrices & Canonical Pole Placement (Issue #8 Part 1, PR #20)
- **File**: `ControlsLean/Controls/Companion.lean`
- **Mathematical Content**:
  Formalizes $n \times n$ companion matrices in controllable canonical form over an arbitrary commutative ring $R$ and proves pole placement and controllability for companion pairs.
  - `companion` & `charpoly_companion`: By Laplace expansion along the first column (`Matrix.det_succ_column_zero`), proves $\operatorname{charpoly}(\operatorname{companion}(a)) = X^n + \sum_{i=0}^{n-1} a_i X^i$.
  - `companion_add_vecMulVec` & `charpoly_companion_feedback`: State feedback $u = k^\top x$ with input $e_n$ (`companionB`) shifts only the last row: $\operatorname{companion}(a) + e_n k^\top = \operatorname{companion}(a - k)$.
  - `exists_feedback_charpoly_eq`: Every monic degree-$(n+1)$ polynomial $p \in R[X]$ is achieved as the closed-loop characteristic polynomial for $k_i = a_i - p_i$.
  - `controllable_companion` & `controllable_companion_feedback`: Over a field $K$, every companion pair $(\operatorname{companion}(a), e_n)$ is controllable in the sense of `ControlsLean.Controls.Controllable`.
- **Literature References**:
  - Kailath, T. (1980). *Linear Systems*. Prentice-Hall, Section 2.3.
  - Wonham, W. M. (1985). *Linear Multivariable Control: A Geometric Approach* (3rd ed.). Springer, Chapter 2.

---

## 8. `ControlsLean.Controls.PolePlacementGeneral` — General-$n$ Single-Input Pole Placement (Issue #8 Part 2, PR #21)
- **File**: `ControlsLean/Controls/PolePlacementGeneral.lean`
- **Mathematical Content**:
  Proves the general-$n$ single-input pole placement theorem over an arbitrary field $K$.
  - `canonVec`: Constructs the Horner basis vectors $w_j = (\operatorname{divX}^{[j+1]} \chi_A)(A) b$, satisfying $w_n = b$ (`canonVec_last`), $A w_{j+1} = w_j - c_{j+1} b$ (`mulVec_canonVec_succ`), and $A w_0 = -c_0 b$ (`mulVec_canonVec_zero`, via Cayley–Hamilton `aeval_self_charpoly`).
  - `top_le_span_canonVec` & `canonBasis`: If $(A, b)$ is controllable, $\{w_0, \dots, w_n\}$ spans $K^{n+1}$ and therefore forms a basis (`basisOfTopLeSpanOfCardEqFinrank`).
  - `toMatrix_canonBasis` & `repr_canonBasis_b`: In `canonBasis`, $A$ has matrix `companion c` and $b$ has coordinate vector $e_n$.
  - `toMatrix_canonBasis_add_vecMulVec` & `charpoly_add_vecMulVec_eq`: Similarity invariance of the closed-loop characteristic polynomial $\operatorname{charpoly}(A + b k^\top)$.
  - `pole_placement`: **General-$n$ Pole Placement Theorem**: For any controllable pair $(A, b)$ over a field $K$ and any monic polynomial $p \in K[X]$ of degree $n + 1$, there exists $k : \operatorname{Fin}(n+1) \to K$ such that $\operatorname{charpoly}(A + b k^\top) = p$.
- **Literature References**:
  - Wonham, W. M. (1967). On pole assignment in multi-input controllable linear systems. *IEEE Transactions on Automatic Control*, 12(6), 660–665.
  - Ackermann, J. (1972). Der Entwurf linearer Regelungssysteme im Zustandsraum. *Regelungstechnik und Prozess-Datenverarbeitung*, 20(7), 297–300.
  - Sontag, E. D. (1998). *Mathematical Control Theory* (2nd ed.). Springer, Theorem 13 (Pole Shifting Theorem).

---

## Exact Module Imports for `ControlsLean.lean`

```lean
import ControlsLean.Controls.Jury2
import ControlsLean.Vision.EightPoint
import ControlsLean.Controls.Observability
import ControlsLean.Vision.Triangulation
import ControlsLean.Controls.SmallGain
import ControlsLean.Estimation.AlphaBeta
import ControlsLean.Controls.Companion
import ControlsLean.Controls.PolePlacementGeneral
```

## Exact `#print axioms` Lines for `scripts/Audit.lean`

```lean
-- Issue #5: Controls (Jury stability test, degree 2)
#print axioms ControlsLean.Controls.isSchur2_iff
#print axioms ControlsLean.Controls.isSchur2_iff_jury

-- Issue #9: Vision (Eight-point algorithm: E determined up to scale)
#print axioms ControlsLean.Vision.finrank_ker_constraintMatrix
#print axioms ControlsLean.Vision.eq_smul_of_rank_eq_eight
#print axioms ControlsLean.Vision.essential_satisfies_constraints
#print axioms ControlsLean.Vision.eq_smul_essential

-- Issue #4: Controls (Observability as the dual of controllability, without Cayley-Hamilton)
#print axioms ControlsLean.Controls.unobs_eq_dualCoannihilator_reach
#print axioms ControlsLean.Controls.observable_iff_controllable_dual
#print axioms ControlsLean.Controls.unobs_eq_unobs_finrank
#print axioms ControlsLean.Controls.observable_iff_forall
#print axioms ControlsLean.Controls.Observable.eq_of_output_eq
#print axioms ControlsLean.Controls.observable_outputInjection

-- Issue #13: Vision (Two-view triangulation)
#print axioms ControlsLean.Vision.depth₁_eq
#print axioms ControlsLean.Vision.depth₂_eq
#print axioms ControlsLean.Vision.depths_unique
#print axioms ControlsLean.Vision.scene_closedForm
#print axioms ControlsLean.Vision.exists_depths_iff
#print axioms ControlsLean.Vision.cheirality

-- Issue #15: Controls (Discrete-time small-gain theorem)
#print axioms ControlsLean.Controls.small_gain
#print axioms ControlsLean.Controls.small_gain_bounded
#print axioms ControlsLean.Controls.HasGain.linear_zero_bias
#print axioms ControlsLean.Controls.small_gain_linear

-- Issue #17: Estimation (Steady-state alpha-beta filter & Kalata relation)
#print axioms ControlsLean.Estimation.AlphaBeta.riccatiMap_eq_iff
#print axioms ControlsLean.Estimation.AlphaBeta.gain_quadratic
#print axioms ControlsLean.Estimation.AlphaBeta.beta_sq_div
#print axioms ControlsLean.Estimation.AlphaBeta.kalata
#print axioms ControlsLean.Estimation.AlphaBeta.isSteadyState_of_gains
#print axioms ControlsLean.Estimation.AlphaBeta.exists_gains
#print axioms ControlsLean.Estimation.AlphaBeta.exists_steadyState

-- Issue #8, part 1: Controls (Companion matrix & pole placement in canonical form)
#print axioms ControlsLean.Controls.charpoly_companion
#print axioms ControlsLean.Controls.companion_add_vecMulVec
#print axioms ControlsLean.Controls.charpoly_companion_feedback
#print axioms ControlsLean.Controls.exists_feedback_charpoly_eq
#print axioms ControlsLean.Controls.controllable_companion

-- Issue #8, part 2: Controls (Pole placement for controllable single-input systems)
#print axioms ControlsLean.Controls.top_le_span_canonVec
#print axioms ControlsLean.Controls.toMatrix_canonBasis
#print axioms ControlsLean.Controls.repr_canonBasis_b
#print axioms ControlsLean.Controls.charpoly_add_vecMulVec_eq
#print axioms ControlsLean.Controls.pole_placement
```
