/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DAREDetectable
import ControlsLean.Estimation.KalmanOptimality
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Continuous-Time Algebraic Riccati Equation (CARE), HJB Optimality & the Kalman–Bucy Filter

This module formalizes the continuous-time counterparts of the discrete-time LQR and Kalman filter
theories in `LQR.lean`, `DAREExistence.lean`, `KalmanOptimality.lean`, and
`SteadyStateKalman.lean`, closing Roadmap §3.3.

## 1. Continuous-Time LQR and the Algebraic Riccati Equation (CARE)

For the continuous-time LTI system $\dot{x} = A x + B u$ with quadratic stage cost
$\ell(x, u) = x^\top Q x + u^\top R u$ and value function $V(x) = x^\top P x$:

- `careGain B R P`: The optimal continuous-time LQR feedback gain $K^* = R^{-1} B^\top P$.
- `careResidual P A B Q R`: The CARE matrix residual
  $$A^\top P + P A - P B R^{-1} B^\top P + Q.$$
- `careJoseph P A B Q R K`: The continuous-time Joseph / Hamiltonian Lyapunov operator
  $$(A - B K)^\top P + P (A - B K) + Q + K^\top R K.$$
- `care_completion_of_squares`: For any state-feedback gain $K$ and optimal gain $K^*$ satisfying
  $R K^* = B^\top P$,
  $$\operatorname{careJoseph}(K) = \operatorname{careJoseph}(K^*) + (K - K^*)^\top R (K - K^*).$$
- `care_closedLoop_lyapunov`: At a CARE solution $\operatorname{careJoseph}(K^*) = 0$, the
  closed-loop matrix $A_{\text{cl}} = A - B K^*$ satisfies the continuous-time Lyapunov equation
  $$A_{\text{cl}}^\top P + P A_{\text{cl}} = -(Q + (K^*)^\top R K^*).$$
- `care_lie_derivative_neg`: When $P, Q, R \succ 0$ and $P$ solves the CARE, $V(x) = x^\top P x$
  has strictly negative Lie derivative $\dot{V}(x) = -x^\top (Q + (K^*)^\top R K^*) x < 0$ for all
  $x \ne 0$ along $\dot{x} = A_{\text{cl}} x$.

## 2. Continuous-Time Hamilton–Jacobi–Bellman (HJB) & `HasDerivAt` Trajectory Calculus

- `care_hjb_completion_of_squares`: For any state $x$ and control input $u$,
  $$2 x^\top P (A x + B u) + x^\top Q x + u^\top R u =
    x^\top \operatorname{careJoseph}(K^*) x + (u + K^* x)^\top R (u + K^* x).$$
- `hasDerivAt_quad`: Along any differentiable trajectory $x : \mathbb{R} \to (n \to \mathbb{R})$
  with componentwise derivative $\dot{x}(t) = x'$ (`HasVecDerivAt x x' t`) and symmetric $P$,
  $\frac{d}{dt} (x(t)^\top P x(t)) = 2 x(t)^\top P x'$.
- `hasDerivAt_care_hjb`: Along any trajectory satisfying $\dot{x}(t) = A x(t) + B u(t)$ at a CARE
  solution $P$, the instantaneous rate of change of $x(t)^\top P x(t)$ plus stage cost equals the
  exact quadratic square completion $(u(t) + K^* x(t))^\top R (u(t) + K^* x(t)) \ge 0$.

## 3. Dual Continuous-Time Kalman–Bucy Filter

For the continuous-time state-space plant with process noise covariance rate $W$ and measurement
noise covariance rate $V$:

- `kalmanBucyGain P C V`: The Kalman–Bucy filter gain $L^* = P C^\top V^{-1}$.
- `kalmanBucyCovDeriv P A C W V L`: The differential Riccati covariance derivative for an arbitrary
  observer gain $L$:
  $$\dot{P}(L) = (A - L C) P + P (A - L C)^\top + W + L V L^\top.$$
- `kalmanBucyCovDeriv_completion_of_squares`:
  $$\dot{P}(L) = \dot{P}(L^*) + (L - L^*) V (L - L^*)^\top.$$
- `kalmanBucy_loewner_optimal`, `kalmanBucy_trace_optimal`: The Kalman–Bucy gain $L^*$ minimizes
  the covariance rate $\dot{P}(L)$ in both the Loewner order and the matrix trace order among all
  linear observer gains $L$.
- `kalmanBucy_steadyState_lyapunov`, `kalmanBucy_steadyState_negDef`: At a steady-state solution of
  $A P + P A^\top - P C^\top V^{-1} C P + W = 0$, the observer error matrix $A - L^* C$ satisfies
  $$(A - L^* C) P + P (A - L^* C)^\top = -(W + L^* V (L^*)^\top) \prec 0.$$

## References

- R. E. Kalman, R. S. Bucy, *New results in linear filtering and prediction theory*, Trans. ASME
  J. Basic Eng. 83 (1961), 95–108.
- B. D. O. Anderson, J. B. Moore, *Optimal Control: Linear Quadratic Methods* (1990), Ch. 2–3.
- H. Kwakernaak, R. Sivan, *Linear Optimal Control Systems* (1972), Ch. 3–4.
-/

namespace ControlsLean.Estimation

open Matrix Filter Topology BigOperators ControlsLean.Controls ControlsLean.Tactics

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]

/-! ### 1. Continuous-Time LQR & Algebraic Riccati Equation (CARE) -/

/-- Optimal continuous-time LQR feedback gain $K^* = R^{-1} B^\top P$. -/
noncomputable def careGain [DecidableEq m] (B : Matrix n m ℝ) (R : Matrix m m ℝ)
    (P : Matrix n n ℝ) : Matrix m n ℝ :=
  R⁻¹ * Bᵀ * P

/-- Standard Continuous-Time Algebraic Riccati Equation (CARE) matrix residual:
$$A^\top P + P A - P B R^{-1} B^\top P + Q.$$ -/
noncomputable def careResidual [DecidableEq m] (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) : Matrix n n ℝ :=
  Aᵀ * P + P * A - P * B * R⁻¹ * Bᵀ * P + Q

/-- Continuous-time Joseph / Hamiltonian Lyapunov operator for a feedback gain $K$:
$$(A - B K)^\top P + P (A - B K) + Q + K^\top R K.$$ -/
def careJoseph (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  (lqrClosedLoop A B K)ᵀ * P + P * lqrClosedLoop A B K + Q + Kᵀ * R * K

omit [Fintype p] in
/-- The optimal gain `careGain B R P` solves the continuous-time LQR normal equation
$R K^* = B^\top P$ whenever $R \succ 0$. -/
theorem care_normal_eq [DecidableEq m] {P : Matrix n n ℝ} {B : Matrix n m ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) :
    R * careGain B R P = Bᵀ * P := by
  unfold careGain
  have hdet : IsUnit R.det := hR.det_pos.ne'.isUnit
  rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left R (Bᵀ * P) hdet]

omit [Fintype p] in
/-- Transposed continuous-time LQR normal equation: if $P^\top = P$, $R^\top = R$, and
$R K^* = B^\top P$, then $(K^*)^\top R = P B$. -/
theorem care_normal_eq_transpose {P : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix m n ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : R * Kstar = Bᵀ * P) :
    Kstarᵀ * R = P * B := by
  calc Kstarᵀ * R
      = (R * Kstar)ᵀ := by rw [transpose_mul, hR]
    _ = (Bᵀ * P)ᵀ := by rw [hKstar]
    _ = P * B := by rw [transpose_mul, transpose_transpose, hP]

omit [Fintype p] in
/-- Expansion of the continuous-time Joseph operator:
$$\operatorname{careJoseph}(K) = A^\top P + P A + Q - K^\top B^\top P - P B K + K^\top R K.$$ -/
theorem careJoseph_expand (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) :
    careJoseph P A B Q R K =
      Aᵀ * P + P * A + Q - Kᵀ * Bᵀ * P - P * B * K + Kᵀ * R * K := by
  unfold careJoseph lqrClosedLoop
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [Fintype p] in
/-- At a gain $K^*$ satisfying $R K^* = B^\top P$, the continuous-time Joseph operator reduces to
$$A^\top P + P A - (K^*)^\top R K^* + Q.$$ -/
theorem careJoseph_opt_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P) :
    careJoseph P A B Q R Kstar = Aᵀ * P + P * A - Kstarᵀ * R * Kstar + Q := by
  have hKT : Kstarᵀ * R = P * B := care_normal_eq_transpose hP hR hKstar
  have h1 : Kstarᵀ * Bᵀ * P = Kstarᵀ * R * Kstar := by
    calc Kstarᵀ * Bᵀ * P = Kstarᵀ * (Bᵀ * P) := by simp only [Matrix.mul_assoc]
      _ = Kstarᵀ * (R * Kstar) := by rw [hKstar]
      _ = Kstarᵀ * R * Kstar := by simp only [Matrix.mul_assoc]
  have h2 : P * B * Kstar = Kstarᵀ * R * Kstar := by rw [hKT]
  rw [careJoseph_expand, h1, h2]
  abel

omit [Fintype p] in
/-- For $R \succ 0$ and symmetric $P$, evaluating `careJoseph` at `careGain B R P` yields the
standard CARE residual $A^\top P + P A - P B R^{-1} B^\top P + Q$. -/
theorem careJoseph_careGain_eq_careResidual [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : R.PosDef) :
    careJoseph P A B Q R (careGain B R P) = careResidual P A B Q R := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hnorm := care_normal_eq (P := P) (B := B) hR
  have hKT : (careGain B R P)ᵀ * R = P * B := care_normal_eq_transpose hP hR'.1 hnorm
  rw [careJoseph_opt_eq hP hR'.1 hnorm, hKT]
  unfold careResidual careGain
  simp only [Matrix.mul_assoc]

omit [Fintype p] in
/-- **Headline Theorem 1 — CARE Matrix Completion of Squares**:
If $P^\top = P$, $R^\top = R$, and $R K^* = B^\top P$, then for every feedback gain $K$:
$$\operatorname{careJoseph}(K) =
  \operatorname{careJoseph}(K^*) + (K - K^*)^\top R (K - K^*).$$ -/
theorem care_completion_of_squares {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P) (K : Matrix m n ℝ) :
    careJoseph P A B Q R K =
      careJoseph P A B Q R Kstar + (K - Kstar)ᵀ * R * (K - Kstar) := by
  have hKT : Kstarᵀ * R = P * B := care_normal_eq_transpose hP hR hKstar
  have h1 : Kᵀ * Bᵀ * P = Kᵀ * R * Kstar := by
    calc Kᵀ * Bᵀ * P = Kᵀ * (Bᵀ * P) := by simp only [Matrix.mul_assoc]
      _ = Kᵀ * (R * Kstar) := by rw [hKstar]
      _ = Kᵀ * R * Kstar := by simp only [Matrix.mul_assoc]
  have h2 : P * B * K = Kstarᵀ * R * K := by rw [hKT]
  rw [careJoseph_expand P A B Q R K, careJoseph_opt_eq hP hR hKstar, h1, h2]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [Fintype p] in
/-- **CARE Closed-Loop Hamiltonian Lyapunov Identity** (Joseph form):
If $\operatorname{careJoseph} P A B Q R K = 0$, then for $A_{\text{cl}} = A - B K$,
$$A_{\text{cl}}^\top P + P A_{\text{cl}} = -(Q + K^\top R K).$$ -/
theorem care_closedLoop_lyapunov {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hcare : careJoseph P A B Q R K = 0) :
    (lqrClosedLoop A B K)ᵀ * P + P * lqrClosedLoop A B K = -(Q + Kᵀ * R * K) := by
  unfold careJoseph at hcare
  calc (lqrClosedLoop A B K)ᵀ * P + P * lqrClosedLoop A B K
      = ((lqrClosedLoop A B K)ᵀ * P + P * lqrClosedLoop A B K + Q + Kᵀ * R * K) -
          (Q + Kᵀ * R * K) := by abel
    _ = 0 - (Q + Kᵀ * R * K) := by rw [hcare]
    _ = -(Q + Kᵀ * R * K) := by abel

omit [Fintype p] in
/-- **CARE Closed-Loop Hamiltonian Lyapunov Identity** (Standard CARE form):
If $P^\top = P$, $R \succ 0$, and $A^\top P + P A - P B R^{-1} B^\top P + Q = 0$, then for
$K^* = R^{-1} B^\top P$ and $A_{\text{cl}} = A - B K^*$,
$$A_{\text{cl}}^\top P + P A_{\text{cl}} = -(Q + (K^*)^\top R K^*).$$ -/
theorem care_closedLoop_lyapunov_of_careResidual [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : R.PosDef) (hcare : careResidual P A B Q R = 0) :
    (lqrClosedLoop A B (careGain B R P))ᵀ * P + P * lqrClosedLoop A B (careGain B R P) =
      -(Q + (careGain B R P)ᵀ * R * careGain B R P) := by
  apply care_closedLoop_lyapunov
  rwa [careJoseph_careGain_eq_careResidual hP hR]

/-! ### 2. Continuous-Time Lie Derivative & Strict Lyapunov Decrease -/

omit [Fintype m] [Fintype p] in
/-- For a symmetric matrix $P^\top = P$ and any matrix $M$, the quadratic form of the symmetric
Lyapunov operator $M^\top P + P M$ equals $2 x^\top P (M x)$. -/
theorem quad_symm_mul_eq_two_dotProduct {P M : Matrix n n ℝ} (hP : Pᵀ = P) (x : n → ℝ) :
    quad (Mᵀ * P + P * M) x = 2 * (x ⬝ᵥ (P *ᵥ (M *ᵥ x))) := by
  have h1 : x ⬝ᵥ ((Mᵀ * P) *ᵥ x) = x ⬝ᵥ (P *ᵥ (M *ᵥ x)) := by
    calc x ⬝ᵥ ((Mᵀ * P) *ᵥ x)
        = x ⬝ᵥ (Mᵀ *ᵥ (P *ᵥ x)) := by rw [← mulVec_mulVec]
      _ = (P *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
          rw [dotProduct_comm, mulVec_dotProduct_eq, transpose_transpose]
      _ = x ⬝ᵥ (Pᵀ *ᵥ (M *ᵥ x)) := mulVec_dotProduct_eq P x (M *ᵥ x)
      _ = x ⬝ᵥ (P *ᵥ (M *ᵥ x)) := by rw [hP]
  rw [quad_add]
  dsimp [quad]
  rw [h1, ← mulVec_mulVec]
  ring

omit [Fintype p] in
/-- **Lie Derivative of $V(x) = x^\top P x$ along the CARE Closed Loop**:
If $P^\top = P$ and $\operatorname{careJoseph} P A B Q R K = 0$, then for every state $x$:
$$2 x^\top P (A_{\text{cl}} x) = -\left(x^\top Q x + (K x)^\top R (K x)\right).$$ -/
theorem care_lie_derivative_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hP : Pᵀ = P) (hcare : careJoseph P A B Q R K = 0) (x : n → ℝ) :
    2 * (x ⬝ᵥ (P *ᵥ (lqrClosedLoop A B K *ᵥ x))) =
      -(quad Q x + quad R (K *ᵥ x)) := by
  rw [← quad_symm_mul_eq_two_dotProduct hP, care_closedLoop_lyapunov hcare,
    quad_neg, quad_add, quad_mulVec_rect]

omit [Fintype p] in
/-- **Headline Theorem 2 — Strict Negative Definiteness of the CARE Lie Derivative**:
If $P \succ 0$, $Q \succ 0$, $R \succ 0$, and $P$ solves the CARE
$A^\top P + P A - P B R^{-1} B^\top P + Q = 0$, then for every nonzero state $x \ne 0$:
1. $V(x) = x^\top P x > 0$, and
2. $\dot{V}(x) = 2 x^\top P (A_{\text{cl}} x) = -x^\top (Q + (K^*)^\top R K^*) x < 0$. -/
theorem care_lie_derivative_neg [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : P.PosDef) (hQ : Q.PosDef) (hR : R.PosDef)
    (hcare : careResidual P A B Q R = 0) {x : n → ℝ} (hx : x ≠ 0) :
    0 < quad P x ∧
      2 * (x ⬝ᵥ (P *ᵥ (lqrClosedLoop A B (careGain B R P) *ᵥ x))) < 0 := by
  have hP' := hP
  have hQ' := hQ
  rw [posDef_iff_quad_pos] at hP' hQ'
  have hjos : careJoseph P A B Q R (careGain B R P) = 0 := by
    rwa [careJoseph_careGain_eq_careResidual hP'.1 hR]
  refine ⟨hP'.2 x hx, ?_⟩
  rw [care_lie_derivative_eq hP'.1 hjos x]
  have hpos : 0 < quad Q x + quad R (careGain B R P *ᵥ x) :=
    add_pos_of_pos_of_nonneg (hQ'.2 x hx) (quad_nonneg_of_posDef hR _)
  linarith

/-! ### 3. Continuous-Time Hamilton–Jacobi–Bellman (HJB) Identity & Trajectory Calculus -/

omit [Fintype p] in
/-- **Headline Theorem 3 — Continuous-Time Hamilton–Jacobi–Bellman Completion of Squares**:
If $P^\top = P$, $R^\top = R$, and $R K^* = B^\top P$, then for any state $x \in \mathbb{R}^n$
and control input $u \in \mathbb{R}^m$:
$$2 x^\top P (A x + B u) + x^\top Q x + u^\top R u =
  x^\top \operatorname{careJoseph}(K^*) x + (u + K^* x)^\top R (u + K^* x).$$ -/
theorem care_hjb_completion_of_squares {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P)
    (x : n → ℝ) (u : m → ℝ) :
    2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u))) + quad Q x + quad R u =
      quad (careJoseph P A B Q R Kstar) x + quad R (u + Kstar *ᵥ x) := by
  have hopt := careJoseph_opt_eq (A := A) (Q := Q) hP hR hKstar
  have hKT : Kstarᵀ * R = P * B := care_normal_eq_transpose hP hR hKstar
  have hAx : 2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x))) = quad (Aᵀ * P + P * A) x :=
    (quad_symm_mul_eq_two_dotProduct hP x).symm
  have hBu1 : x ⬝ᵥ (P *ᵥ (B *ᵥ u)) = (Kstar *ᵥ x) ⬝ᵥ (R *ᵥ u) := by
    calc x ⬝ᵥ (P *ᵥ (B *ᵥ u))
        = x ⬝ᵥ ((P * B) *ᵥ u) := by rw [← mulVec_mulVec]
      _ = x ⬝ᵥ ((Kstarᵀ * R) *ᵥ u) := by rw [hKT]
      _ = (Kstar *ᵥ x) ⬝ᵥ (R *ᵥ u) := by rw [← mulVec_mulVec, ← mulVec_dotProduct_eq Kstar x]
  have hBu2 : x ⬝ᵥ (P *ᵥ (B *ᵥ u)) = u ⬝ᵥ (R *ᵥ (Kstar *ᵥ x)) := by
    rw [hBu1, dotProduct_comm, mulVec_dotProduct_eq, hR]
  have hquadK : (Kstar *ᵥ x) ⬝ᵥ (R *ᵥ (Kstar *ᵥ x)) = quad (Kstarᵀ * R * Kstar) x := by
    change quad R (Kstar *ᵥ x) = _
    exact quad_mulVec_rect R Kstar x
  rw [hopt, mulVec_add, dotProduct_add, mul_add, hAx]
  rw [quad_add (Aᵀ * P + P * A - Kstarᵀ * R * Kstar) Q,
      quad_sub (Aᵀ * P + P * A) (Kstarᵀ * R * Kstar)]
  dsimp [quad] at hquadK ⊢
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  linarith [hBu1, hBu2, hquadK]

omit [Fintype p] in
/-- **HJB Identity at a CARE Solution**:
If $P^\top = P$, $R^\top = R$, $R K^* = B^\top P$, and
$\operatorname{careJoseph} P A B Q R K^* = 0$, then for every state $x$ and control input $u$:
$$2 x^\top P (A x + B u) + x^\top Q x + u^\top R u = (u + K^* x)^\top R (u + K^* x).$$ -/
theorem care_hjb_eq_of_solution {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P)
    (hcare : careJoseph P A B Q R Kstar = 0)
    (x : n → ℝ) (u : m → ℝ) :
    2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u))) + quad Q x + quad R u =
      quad R (u + Kstar *ᵥ x) := by
  rw [care_hjb_completion_of_squares hP hR hKstar x u, hcare]
  simp [quad]

omit [Fintype p] in
/-- **Pointwise HJB Optimality**:
Under $R \succeq 0$ and $\operatorname{careJoseph} P A B Q R K^* = 0$, the linear state feedback
$u^* = -K^* x$ globally minimizes the HJB Hamiltonian over all $u \in \mathbb{R}^m$:
$$0 \le 2 x^\top P (A x + B u) + x^\top Q x + u^\top R u.$$ -/
theorem care_hjb_nonneg_of_solution {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P)
    (hcare : careJoseph P A B Q R Kstar = 0)
    (hR_psd : ∀ v : m → ℝ, 0 ≤ quad R v) (x : n → ℝ) (u : m → ℝ) :
    0 ≤ 2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u))) + quad Q x + quad R u := by
  rw [care_hjb_eq_of_solution hP hR hKstar hcare x u]
  exact hR_psd (u + Kstar *ᵥ x)

/-- Componentwise time derivative of a vector trajectory $x : \mathbb{R} \to (\iota \to \mathbb{R})$
at time $t$. -/
def HasVecDerivAt {ι : Type*} (x : ℝ → ι → ℝ) (x' : ι → ℝ) (t : ℝ) : Prop :=
  ∀ i : ι, HasDerivAt (fun s => x s i) (x' i) t

omit [Fintype m] [Fintype p] in
/-- Product rule for the Euclidean dot product of two differentiable vector trajectories. -/
theorem hasDerivAt_dotProduct {x y : ℝ → n → ℝ} {x' y' : n → ℝ} {t : ℝ}
    (hx : HasVecDerivAt x x' t) (hy : HasVecDerivAt y y' t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t := by
  unfold dotProduct
  rw [← Finset.sum_add_distrib]
  have h := HasDerivAt.sum (u := (Finset.univ : Finset n)) fun i _ => (hx i).mul (hy i)
  have hfun : (∑ i : n, (fun s => x s i) * (fun s => y s i)) =
      (fun s => ∑ i : n, x s i * y s i) := by
    ext s
    simp
  rwa [hfun] at h

omit [Fintype n] [Fintype p] in
/-- Linearity of `HasVecDerivAt` under matrix-vector multiplication. -/
theorem hasVecDerivAt_mulVec (M : Matrix n m ℝ) {x : ℝ → m → ℝ} {x' : m → ℝ} {t : ℝ}
    (hx : HasVecDerivAt x x' t) :
    HasVecDerivAt (fun s => M *ᵥ x s) (M *ᵥ x') t := by
  intro i
  unfold mulVec dotProduct
  have h := HasDerivAt.sum (u := (Finset.univ : Finset m)) fun j _ => (hx j).const_mul (M i j)
  have hfun : (∑ j : m, fun s => M i j * x s j) = (fun s => ∑ j : m, M i j * x s j) := by
    ext s
    simp
  rwa [hfun] at h

omit [Fintype m] [Fintype p] in
/-- **Time Derivative of a Symmetric Quadratic Form**:
If $P^\top = P$ and $x : \mathbb{R} \to (n \to \mathbb{R})$ has derivative $x'$ at $t$, then
$\frac{d}{dt} (x(t)^\top P x(t)) = 2 x(t)^\top P x'$. -/
theorem hasDerivAt_quad {P : Matrix n n ℝ} (hP : Pᵀ = P)
    {x : ℝ → n → ℝ} {x' : n → ℝ} {t : ℝ} (hx : HasVecDerivAt x x' t) :
    HasDerivAt (fun s => quad P (x s)) (2 * (x t ⬝ᵥ (P *ᵥ x'))) t := by
  have h := hasDerivAt_dotProduct hx (hasVecDerivAt_mulVec P hx)
  have hsym : x' ⬝ᵥ (P *ᵥ x t) = x t ⬝ᵥ (P *ᵥ x') := by
    rw [dotProduct_comm, mulVec_dotProduct_eq, hP]
  have hd : x' ⬝ᵥ (P *ᵥ x t) + x t ⬝ᵥ (P *ᵥ x') = 2 * (x t ⬝ᵥ (P *ᵥ x')) := by linarith
  rwa [hd] at h

omit [Fintype p] in
/-- **Calculus HJB Identity along Differentiable State-Control Trajectories**:
If $P$ solves $\operatorname{careJoseph} P A B Q R K^* = 0$ with $R K^* = B^\top P$, and a
trajectory $x : \mathbb{R} \to (n \to \mathbb{R})$ satisfies $\dot{x}(t) = A x(t) + B u(t)$ at
time $t$, then $s \mapsto x(s)^\top P x(s)$ has derivative
$$(u(t) + K^* x(t))^\top R (u(t) + K^* x(t)) - \left(x(t)^\top Q x(t) + u(t)^\top R u(t)\right)$$
at time $t$. -/
theorem hasDerivAt_care_hjb {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : R * Kstar = Bᵀ * P)
    (hcare : careJoseph P A B Q R Kstar = 0)
    {x : ℝ → n → ℝ} {u : ℝ → m → ℝ} {t : ℝ}
    (hx : HasVecDerivAt x (A *ᵥ x t + B *ᵥ u t) t) :
    HasDerivAt (fun s => quad P (x s))
      (quad R (u t + Kstar *ᵥ x t) - (quad Q (x t) + quad R (u t))) t := by
  have hderiv := hasDerivAt_quad hP hx
  have hhjb := care_hjb_eq_of_solution hP hR hKstar hcare (x t) (u t)
  have hd : 2 * (x t ⬝ᵥ (P *ᵥ (A *ᵥ x t + B *ᵥ u t))) =
      quad R (u t + Kstar *ᵥ x t) - (quad Q (x t) + quad R (u t)) := by linarith
  rwa [hd] at hderiv

/-! ### 4. Dual Continuous-Time Kalman–Bucy Filter & Error Covariance Optimality -/

/-- Continuous-time Kalman–Bucy filter gain $L^* = P C^\top V^{-1}$. -/
noncomputable def kalmanBucyGain [DecidableEq p] (P : Matrix n n ℝ) (C : Matrix p n ℝ)
    (V : Matrix p p ℝ) : Matrix n p ℝ :=
  P * Cᵀ * V⁻¹

/-- Dual Continuous-Time Algebraic Riccati Equation (Kalman–Bucy CARE) residual:
$$A P + P A^\top - P C^\top V^{-1} C P + W.$$ -/
noncomputable def kalmanBucyResidual [DecidableEq p] (P A : Matrix n n ℝ) (C : Matrix p n ℝ)
    (W : Matrix n n ℝ) (V : Matrix p p ℝ) : Matrix n n ℝ :=
  A * P + P * Aᵀ - P * Cᵀ * V⁻¹ * C * P + W

/-- Differential Riccati error covariance derivative for an arbitrary observer gain $L$:
$$\dot{P}(L) = (A - L C) P + P (A - L C)^\top + W + L V L^\top.$$ -/
def kalmanBucyCovDeriv (P A : Matrix n n ℝ) (C : Matrix p n ℝ)
    (W : Matrix n n ℝ) (V : Matrix p p ℝ) (L : Matrix n p ℝ) : Matrix n n ℝ :=
  (A - L * C) * P + P * (A - L * C)ᵀ + W + L * V * Lᵀ

omit [Fintype m] in
/-- The Kalman–Bucy gain `kalmanBucyGain P C V` solves the normal equation $L^* V = P C^\top$
whenever $V \succ 0$. -/
theorem kalmanBucy_normal_eq [DecidableEq p] {P : Matrix n n ℝ} {C : Matrix p n ℝ}
    {V : Matrix p p ℝ} (hV : V.PosDef) :
    kalmanBucyGain P C V * V = P * Cᵀ := by
  unfold kalmanBucyGain
  have hdet : IsUnit V.det := hV.det_pos.ne'.isUnit
  rw [Matrix.mul_assoc, nonsing_inv_mul V hdet, Matrix.mul_one]

omit [Fintype m] in
/-- Transposed Kalman–Bucy normal equation: if $P^\top = P$, $V^\top = V$, and
$L^* V = P C^\top$, then $V (L^*)^\top = C P$. -/
theorem kalmanBucy_normal_eq_transpose {P : Matrix n n ℝ} {C : Matrix p n ℝ}
    {V : Matrix p p ℝ} {Lstar : Matrix n p ℝ}
    (hP : Pᵀ = P) (hV : Vᵀ = V) (hLstar : Lstar * V = P * Cᵀ) :
    V * Lstarᵀ = C * P := by
  calc V * Lstarᵀ
      = (Lstar * V)ᵀ := by rw [transpose_mul, hV]
    _ = (P * Cᵀ)ᵀ := by rw [hLstar]
    _ = C * P := by rw [transpose_mul, transpose_transpose, hP]

omit [Fintype m] in
/-- Expansion of the Kalman–Bucy covariance derivative:
$$\dot{P}(L) = A P + P A^\top + W - L C P - P C^\top L^\top + L V L^\top.$$ -/
theorem kalmanBucyCovDeriv_expand (P A : Matrix n n ℝ) (C : Matrix p n ℝ)
    (W : Matrix n n ℝ) (V : Matrix p p ℝ) (L : Matrix n p ℝ) :
    kalmanBucyCovDeriv P A C W V L =
      A * P + P * Aᵀ + W - L * C * P - P * Cᵀ * Lᵀ + L * V * Lᵀ := by
  unfold kalmanBucyCovDeriv
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [Fintype m] in
/-- At an optimal gain $L^*$ satisfying $L^* V = P C^\top$, the covariance derivative reduces to
$$A P + P A^\top - L^* V (L^*)^\top + W.$$ -/
theorem kalmanBucyCovDeriv_opt_eq {P A : Matrix n n ℝ} {C : Matrix p n ℝ}
    {W : Matrix n n ℝ} {V : Matrix p p ℝ} {Lstar : Matrix n p ℝ}
    (hP : Pᵀ = P) (hV : Vᵀ = V) (hLstar : Lstar * V = P * Cᵀ) :
    kalmanBucyCovDeriv P A C W V Lstar =
      A * P + P * Aᵀ - Lstar * V * Lstarᵀ + W := by
  have hVL : V * Lstarᵀ = C * P := kalmanBucy_normal_eq_transpose hP hV hLstar
  have h1 : Lstar * C * P = Lstar * V * Lstarᵀ := by
    calc Lstar * C * P = Lstar * (C * P) := by simp only [Matrix.mul_assoc]
      _ = Lstar * (V * Lstarᵀ) := by rw [hVL]
      _ = Lstar * V * Lstarᵀ := by simp only [Matrix.mul_assoc]
  have h2 : P * Cᵀ * Lstarᵀ = Lstar * V * Lstarᵀ := by rw [← hLstar]
  rw [kalmanBucyCovDeriv_expand, h1, h2]
  abel

omit [Fintype m] in
/-- Evaluating `kalmanBucyCovDeriv` at `kalmanBucyGain P C V` yields `kalmanBucyResidual`. -/
theorem kalmanBucyCovDeriv_opt_eq_residual [DecidableEq p]
    {P A : Matrix n n ℝ} {C : Matrix p n ℝ} {W : Matrix n n ℝ} {V : Matrix p p ℝ}
    (hP : Pᵀ = P) (hV : V.PosDef) :
    kalmanBucyCovDeriv P A C W V (kalmanBucyGain P C V) =
      kalmanBucyResidual P A C W V := by
  have hV' := hV
  rw [posDef_iff_quad_pos] at hV'
  have hnorm := kalmanBucy_normal_eq (P := P) (C := C) hV
  have hVL : V * (kalmanBucyGain P C V)ᵀ = C * P :=
    kalmanBucy_normal_eq_transpose hP hV'.1 hnorm
  rw [kalmanBucyCovDeriv_opt_eq hP hV'.1 hnorm, Matrix.mul_assoc (kalmanBucyGain P C V) V _,
    hVL]
  unfold kalmanBucyResidual kalmanBucyGain
  simp only [Matrix.mul_assoc]

omit [Fintype m] in
/-- **Headline Theorem 4 — Kalman–Bucy Covariance Derivative Completion of Squares**:
If $P^\top = P$, $V^\top = V$, and $L^* V = P C^\top$, then for every observer gain $L$:
$$\dot{P}(L) = \dot{P}(L^*) + (L - L^*) V (L - L^*)^\top.$$ -/
theorem kalmanBucyCovDeriv_completion_of_squares {P A : Matrix n n ℝ} {C : Matrix p n ℝ}
    {W : Matrix n n ℝ} {V : Matrix p p ℝ} {Lstar : Matrix n p ℝ}
    (hP : Pᵀ = P) (hV : Vᵀ = V) (hLstar : Lstar * V = P * Cᵀ) (L : Matrix n p ℝ) :
    kalmanBucyCovDeriv P A C W V L =
      kalmanBucyCovDeriv P A C W V Lstar + (L - Lstar) * V * (L - Lstar)ᵀ := by
  have hVL : V * Lstarᵀ = C * P := kalmanBucy_normal_eq_transpose hP hV hLstar
  have h1 : L * C * P = L * V * Lstarᵀ := by
    calc L * C * P = L * (C * P) := by simp only [Matrix.mul_assoc]
      _ = L * (V * Lstarᵀ) := by rw [hVL]
      _ = L * V * Lstarᵀ := by simp only [Matrix.mul_assoc]
  have h2 : P * Cᵀ * Lᵀ = Lstar * V * Lᵀ := by rw [← hLstar]
  rw [kalmanBucyCovDeriv_expand P A C W V L, kalmanBucyCovDeriv_opt_eq hP hV hLstar, h1, h2]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [Fintype m] in
/-- **Loewner Optimality of the Kalman–Bucy Gain**:
If $P^\top = P$ and $V \succ 0$, the Kalman–Bucy gain $L^* = P C^\top V^{-1}$ minimizes the
error covariance derivative $\dot{P}(L)$ in the Loewner order among all observer gains $L$:
$$\dot{P}(L^*) \preceq \dot{P}(L).$$ -/
theorem kalmanBucy_loewner_optimal [DecidableEq p]
    {P A : Matrix n n ℝ} {C : Matrix p n ℝ} {W : Matrix n n ℝ} {V : Matrix p p ℝ}
    (hP : Pᵀ = P) (hV : V.PosDef) (L : Matrix n p ℝ) :
    LoewnerLE (kalmanBucyCovDeriv P A C W V (kalmanBucyGain P C V))
      (kalmanBucyCovDeriv P A C W V L) := by
  intro x
  have hV' := hV
  rw [posDef_iff_quad_pos] at hV'
  rw [kalmanBucyCovDeriv_completion_of_squares hP hV'.1 (kalmanBucy_normal_eq hV) L, quad_add]
  have hquad : quad ((L - kalmanBucyGain P C V) * V * (L - kalmanBucyGain P C V)ᵀ) x =
      quad V ((L - kalmanBucyGain P C V)ᵀ *ᵥ x) := by
    simpa [quad] using quad_conj_transpose (L - kalmanBucyGain P C V) V x
  rw [hquad]
  linarith [quad_nonneg_of_posDef hV ((L - kalmanBucyGain P C V)ᵀ *ᵥ x)]

omit [Fintype m] in
/-- **Trace (MMSE Rate) Optimality of the Kalman–Bucy Gain**:
If $P^\top = P$ and $V \succ 0$, the Kalman–Bucy gain $L^* = P C^\top V^{-1}$ minimizes the
trace of the error covariance derivative $\operatorname{tr}(\dot{P}(L))$ over all observer
gains $L$:
$$\operatorname{tr}(\dot{P}(L^*)) \le \operatorname{tr}(\dot{P}(L)).$$ -/
theorem kalmanBucy_trace_optimal [DecidableEq p]
    {P A : Matrix n n ℝ} {C : Matrix p n ℝ} {W : Matrix n n ℝ} {V : Matrix p p ℝ}
    (hP : Pᵀ = P) (hV : V.PosDef) (L : Matrix n p ℝ) :
    Matrix.trace (kalmanBucyCovDeriv P A C W V (kalmanBucyGain P C V)) ≤
      Matrix.trace (kalmanBucyCovDeriv P A C W V L) := by
  classical
  rw [trace_eq_sum_quad_single, trace_eq_sum_quad_single]
  refine Finset.sum_le_sum fun i _ => ?_
  exact kalmanBucy_loewner_optimal hP hV L (Pi.single i 1)

omit [Fintype m] in
/-- **Steady-State Kalman–Bucy Dual Lyapunov Identity**:
At a steady-state solution $\dot{P}(L) = 0$, the observer error matrix $A - L C$ satisfies
$$(A - L C) P + P (A - L C)^\top = -(W + L V L^\top).$$ -/
theorem kalmanBucy_steadyState_lyapunov {P A : Matrix n n ℝ} {C : Matrix p n ℝ}
    {W : Matrix n n ℝ} {V : Matrix p p ℝ} {L : Matrix n p ℝ}
    (hss : kalmanBucyCovDeriv P A C W V L = 0) :
    (A - L * C) * P + P * (A - L * C)ᵀ = -(W + L * V * Lᵀ) := by
  unfold kalmanBucyCovDeriv at hss
  calc (A - L * C) * P + P * (A - L * C)ᵀ
      = ((A - L * C) * P + P * (A - L * C)ᵀ + W + L * V * Lᵀ) - (W + L * V * Lᵀ) := by abel
    _ = 0 - (W + L * V * Lᵀ) := by rw [hss]
    _ = -(W + L * V * Lᵀ) := by abel

omit [Fintype m] in
/-- **Strict Negative Definiteness of the Steady-State Kalman–Bucy Error Lyapunov Operator**:
If $W \succ 0$, $V \succ 0$, $P^\top = P$, and $P$ solves the steady-state Kalman–Bucy CARE
$A P + P A^\top - P C^\top V^{-1} C P + W = 0$, then for $L^* = P C^\top V^{-1}$ and every
nonzero vector $x \ne 0$:
$$x^\top \left((A - L^* C) P + P (A - L^* C)^\top\right) x < 0.$$ -/
theorem kalmanBucy_steadyState_negDef [DecidableEq p]
    {P A : Matrix n n ℝ} {C : Matrix p n ℝ} {W : Matrix n n ℝ} {V : Matrix p p ℝ}
    (hP : Pᵀ = P) (hW : W.PosDef) (hV : V.PosDef)
    (hcare : kalmanBucyResidual P A C W V = 0) {x : n → ℝ} (hx : x ≠ 0) :
    quad ((A - kalmanBucyGain P C V * C) * P + P * (A - kalmanBucyGain P C V * C)ᵀ) x < 0 := by
  have hW' := hW
  rw [posDef_iff_quad_pos] at hW'
  have hss : kalmanBucyCovDeriv P A C W V (kalmanBucyGain P C V) = 0 := by
    rwa [kalmanBucyCovDeriv_opt_eq_residual hP hV]
  rw [kalmanBucy_steadyState_lyapunov hss, quad_neg, quad_add]
  have hquad : quad (kalmanBucyGain P C V * V * (kalmanBucyGain P C V)ᵀ) x =
      quad V ((kalmanBucyGain P C V)ᵀ *ᵥ x) := by
    simpa [quad] using quad_conj_transpose (kalmanBucyGain P C V) V x
  rw [hquad]
  have hpos : 0 < quad W x + quad V ((kalmanBucyGain P C V)ᵀ *ᵥ x) :=
    add_pos_of_pos_of_nonneg (hW'.2 x hx) (quad_nonneg_of_posDef hV _)
  linarith

/-- **Continuous-Time Kalman–Bucy / Luenberger Observer Error ODE**:
If the plant trajectory $x(t)$ satisfies $\dot{x}(t) = A x(t) + B u(t)$ and the observer
trajectory $\hat{x}(t)$ satisfies
$\dot{\hat{x}}(t) = A \hat{x}(t) + B u(t) + L (C x(t) - C \hat{x}(t))$, then the estimation error
$e(t) = x(t) - \hat{x}(t)$ satisfies the autonomous linear ODE
$\dot{e}(t) = (A - L C) e(t)$, completely invariant to the control input $u(t)$. -/
theorem hasVecDerivAt_kalmanBucy_error {A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {L : Matrix n p ℝ}
    {x xhat : ℝ → n → ℝ} {u : ℝ → m → ℝ} {t : ℝ}
    (hx : HasVecDerivAt x (A *ᵥ x t + B *ᵥ u t) t)
    (hxhat : HasVecDerivAt xhat
      (A *ᵥ xhat t + B *ᵥ u t + L *ᵥ (C *ᵥ x t - C *ᵥ xhat t)) t) :
    HasVecDerivAt (fun s => x s - xhat s) ((A - L * C) *ᵥ (x t - xhat t)) t := by
  have heq : (A *ᵥ x t + B *ᵥ u t) -
      (A *ᵥ xhat t + B *ᵥ u t + L *ᵥ (C *ᵥ x t - C *ᵥ xhat t)) =
      (A - L * C) *ᵥ (x t - xhat t) := by
    simp only [sub_mulVec, mulVec_sub, ← mulVec_mulVec]
    abel
  rw [← heq]
  intro i
  exact (hx i).sub (hxhat i)

end ControlsLean.Estimation
