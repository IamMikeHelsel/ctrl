/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DiscreteLyapunov
import Mathlib.Tactic.Abel

/-!
# Discrete-Time Linear Quadratic Regulator (LQR), Bellman Completion of Squares & DARE Stability

This module formalizes the multivariate discrete-time Linear Quadratic Regulator (LQR)
and Discrete Algebraic Riccati Equation (DARE) for linear time-invariant systems
$$x_{k+1} = A x_k + B u_k, \qquad x_k \in \mathbb{R}^n,\; u_k \in \mathbb{R}^m,$$
with stage cost $\ell(x, u) = x^\top Q x + u^\top R u$ and quadratic cost-to-go $V(x) = x^\top P x$.

## Main definitions and theorems

- `lqrHessian P B R`: The control-input Hessian $G = R + B^\top P B \in \mathbb{R}^{m \times m}$.
- `lqrClosedLoop A B K`: The state-feedback closed-loop matrix $A_K = A - B K$.
- `lqrJosephUpdate P A B Q R K`: The Joseph-form LQR Riccati operator
  $\mathcal{R}_K(P) = Q + K^\top R K + (A - B K)^\top P (A - B K)$.
- `lqr_joseph_completion_of_squares`: If $P^\top = P$, $R^\top = R$, and $K^*$ satisfies the
  optimal LQR gain normal equation $(R + B^\top P B) K^* = B^\top P A$, then for any feedback
  gain $K$:
  $$\mathcal{R}_K(P) = \mathcal{R}_{K^*}(P) + (K - K^*)^\top (R + B^\top P B) (K - K^*).$$
- `lqr_bellman_completion_of_squares`: Pointwise Bellman equation completion of squares for any
  state $x \in \mathbb{R}^n$ and control input $u \in \mathbb{R}^m$:
  $$x^\top Q x + u^\top R u + (A x + B u)^\top P (A x + B u)
    = x^\top \mathcal{R}_{K^*}(P) x + (u + K^* x)^\top (R + B^\top P B) (u + K^* x).$$
- `lqr_bellman_min_le`: Under positive semidefinite Hessian $G = R + B^\top P B \succeq 0$,
  the linear state feedback $u^* = -K^* x$ globally minimizes the Bellman one-step cost-to-go
  over all control inputs $u \in \mathbb{R}^m$.
- `dare_lyapunov_dissipation`: At a DARE fixed point $P = \mathcal{R}_K(P)$, the closed-loop
  Lyapunov dissipation matrix equals $P - A_K^\top P A_K = Q + K^\top R K$.
- `dare_closedLoop_tendsto_zero`: If $P \succ 0$ satisfies the Joseph DARE
  $P = Q + K^\top R K + (A - B K)^\top P (A - B K)$ with $Q + K^\top R K \succ 0$, then the
  closed-loop trajectory $x_{k+1} = (A - B K) x_k$ is globally asymptotically stable
  ($(A - B K)^k x_0 \to 0$).
-/

namespace ControlsLean.Controls

open Matrix Filter Topology

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The LQR control-input Hessian matrix $G = R + B^\top P B \in \mathbb{R}^{m \times m}$. -/
def lqrHessian (P : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ) : Matrix m m ℝ :=
  R + Bᵀ * P * B

/-- Closed-loop transition matrix under linear state feedback $u = -K x$:
$A_K = A - B K$. -/
def lqrClosedLoop (A : Matrix n n ℝ) (B : Matrix n m ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  A - B * K

/-- Joseph-form LQR Riccati operator for a feedback gain $K$:
$\mathcal{R}_K(P) = Q + K^\top R K + (A - B K)^\top P (A - B K)$. -/
def lqrJosephUpdate (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  Q + Kᵀ * R * K + (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K

omit [Fintype m] in
/-- Symmetry of the LQR Hessian $G = R + B^\top P B$. -/
theorem lqrHessian_transpose {P : Matrix n n ℝ} (B : Matrix n m ℝ) {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (lqrHessian P B R)ᵀ = lqrHessian P B R := by
  unfold lqrHessian
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hR, Matrix.mul_assoc]

/-- Expansion of the Joseph-form LQR Riccati operator in terms of `lqrHessian`:
$\mathcal{R}_K(P) = Q + A^\top P A - A^\top P B K - K^\top B^\top P A + K^\top G K$. -/
theorem lqrJosephUpdate_expand (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) :
    lqrJosephUpdate P A B Q R K =
      Q + Aᵀ * P * A - Aᵀ * P * B * K - Kᵀ * Bᵀ * P * A + Kᵀ * lqrHessian P B R * K := by
  unfold lqrJosephUpdate lqrClosedLoop lqrHessian
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- Transposed LQR normal equation: if $P^\top = P$, $R^\top = R$, and
$G K^* = B^\top P A$, then $(K^*)^\top G = A^\top P B$. -/
theorem lqr_normal_eq_transpose {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix m n ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) :
    Kstarᵀ * lqrHessian P B R = Aᵀ * P * B := by
  calc Kstarᵀ * lqrHessian P B R
      = (lqrHessian P B R * Kstar)ᵀ := by rw [transpose_mul, lqrHessian_transpose B hP hR]
    _ = (Bᵀ * P * A)ᵀ := by rw [hKstar]
    _ = Aᵀ * P * B := by simp only [transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

/-- At the optimal gain $K^*$ satisfying $G K^* = B^\top P A$, the Joseph Riccati update reduces to
$Q + A^\top P A - (K^*)^\top G K^*$. -/
theorem lqrJosephUpdate_opt_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) :
    lqrJosephUpdate P A B Q R Kstar =
      Q + Aᵀ * P * A - Kstarᵀ * lqrHessian P B R * Kstar := by
  have hKT : Kstarᵀ * lqrHessian P B R = Aᵀ * P * B := lqr_normal_eq_transpose hP hR hKstar
  have h1 : Aᵀ * P * B * Kstar = Kstarᵀ * lqrHessian P B R * Kstar := by rw [hKT]
  have h2 : Kstarᵀ * Bᵀ * P * A = Kstarᵀ * lqrHessian P B R * Kstar := by
    calc Kstarᵀ * Bᵀ * P * A
        = Kstarᵀ * (Bᵀ * P * A) := by simp only [Matrix.mul_assoc]
      _ = Kstarᵀ * (lqrHessian P B R * Kstar) := by rw [hKstar]
      _ = Kstarᵀ * lqrHessian P B R * Kstar := by simp only [Matrix.mul_assoc]
  rw [lqrJosephUpdate_expand, h1, h2]
  abel

/-- **Matrix Completion of Squares for the LQR Joseph Riccati Update**:
If $P^\top = P$, $R^\top = R$, and $G K^* = B^\top P A$, then for any gain matrix $K$:
$\mathcal{R}_K(P) = \mathcal{R}_{K^*}(P) + (K - K^*)^\top (R + B^\top P B) (K - K^*)$. -/
theorem lqr_joseph_completion_of_squares {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) (K : Matrix m n ℝ) :
    lqrJosephUpdate P A B Q R K =
      lqrJosephUpdate P A B Q R Kstar + (K - Kstar)ᵀ * lqrHessian P B R * (K - Kstar) := by
  have hKT : Kstarᵀ * lqrHessian P B R = Aᵀ * P * B := lqr_normal_eq_transpose hP hR hKstar
  have h1 : Aᵀ * P * B * K = Kstarᵀ * lqrHessian P B R * K := by rw [hKT]
  have h2 : Kᵀ * Bᵀ * P * A = Kᵀ * lqrHessian P B R * Kstar := by
    calc Kᵀ * Bᵀ * P * A
        = Kᵀ * (Bᵀ * P * A) := by simp only [Matrix.mul_assoc]
      _ = Kᵀ * (lqrHessian P B R * Kstar) := by rw [hKstar]
      _ = Kᵀ * lqrHessian P B R * Kstar := by simp only [Matrix.mul_assoc]
  rw [lqrJosephUpdate_expand P A B Q R K, lqrJosephUpdate_opt_eq hP hR hKstar, h1, h2]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- Adjoint identity for matrix-vector dot products: $(M u) \cdot y = u \cdot (M^\top y)$. -/
theorem mulVec_dotProduct_eq (M : Matrix n m ℝ) (u : m → ℝ) (y : n → ℝ) :
    (M *ᵥ u) ⬝ᵥ y = u ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

/-- **Bellman Equation Completion of Squares**:
For any state $x \in \mathbb{R}^n$ and any control input $u \in \mathbb{R}^m$,
$x^\top Q x + u^\top R u + (A x + B u)^\top P (A x + B u) =
x^\top \mathcal{R}_{K^*}(P) x + (u + K^* x)^\top (R + B^\top P B) (u + K^* x)$. -/
theorem lqr_bellman_completion_of_squares {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (x : n → ℝ) (u : m → ℝ) :
    quad Q x + quad R u + quad P (A *ᵥ x + B *ᵥ u) =
      quad (lqrJosephUpdate P A B Q R Kstar) x +
        quad (lqrHessian P B R) (u + Kstar *ᵥ x) := by
  have h_opt := lqrJosephUpdate_opt_eq (Q := Q) hP hR hKstar
  have hKT : Kstarᵀ * lqrHessian P B R = Aᵀ * P * B := lqr_normal_eq_transpose hP hR hKstar
  have h_cross1 : (A *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ u)) = (Kstar *ᵥ x) ⬝ᵥ (lqrHessian P B R *ᵥ u) := by
    calc (A *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ u))
        = x ⬝ᵥ (Aᵀ *ᵥ (P *ᵥ (B *ᵥ u))) := mulVec_dotProduct_eq A x _
      _ = x ⬝ᵥ ((Aᵀ * P * B) *ᵥ u) := by simp only [← mulVec_mulVec]
      _ = x ⬝ᵥ ((Kstarᵀ * lqrHessian P B R) *ᵥ u) := by rw [hKT]
      _ = (Kstar *ᵥ x) ⬝ᵥ (lqrHessian P B R *ᵥ u) := by
          rw [← mulVec_mulVec, ← mulVec_dotProduct_eq Kstar x]
  have h_cross2 : (B *ᵥ u) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = u ⬝ᵥ (lqrHessian P B R *ᵥ (Kstar *ᵥ x)) := by
    calc (B *ᵥ u) ⬝ᵥ (P *ᵥ (A *ᵥ x))
        = u ⬝ᵥ (Bᵀ *ᵥ (P *ᵥ (A *ᵥ x))) := mulVec_dotProduct_eq B u _
      _ = u ⬝ᵥ ((Bᵀ * P * A) *ᵥ x) := by simp only [← mulVec_mulVec]
      _ = u ⬝ᵥ ((lqrHessian P B R * Kstar) *ᵥ x) := by rw [hKstar]
      _ = u ⬝ᵥ (lqrHessian P B R *ᵥ (Kstar *ᵥ x)) := by rw [← mulVec_mulVec]
  have h_quadA : (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((Aᵀ * P * A) *ᵥ x) := by
    rw [mulVec_dotProduct_eq A x, ← mulVec_mulVec, ← mulVec_mulVec]
  have h_quadB : (B *ᵥ u) ⬝ᵥ (P *ᵥ (B *ᵥ u)) = u ⬝ᵥ ((Bᵀ * P * B) *ᵥ u) := by
    rw [mulVec_dotProduct_eq B u, ← mulVec_mulVec, ← mulVec_mulVec]
  have h_quadK :
      (Kstar *ᵥ x) ⬝ᵥ (lqrHessian P B R *ᵥ (Kstar *ᵥ x)) =
        x ⬝ᵥ ((Kstarᵀ * lqrHessian P B R * Kstar) *ᵥ x) := by
    rw [mulVec_dotProduct_eq Kstar x, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [h_opt]
  dsimp [quad]
  simp only [add_mulVec, sub_mulVec, mulVec_add, dotProduct_add, add_dotProduct, dotProduct_sub]
  rw [h_quadA, h_quadB, h_cross1, h_cross2, ← h_quadK]
  unfold lqrHessian
  simp only [add_mulVec, dotProduct_add]
  linarith

/-- **Bellman Optimality of the LQR State-Feedback Law**:
If $G = R + B^\top P B$ is positive semidefinite ($\forall v, 0 \le v^\top G v$), then for every
state $x \in \mathbb{R}^n$ and control input $u \in \mathbb{R}^m$, the optimal feedback
$u^* = -K^* x$ achieves the minimum one-step Bellman cost-to-go $x^\top \mathcal{R}_{K^*}(P) x$:
$x^\top \mathcal{R}_{K^*}(P) x \le x^\top Q x + u^\top R u + (A x + B u)^\top P (A x + B u)$. -/
theorem lqr_bellman_min_le {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hG : ∀ v : m → ℝ, 0 ≤ quad (lqrHessian P B R) v)
    (x : n → ℝ) (u : m → ℝ) :
    quad (lqrJosephUpdate P A B Q R Kstar) x ≤
      quad Q x + quad R u + quad P (A *ᵥ x + B *ᵥ u) := by
  rw [lqr_bellman_completion_of_squares hP hR hKstar x u]
  linarith [hG (u + Kstar *ᵥ x)]

/-- **DARE Lyapunov Dissipation Identity**:
At any solution $P = \mathcal{R}_K(P)$ of the Joseph-form Riccati equation, the closed-loop
Stein/Lyapunov difference equals the stage cost matrix $Q + K^\top R K$:
$P - (A - B K)^\top P (A - B K) = Q + K^\top R K$. -/
theorem dare_lyapunov_dissipation {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hdare : lqrJosephUpdate P A B Q R K = P) :
    P - (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K = Q + Kᵀ * R * K := by
  calc P - (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K
      = lqrJosephUpdate P A B Q R K - (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K := by
        nth_rw 1 [← hdare]
    _ = Q + Kᵀ * R * K := by
        unfold lqrJosephUpdate
        abel

/-- **Global Asymptotic Stability of Discrete-Time LQR**:
If $P$ is positive definite ($x^\top P x > 0$ for $x \ne 0$), satisfies the Joseph-form DARE
$P = \mathcal{R}_K(P)$, and the closed-loop stage cost $Q + K^\top R K$ is positive definite
($x^\top (Q + K^\top R K) x > 0$ for $x \ne 0$), then every closed-loop trajectory converges
geometrically to the origin: $((A - B K)^k) x_0 \to 0$ as $k \to \infty$. -/
theorem dare_closedLoop_tendsto_zero [DecidableEq n]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hP : ∀ x ≠ 0, 0 < quad P x)
    (hdare : lqrJosephUpdate P A B Q R K = P)
    (hQR : ∀ x ≠ 0, 0 < quad (Q + Kᵀ * R * K) x)
    (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (lqrClosedLoop A B K ^ k) *ᵥ x₀) atTop (𝓝 0) := by
  refine tendsto_pow_mulVec_zero hP ?_ x₀
  rw [dare_lyapunov_dissipation hdare]
  exact hQR

end ControlsLean.Controls
