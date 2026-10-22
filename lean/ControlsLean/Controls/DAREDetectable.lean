/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DARE
import ControlsLean.Controls.ConverseLyapunov
import ControlsLean.Tactics.ControlTactics
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Detectability Theory for the DARE, Zero-Step Escape & LQR Quadratic Robustness

In control engineering, LQR penalties frequently weight only a measured performance output
$y_k = C x_k$, giving a positive semidefinite state cost
$$Q = C^\top C \succeq 0$$
that may have a nontrivial kernel.

This module relaxes $Q \succ 0$ to **detectability** of $(A, C)$ (`IsDetectable A C`), proving the
Kwakernaak–Sivan / Wonham discrete-time LQR and Kalman detectability theorem without spectral theory
or complex eigenvalues, and establishes the **discrete-time LQR return-difference and quadratic
robustness identities**:

1. **Factored DARE Dissipation & Zero-Step Escape (`joseph_dissipation_factored`,
   `joseph_zero_dissipation_escape`, `dare_dissipation_factored`, `dare_zero_dissipation_escape`)**:
   At any solution $P = \mathcal{R}_K(P)$ of the Joseph DARE with $Q = C^\top C$,
   $$x^\top P x - (A_K x)^\top P (A_K x) = \|C x\|_2^2 + (K x)^\top R (K x).$$
   If $(A_K x)^\top P (A_K x) = x^\top P x$ and $R \succ 0$, then $C x = 0$ and $K x = 0$, so the
   closed-loop step coincides with both the open-loop step $A x$ and the observer step
   $(A - L C) x$.

2. **Schur Stability & Uniqueness under Detectability (`joseph_schur_of_detectable`,
   `dare_schur_of_detectable`, `dare_unique_of_detectable`)**:
   If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ satisfies $P = \mathcal{R}_K(P)$ for
   $Q = C^\top C$, then $A - B K$ is Schur stable, and the DARE for $Q = C^\top C$ admits at most
   one symmetric PSD solution.

3. **LQR Return-Difference & Quadratic Gain-Margin Robustness
   (`dare_bellman_return_difference`, `dare_perturbed_lyapunov_dissipation`,
   `dare_optimal_dominates_perturbed_bellman`, `dare_perturbed_dissipation_ge_of_margin`)**:
   For any perturbed state-feedback gain $K^* + \Delta K$, the one-step Bellman / Hamiltonian cost
   exceeds that of the optimal gain $K^*$ by the exact quadratic return-difference penalty
   $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \ge 0$. Whenever a gain perturbation lies within
   the quadratic disk margin $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \le
   ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x)$, the perturbed closed loop still dissipates at
   least $x^\top Q x$ at every step.

## References

- H. Kwakernaak, R. Sivan, *Linear Optimal Control Systems* (1972), §6.4.
- P. Lancaster, L. Rodman, *Algebraic Riccati Equations* (1995), Ch. 13.
- D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. I, §4.1.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology BigOperators ControlsLean.Tactics

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]

/-! ### 0. LQR Joseph Operator, Riccati Map & Converging-Input Converging-State Preliminaries -/

/-- The LQR control-input Hessian matrix $G = R + B^\top P B \in \mathbb{R}^{m \times m}$. -/
def lqrHessian (P : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ) : Matrix m m ℝ :=
  R + Bᵀ * P * B

/-- Joseph-form LQR Riccati operator for a feedback gain $K$:
$\mathcal{R}_K(P) = Q + K^\top R K + (A - B K)^\top P (A - B K)$. -/
def lqrJosephUpdate (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  Q + Kᵀ * R * K + (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K

/-- One-step LQR stage cost $\ell(x, u) = x^\top Q x + u^\top R u$. -/
def lqrStage (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (x : n → ℝ) (u : m → ℝ) : ℝ :=
  quad Q x + quad R u

/-- Loewner order expressed through quadratic forms: $P \preceq P'$. -/
def LoewnerLE (P P' : Matrix n n ℝ) : Prop := ∀ x : n → ℝ, quad P x ≤ quad P' x

omit [Fintype m] [Fintype p] in
theorem LoewnerLE.refl (P : Matrix n n ℝ) : LoewnerLE P P := fun _ => le_rfl

omit [Fintype m] [Fintype p] in
theorem LoewnerLE.trans {P P' P'' : Matrix n n ℝ} (h₁ : LoewnerLE P P') (h₂ : LoewnerLE P' P'') :
    LoewnerLE P P'' := fun x => (h₁ x).trans (h₂ x)

/-- Symmetric positive semidefinite, in quadratic-form language. -/
def SymPSD (P : Matrix n n ℝ) : Prop := Pᵀ = P ∧ ∀ x : n → ℝ, 0 ≤ quad P x

/-- The optimal Riccati gain $K(P) = (R + B^\top P B)^{-1} B^\top P A$. -/
noncomputable def riccatiGain [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) : Matrix m n ℝ :=
  (lqrHessian P B R)⁻¹ * (Bᵀ * P * A)

/-- The Riccati map $\mathcal{T}(P) = \mathcal{R}_{K(P)}(P)$. -/
noncomputable def riccatiMap [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (P : Matrix n n ℝ) : Matrix n n ℝ :=
  lqrJosephUpdate P A B Q R (riccatiGain A B R P)

omit [Fintype m] [Fintype p] in
theorem lqrHessian_transpose {P : Matrix n n ℝ} (B : Matrix n m ℝ) {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (lqrHessian P B R)ᵀ = lqrHessian P B R := by
  unfold lqrHessian
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hR, Matrix.mul_assoc]

omit [Fintype p] in
theorem lqrJosephUpdate_expand (P A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (K : Matrix m n ℝ) :
    lqrJosephUpdate P A B Q R K =
      Q + Aᵀ * P * A - Aᵀ * P * B * K - Kᵀ * Bᵀ * P * A + Kᵀ * lqrHessian P B R * K := by
  unfold lqrJosephUpdate lqrClosedLoop lqrHessian
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

omit [Fintype p] in
theorem lqr_normal_eq_transpose {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix m n ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) :
    Kstarᵀ * lqrHessian P B R = Aᵀ * P * B := by
  calc Kstarᵀ * lqrHessian P B R
      = (lqrHessian P B R * Kstar)ᵀ := by rw [transpose_mul, lqrHessian_transpose B hP hR]
    _ = (Bᵀ * P * A)ᵀ := by rw [hKstar]
    _ = Aᵀ * P * B := by simp only [transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

omit [Fintype p] in
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

omit [Fintype p] in
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

omit [Fintype p] in
theorem mulVec_dotProduct_eq (M : Matrix n m ℝ) (u : m → ℝ) (y : n → ℝ) :
    (M *ᵥ u) ⬝ᵥ y = u ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

omit [Fintype p] in
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

omit [Fintype p] in
theorem quad_lqrJosephUpdate (P A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (K : Matrix m n ℝ) (x : n → ℝ) :
    quad (lqrJosephUpdate P A B Q R K) x =
      quad Q x + quad R (K *ᵥ x) + quad P (lqrClosedLoop A B K *ᵥ x) := by
  unfold lqrJosephUpdate
  rw [quad_add, quad_add, quad_mulVec_rect, quad_mulVec]

omit [Fintype p] in
theorem quad_lqrHessian (P : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ) (v : m → ℝ) :
    quad (lqrHessian P B R) v = quad R v + quad P (B *ᵥ v) := by
  unfold lqrHessian
  rw [quad_add, quad_mulVec_rect]

set_option linter.unusedFintypeInType false in
omit [Fintype p] in
theorem lqrHessian_posDef {P : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) : (lqrHessian P B R).PosDef := by
  rw [posDef_iff_quad_pos] at hR ⊢
  refine ⟨lqrHessian_transpose B hP.1 hR.1, fun v hv => ?_⟩
  rw [quad_lqrHessian]
  linarith [hR.2 v hv, hP.2 (B *ᵥ v)]

omit [Fintype n] [Fintype p] in
theorem quad_nonneg_of_posDef {R : Matrix m m ℝ} (hR : R.PosDef) (v : m → ℝ) : 0 ≤ quad R v := by
  rw [posDef_iff_quad_pos] at hR
  rcases eq_or_ne v 0 with rfl | hv
  · simp [quad]
  · exact (hR.2 v hv).le

omit [Fintype p] in
theorem riccatiGain_normal_eq [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) (hP : SymPSD P) :
    lqrHessian P B R * riccatiGain A B R P = Bᵀ * P * A := by
  unfold riccatiGain
  have hpos : (lqrHessian P B R).PosDef := lqrHessian_posDef hR hP
  have hdet : IsUnit (lqrHessian P B R).det := hpos.det_pos.ne'.isUnit
  exact mul_nonsing_inv_cancel_left _ _ hdet

omit [Fintype p] in
theorem riccatiMap_le_joseph [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} (hR : R.PosDef) (hP : SymPSD P) (K : Matrix m n ℝ) :
    LoewnerLE (riccatiMap A B Q R P) (lqrJosephUpdate P A B Q R K) := by
  intro x
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  rw [lqr_joseph_completion_of_squares (Q := Q) hP.1 hR'.1 (riccatiGain_normal_eq hR hP) K,
    quad_add, ← quad_mulVec_rect]
  unfold riccatiMap
  linarith [quad_nonneg_of_posDef (lqrHessian_posDef (B := B) hR hP)
    ((K - riccatiGain A B R P) *ᵥ x)]

/-! ### 1. Schur Stability, Stabilizability & Detectability Predicates -/

/-- A square matrix $M$ is Schur stable if every trajectory $M^k x$ converges to $0$ as
$k \to \infty$. -/
def IsSchurStable [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∀ x : n → ℝ, Tendsto (fun k : ℕ => (M ^ k) *ᵥ x) atTop (𝓝 0)

/-- The pair $(A, B)$ is stabilizable if there exists a state-feedback gain $K$ such that the
closed-loop matrix $A - B K$ is Schur stable. -/
def IsStabilizable [DecidableEq n] (A : Matrix n n ℝ) (B : Matrix n m ℝ) : Prop :=
  ∃ K : Matrix m n ℝ, IsSchurStable (lqrClosedLoop A B K)

/-- The pair $(A, C)$ is detectable if there exists an observer gain $L$ such that the
estimation error matrix $A - L C$ is Schur stable. -/
def IsDetectable [DecidableEq n] (A : Matrix n n ℝ) (C : Matrix p n ℝ) : Prop :=
  ∃ L : Matrix n p ℝ, IsSchurStable (A - L * C)

omit [Fintype n] [Fintype m] in
theorem lqrClosedLoop_dual (A : Matrix n n ℝ) (C : Matrix p n ℝ) (L : Matrix n p ℝ) :
    lqrClosedLoop Aᵀ Cᵀ Lᵀ = (A - L * C)ᵀ := by
  simp [lqrClosedLoop, transpose_sub, transpose_mul]

omit [Fintype m] [Fintype p] in
theorem schur_transpose [DecidableEq n] {M : Matrix n n ℝ}
    (h : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (M ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∀ x : n → ℝ, Tendsto (fun k : ℕ => (Mᵀ ^ k) *ᵥ x) atTop (𝓝 0) := by
  have hmat : Tendsto (fun k : ℕ => M ^ k) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h1 := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
    simpa [mulVec_single_one] using h1
  have hT : Tendsto (fun k : ℕ => (M ^ k)ᵀ) atTop (𝓝 0) := by
    simpa using tendsto_transpose hmat
  intro x
  have hcont : Continuous fun X : Matrix n n ℝ => X *ᵥ x :=
    continuous_id.matrix_mulVec continuous_const
  have h2 := (hcont.tendsto 0).comp hT
  simp only [zero_mulVec] at h2
  refine h2.congr fun k => ?_
  simp [Function.comp_apply, Matrix.transpose_pow]

omit [Fintype m] in
/-- **Control–Estimation Duality for Detectability**:
$(A, C)$ is detectable if and only if $(A^\top, C^\top)$ is stabilizable. -/
theorem isDetectable_iff_isStabilizable_dual [DecidableEq n]
    (A : Matrix n n ℝ) (C : Matrix p n ℝ) :
    IsDetectable A C ↔ IsStabilizable Aᵀ Cᵀ := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨Lᵀ, ?_⟩
    rw [IsSchurStable, lqrClosedLoop_dual]
    exact schur_transpose hL
  · rintro ⟨K, hK⟩
    refine ⟨Kᵀ, ?_⟩
    have hK' := schur_transpose hK
    have hdual : (lqrClosedLoop Aᵀ Cᵀ K)ᵀ = A - Kᵀ * C := by
      simp [lqrClosedLoop, transpose_sub, transpose_mul]
    rwa [hdual] at hK'

/-! ### 2. Factored State Weight $Q = C^\top C$ and Definite Quadratic Forms -/

omit [Fintype m] in
/-- Quadratic form of a factored weight $C^\top C$ equals the squared Euclidean dot product
$(C x) \cdot (C x)$. -/
theorem quad_transpose_mul_self (C : Matrix p n ℝ) (x : n → ℝ) :
    quad (Cᵀ * C) x = (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by
  simp only [quad, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [Fintype n] [Fintype m] in
/-- The Euclidean dot product of a real vector with itself is nonnegative. -/
theorem dotProduct_self_nonneg' (y : p → ℝ) : 0 ≤ y ⬝ᵥ y :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)

omit [Fintype n] [Fintype m] in
/-- The Euclidean dot product $y \cdot y$ vanishes if and only if $y = 0$. -/
theorem dotProduct_self_eq_zero_iff {y : p → ℝ} : y ⬝ᵥ y = 0 ↔ y = 0 := by
  constructor
  · intro h
    unfold dotProduct at h
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y i))).1 h
    ext i
    exact mul_self_eq_zero.1 (h0 i (Finset.mem_univ i))
  · rintro rfl
    simp

omit [Fintype n] [Fintype m] in
/-- For any nonzero vector $y \ne 0$, the Euclidean dot product $y \cdot y$ is strictly positive. -/
theorem dotProduct_self_pos_of_ne_zero {y : p → ℝ} (hy : y ≠ 0) : 0 < y ⬝ᵥ y :=
  lt_of_le_of_ne (dotProduct_self_nonneg' y) (Ne.symm (mt dotProduct_self_eq_zero_iff.1 hy))

omit [Fintype m] in
/-- For any output matrix $C$, the factored weight $C^\top C$ is symmetric positive semidefinite. -/
theorem symPSD_transpose_mul_self (C : Matrix p n ℝ) : SymPSD (Cᵀ * C) := by
  refine ⟨by simp [transpose_mul], fun x => ?_⟩
  rw [quad_transpose_mul_self]
  exact dotProduct_self_nonneg' (C *ᵥ x)

omit [Fintype n] [Fintype p] in
/-- For a positive definite matrix $R \succ 0$, $\operatorname{quad} R u = 0 \iff u = 0$. -/
theorem quad_eq_zero_iff_of_posDef {R : Matrix m m ℝ} (hR : R.PosDef) {u : m → ℝ} :
    quad R u = 0 ↔ u = 0 := by
  rw [posDef_iff_quad_pos] at hR
  constructor
  · intro h
    by_contra hu
    exact (hR.2 u hu).ne' h
  · rintro rfl
    simp [quad]

/-! ### 3. Fundamental DARE Dissipation Identities & Zero-Step Escape Lemma -/

/-- **Fundamental Joseph Closed-Loop Dissipation Identity** for $Q = C^\top C$:
If $P = \mathcal{R}_K(P)$ with $Q = C^\top C$, then along the closed-loop step
$A_K = A - B K$,
$$x^\top P x - (A_K x)^\top P (A_K x) = (C x) \cdot (C x) + (K x)^\top R (K x).$$ -/
theorem joseph_dissipation_factored {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B K *ᵥ x) =
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad R (K *ᵥ x) := by
  have h := quad_lqrJosephUpdate P A B (Cᵀ * C) R K x
  rw [hfix, quad_transpose_mul_self] at h
  linarith

/-- **Fundamental DARE Closed-Loop Dissipation Identity** for $Q = C^\top C$:
If $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$, then with optimal gain
$K = K(P)$ and $A_{\text{cl}} = A - B K$,
$$x^\top P x - (A_{\text{cl}} x)^\top P (A_{\text{cl}} x) =
  (C x) \cdot (C x) + (K x)^\top R (K x).$$ -/
theorem dare_dissipation_factored [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hfix : riccatiMap A B (Cᵀ * C) R P = P) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x) =
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad R (riccatiGain A B R P *ᵥ x) :=
  joseph_dissipation_factored hfix x

/-- **Open-Loop DARE Hessian Dissipation Identity** for $Q = C^\top C$:
If $R \succ 0$, $P \succeq 0$, and $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$,
then with $K = K(P)$,
$$(C x) \cdot (C x) + (A x)^\top P (A x) - x^\top P x =
  (K x)^\top (R + B^\top P B) (K x).$$ -/
theorem dare_openLoop_dissipation_factored [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : riccatiMap A B (Cᵀ * C) R P = P) (x : n → ℝ) :
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad P (A *ᵥ x) - quad P x =
      quad (lqrHessian P B R) (riccatiGain A B R P *ᵥ x) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hopt := lqrJosephUpdate_opt_eq (Q := Cᵀ * C) hP.1 hR'.1
    (riccatiGain_normal_eq (A := A) (B := B) hR hP)
  have hfix' : lqrJosephUpdate P A B (Cᵀ * C) R (riccatiGain A B R P) = P := hfix
  rw [hfix'] at hopt
  have hq := congr_arg (fun M => quad M x) hopt
  rw [quad_sub, quad_add, quad_transpose_mul_self, ← quad_mulVec, ← quad_mulVec_rect] at hq
  linarith

/-- **Zero-Step Escape Lemma** (Joseph form):
If $R \succ 0$, $P$ satisfies $P = \mathcal{R}_K(P)$ for $Q = C^\top C$, and a state $x$ has zero
one-step Lyapunov decrease ($(A_K x)^\top P (A_K x) = x^\top P x$), then:
1. $C x = 0$ (the state is invisible at the output),
2. $K x = 0$ (the feedback control is inactive),
3. $A_K x = A x$ (the closed-loop step coincides with the open-loop step),
4. $(A - L C) x = A_K x$ for every observer gain $L$ (the closed-loop step coincides with the
   observer error step). -/
theorem joseph_zero_dissipation_escape {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    {x : n → ℝ} (hzero : quad P (lqrClosedLoop A B K *ᵥ x) = quad P x) :
    C *ᵥ x = 0 ∧ K *ᵥ x = 0 ∧ lqrClosedLoop A B K *ᵥ x = A *ᵥ x ∧
      ∀ L : Matrix n p ℝ, (A - L * C) *ᵥ x = lqrClosedLoop A B K *ᵥ x := by
  have hdiss := joseph_dissipation_factored hfix x
  rw [hzero, sub_self] at hdiss
  have hC0 : 0 ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := dotProduct_self_nonneg' (C *ᵥ x)
  have hR0 : 0 ≤ quad R (K *ᵥ x) := quad_nonneg_of_posDef hR (K *ᵥ x)
  have hCeq : (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = 0 := by linarith
  have hReq : quad R (K *ᵥ x) = 0 := by linarith
  have hCx : C *ᵥ x = 0 := dotProduct_self_eq_zero_iff.1 hCeq
  have hKx : K *ᵥ x = 0 := (quad_eq_zero_iff_of_posDef hR).1 hReq
  have hAK : lqrClosedLoop A B K *ᵥ x = A *ᵥ x := by
    simp [lqrClosedLoop, sub_mulVec, ← mulVec_mulVec, hKx]
  refine ⟨hCx, hKx, hAK, fun L => ?_⟩
  rw [hAK, sub_mulVec, ← mulVec_mulVec, hCx, mulVec_zero, sub_zero]

/-- **Zero-Step Escape Lemma** (DARE form):
If $R \succ 0$, $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$, and
$(A_{\text{cl}} x)^\top P (A_{\text{cl}} x) = x^\top P x$, then $C x = 0$, $K(P) x = 0$,
$A_{\text{cl}} x = A x$, and $(A - L C) x = A_{\text{cl}} x$ for every observer gain $L$. -/
theorem dare_zero_dissipation_escape [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hfix : riccatiMap A B (Cᵀ * C) R P = P)
    {x : n → ℝ}
    (hzero : quad P (lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x) = quad P x) :
    C *ᵥ x = 0 ∧ riccatiGain A B R P *ᵥ x = 0 ∧
      lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x = A *ᵥ x ∧
      ∀ L : Matrix n p ℝ,
        (A - L * C) *ᵥ x = lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x :=
  joseph_zero_dissipation_escape hR hfix hzero

/-! ### 4. Converging-Input Converging-State & Schur Stability under Detectability -/

omit [Fintype m] [Fintype p] in
/-- If $A^k x \to 0$ for every $x$, then $\|A^N x\| \le \tfrac12 \|x\|$ for some $N \ge 1$. -/
theorem exists_pow_contraction [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : n → ℝ, ‖(A ^ N) *ᵥ x‖ ≤ (1 / 2) * ‖x‖ := by
  set c : ℕ → ℝ := fun k => ∑ i, ‖(A ^ k) *ᵥ Pi.single i 1‖
  have hc : Tendsto c atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset n)
      (fun i _ => (hA (Pi.single i 1)).norm)
    simpa only [norm_zero, Finset.sum_const_zero] using h
  have hbound : ∀ k (x : n → ℝ), ‖(A ^ k) *ᵥ x‖ ≤ c k * ‖x‖ := by
    intro k x
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [mulVec_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [mulVec_smul, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1 (hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨N₀ + 1, Nat.succ_pos _, fun x => ?_⟩
  exact (hbound _ x).trans (mul_le_mul_of_nonneg_right (hN₀ _ (by omega)).le (norm_nonneg _))

omit [Fintype m] [Fintype p] in
theorem norm_mulVec_le_colSum [DecidableEq n] (M : Matrix n n ℝ) (y : n → ℝ) :
    ‖M *ᵥ y‖ ≤ (∑ i, ‖M *ᵥ Pi.single i 1‖) * ‖y‖ := by
  conv_lhs => rw [pi_eq_sum_univ' y]
  rw [mulVec_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [mulVec_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (norm_nonneg _)

omit [Fintype n] [Fintype m] [Fintype p] in
theorem tendsto_zero_of_block_contraction {a b : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (ha : ∀ k, 0 ≤ a k) (hrec : ∀ k, a (k + N) ≤ (1 / 2) * a k + b k)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hb (ε / 4) (by positivity)
  have hbK : ∀ k ≥ K₀, b k ≤ ε / 4 := fun k hk => by
    have := hK₀ k hk
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have hiter : ∀ q k, K₀ ≤ k → a (k + q * N) ≤ (1 / 2) ^ q * a k + ε / 2 := by
    intro q
    induction q with
    | zero =>
      intro k _
      simp only [zero_mul, add_zero, pow_zero, one_mul, le_add_iff_nonneg_right]
      positivity
    | succ q ih =>
      intro k hk
      have h1 := hrec (k + q * N)
      have h2 := hbK (k + q * N) (by omega)
      have h3 := ih k hk
      rw [show k + (q + 1) * N = k + q * N + N by ring]
      calc a (k + q * N + N) ≤ (1 / 2) * a (k + q * N) + b (k + q * N) := h1
        _ ≤ (1 / 2) * ((1 / 2) ^ q * a k + ε / 2) + ε / 4 := by gcongr
        _ = (1 / 2) ^ (q + 1) * a k + ε / 2 := by ring
  set M : ℝ := ∑ r ∈ Finset.range N, a (K₀ + r)
  have hM : ∀ r < N, a (K₀ + r) ≤ M := fun r hr =>
    Finset.single_le_sum (fun j _ => ha (K₀ + j)) (Finset.mem_range.2 hr)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => ha (K₀ + j)
  obtain ⟨Q, hQ⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * (M + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨K₀ + Q * N + N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha t)]
  obtain ⟨q, r, hr, ht_eq⟩ : ∃ q r, r < N ∧ t = K₀ + r + q * N :=
    ⟨(t - K₀) / N, (t - K₀) % N, Nat.mod_lt _ hN, by
      have := Nat.mod_add_div (t - K₀) N
      rw [mul_comm] at this
      omega⟩
  have h1 : Q * N < (q + 1) * N := by
    rw [add_mul, one_mul]
    omega
  have hqQ : Q ≤ q := Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right h1)
  have hbound := hiter q (K₀ + r) (by omega)
  rw [← ht_eq] at hbound
  have hpow : (1 / 2 : ℝ) ^ q ≤ (1 / 2) ^ Q := pow_le_pow_of_le_one (by norm_num) (by norm_num) hqQ
  have hprod : (1 / 2 : ℝ) ^ q * a (K₀ + r) < ε / 2 := by
    calc (1 / 2 : ℝ) ^ q * a (K₀ + r) ≤ (1 / 2) ^ Q * (M + 1) :=
          mul_le_mul hpow (by linarith [hM r hr]) (ha _) (by positivity)
      _ < ε / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = ε / 2 := by field_simp
  linarith

omit [Fintype m] [Fintype p] in
theorem forced_block_expansion [DecidableEq n] {A : Matrix n n ℝ} {x d : ℕ → n → ℝ}
    (hx : ∀ k, x (k + 1) = A *ᵥ x k + d k) (k : ℕ) :
    ∀ i, x (k + i) = (A ^ i) *ᵥ x k + ∑ j ∈ Finset.range i, (A ^ (i - 1 - j)) *ᵥ d (k + j)
  | 0 => by simp
  | i + 1 => by
    rw [← add_assoc, hx, forced_block_expansion hx k i, mulVec_add, mulVec_mulVec, ← pow_succ',
      Finset.sum_range_succ, mulVec_sum, Finset.sum_congr rfl fun j hj => ?_]
    · simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mulVec]
      abel
    · rw [mulVec_mulVec, ← pow_succ']
      congr 2
      have := Finset.mem_range.1 hj
      omega

omit [Fintype m] [Fintype p] in
/-- **Converging-input converging-state**: if $A$ is Schur stable, $x_{k+1} = A x_k + d_k$ and
$d_k \to 0$, then $x_k \to 0$. -/
theorem tendsto_zero_of_schur_forced [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ y : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ y) atTop (𝓝 0))
    {x d : ℕ → n → ℝ} (hx : ∀ k, x (k + 1) = A *ᵥ x k + d k)
    (hd : Tendsto d atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨N, hNpos, hN⟩ := exists_pow_contraction hA
  set C : ℝ := ∑ r ∈ Finset.range N, ∑ i, ‖(A ^ r) *ᵥ Pi.single i 1‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcol : ∀ r < N, ∑ i, ‖(A ^ r) *ᵥ Pi.single (M := fun _ => ℝ) i 1‖ ≤ C := fun r hr =>
    Finset.single_le_sum (f := fun r => ∑ i, ‖(A ^ r) *ᵥ Pi.single (M := fun _ => ℝ) i 1‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_range.2 hr)
  set b : ℕ → ℝ := fun k => C * ∑ j ∈ Finset.range N, ‖d (k + j)‖
  have hrec : ∀ k, ‖x (k + N)‖ ≤ (1 / 2) * ‖x k‖ + b k := by
    intro k
    rw [forced_block_expansion hx k N]
    refine (norm_add_le _ _).trans (add_le_add (hN _) ?_)
    refine (norm_sum_le _ _).trans ?_
    change _ ≤ C * _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    refine (norm_mulVec_le_colSum _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hcol _ (by omega)) (norm_nonneg _)
  have hb : Tendsto b atTop (𝓝 0) := by
    have h : Tendsto (fun k => ∑ j ∈ Finset.range N, ‖d (k + j)‖) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range N) fun j _ =>
        ((tendsto_add_atTop_iff_nat j).2 hd).norm
      simpa only [norm_zero, Finset.sum_const_zero] using this
    simpa using h.const_mul C
  have ha := tendsto_zero_of_block_contraction hNpos (fun k => norm_nonneg (x k)) hrec hb
  exact tendsto_zero_iff_norm_tendsto_zero.2 ha

omit [Fintype n] [Fintype m] in
/-- If $M$ has strictly positive quadratic form on nonzero vectors and $\operatorname{quad} M (v_k)
\to 0$, then $v_k \to 0$. -/
theorem tendsto_zero_of_quad_tendsto_zero {M : Matrix p p ℝ}
    (hM : ∀ y ≠ 0, 0 < quad M y) {v : ℕ → p → ℝ}
    (hv : Tendsto (fun k => quad M (v k)) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  obtain ⟨c, hc, hcM⟩ := exists_quad_lower hM
  have hsq : Tendsto (fun k => ‖v k‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k => quad M (v k) / c) atTop (𝓝 0) := by
      simpa using hv.div_const c
    refine squeeze_zero (fun _ => by positivity) (fun k => ?_) hlim
    rw [le_div_iff₀ hc, mul_comm]
    exact hcM (v k)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

omit [Fintype n] [Fintype m] in
/-- If $(v_k) \cdot (v_k) \to 0$ as $k \to \infty$, then $v_k \to 0$. -/
theorem tendsto_zero_of_dotProduct_self_tendsto_zero {v : ℕ → p → ℝ}
    (hv : Tendsto (fun k => (v k) ⬝ᵥ (v k)) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  have hsq : Tendsto (fun k => (v k i) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => sq_nonneg _) (fun k => ?_) hv
    rw [sq]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v k j)) (Finset.mem_univ i)
  have h0 := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] at h0
  exact tendsto_zero_iff_norm_tendsto_zero.2 h0

/-- **Summability of Output & Control Energy along Closed-Loop Trajectories**:
If $R \succ 0$, $P \succeq 0$, and $P = \mathcal{R}_K(P)$ for $Q = C^\top C$, then along any
closed-loop trajectory $x_k = (A - B K)^k x_0$, the stage energy sequence
$(C x_k) \cdot (C x_k) + (K x_k)^\top R (K x_k)$ is summable. -/
theorem summable_dissipation_of_joseph [DecidableEq n] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    (x₀ : n → ℝ) :
    Summable (fun k : ℕ =>
      (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) +
        quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) := by
  refine summable_of_sum_range_le
    (fun k => add_nonneg (dotProduct_self_nonneg' _) (quad_nonneg_of_posDef hR _))
    (c := quad P x₀) fun N => ?_
  have htel : ∑ k ∈ Finset.range N,
      ((C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) +
        quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) =
      quad P x₀ - quad P ((lqrClosedLoop A B K ^ N) *ᵥ x₀) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        ← joseph_dissipation_factored hfix ((lqrClosedLoop A B K ^ N) *ᵥ x₀),
        mulVec_mulVec, ← pow_succ']
      ring
  rw [htel]
  linarith [hP.2 ((lqrClosedLoop A B K ^ N) *ᵥ x₀)]

/-- **Output-to-Zero & Control-to-Zero Convergence**:
Under the hypotheses of `summable_dissipation_of_joseph`, both the output sequence
$C (A - B K)^k x_0$ and the control sequence $K (A - B K)^k x_0$ converge to $0$ as
$k \to \infty$. -/
theorem tendsto_output_and_control_zero_of_joseph [DecidableEq n]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) atTop (𝓝 0) := by
  have hsum := (summable_dissipation_of_joseph hR hP hfix x₀).tendsto_atTop_zero
  have hC_sq : Tendsto (fun k : ℕ =>
      (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ
        (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dotProduct_self_nonneg' _)
      (fun k => le_add_of_nonneg_right (quad_nonneg_of_posDef hR _)) hsum
  have hK_sq : Tendsto (fun k : ℕ =>
      quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => quad_nonneg_of_posDef hR _)
      (fun k => le_add_of_nonneg_left (dotProduct_self_nonneg' _)) hsum
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  exact ⟨tendsto_zero_of_dotProduct_self_tendsto_zero hC_sq,
    tendsto_zero_of_quad_tendsto_zero hR'.2 hK_sq⟩

/-- **Forced Observer Decomposition of the Closed Loop**:
Every closed-loop step $x_{k+1} = (A - B K) x_k$ can be written as an observer error step
$(A - L C) x_k$ driven by the output-control perturbation $L (C x_k) - B (K x_k)$. -/
theorem closedLoop_eq_observer_add_forcing (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (C : Matrix p n ℝ) (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x : n → ℝ) :
    lqrClosedLoop A B K *ᵥ x =
      (A - L * C) *ᵥ x + (L *ᵥ (C *ᵥ x) - B *ᵥ (K *ᵥ x)) := by
  simp only [lqrClosedLoop, sub_mulVec, ← mulVec_mulVec]
  abel

/-- **Schur Stability of Any Joseph DARE Solution under Detectability**:
If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ satisfies the Joseph equation
$P = \mathcal{R}_K(P)$ for $Q = C^\top C$, then $A - B K$ is Schur stable. -/
theorem joseph_schur_of_detectable [DecidableEq n] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hdet : IsDetectable A C)
    (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P) :
    IsSchurStable (lqrClosedLoop A B K) := by
  obtain ⟨L, hL⟩ := hdet
  intro x₀
  set x : ℕ → n → ℝ := fun k => (lqrClosedLoop A B K ^ k) *ᵥ x₀
  obtain ⟨hCx, hKx⟩ := tendsto_output_and_control_zero_of_joseph hR hP hfix x₀
  have hLCx : Tendsto (fun k => L *ᵥ (C *ᵥ x k)) atTop (𝓝 0) := by
    have hcont : Continuous fun y : p → ℝ => L *ᵥ y :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp hCx
  have hBKx : Tendsto (fun k => B *ᵥ (K *ᵥ x k)) atTop (𝓝 0) := by
    have hcont : Continuous fun u : m → ℝ => B *ᵥ u :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp hKx
  have hd : Tendsto (fun k => L *ᵥ (C *ᵥ x k) - B *ᵥ (K *ᵥ x k)) atTop (𝓝 0) := by
    simpa using hLCx.sub hBKx
  have hstep : ∀ k, x (k + 1) = (A - L * C) *ᵥ x k + (L *ᵥ (C *ᵥ x k) - B *ᵥ (K *ᵥ x k)) := by
    intro k
    change (lqrClosedLoop A B K ^ (k + 1)) *ᵥ x₀ = _
    rw [pow_succ', ← mulVec_mulVec]
    exact closedLoop_eq_observer_add_forcing A B C K L (x k)
  exact tendsto_zero_of_schur_forced hL hstep hd

/-- **Headline Theorem 1 — Schur Stability of the DARE Solution under Detectability**:
If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ solves the DARE
$\mathcal{T}(P) = P$ for $Q = C^\top C$, then the optimal closed loop
$A_{\text{cl}} = A - B K(P)$ is Schur stable. -/
theorem dare_schur_of_detectable [DecidableEq n] [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hdet : IsDetectable A C)
    (hfix : riccatiMap A B (Cᵀ * C) R P = P) :
    IsSchurStable (lqrClosedLoop A B (riccatiGain A B R P)) :=
  joseph_schur_of_detectable hR hP hdet hfix

/-! ### 5. Uniqueness of the PSD DARE Solution under Detectability -/

omit [Fintype m] [Fintype p] in
theorem quad_add_sub_quad_sub {M : Matrix n n ℝ} (hM : Mᵀ = M) (u v : n → ℝ) :
    quad M (u + v) - quad M (u - v) = 4 * (u ⬝ᵥ (M *ᵥ v)) := by
  have hsw : v ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ v) := by
    rw [dotProduct_comm, mulVec_dotProduct_eq, hM]
  simp only [quad, mulVec_add, mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub,
    sub_dotProduct, hsw]
  ring

omit [Fintype m] [Fintype p] in
theorem entry_eq_polar [DecidableEq n] {M : Matrix n n ℝ} (hM : Mᵀ = M) (i j : n) :
    M i j = (quad M (Pi.single i 1 + Pi.single j 1) -
      quad M (Pi.single i 1 - Pi.single j 1)) / 4 := by
  rw [quad_add_sub_quad_sub hM]
  simp

/-- The matrix reconstructed from a limiting quadratic form by polarization. -/
noncomputable def polarMatrix [DecidableEq n] (q : (n → ℝ) → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1 - Pi.single j 1)) / 4

omit [Fintype m] [Fintype p] in
theorem tendsto_polarMatrix [DecidableEq n] {M : ℕ → Matrix n n ℝ} (hM : ∀ k, (M k)ᵀ = M k)
    {q : (n → ℝ) → ℝ} (hq : ∀ x, Tendsto (fun k => quad (M k) x) atTop (𝓝 (q x))) :
    Tendsto M atTop (𝓝 (polarMatrix q)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((hq (Pi.single i 1 + Pi.single j 1)).sub
    (hq (Pi.single i 1 - Pi.single j 1))).div_const 4
  refine h.congr fun k => ?_
  exact (entry_eq_polar (hM k) i j).symm

omit [Fintype m] [Fintype p] in
theorem norm_pow_mulVec_le [DecidableEq n] {A : Matrix n n ℝ} {N : ℕ}
    (hN : ∀ x : n → ℝ, ‖(A ^ N) *ᵥ x‖ ≤ (1 / 2) * ‖x‖) (x : n → ℝ) (r : ℕ) :
    ∀ q : ℕ, ‖(A ^ (q * N + r)) *ᵥ x‖ ≤ (1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖
  | 0 => by simp
  | q + 1 => by
    have h : A ^ ((q + 1) * N + r) = A ^ N * A ^ (q * N + r) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h, ← mulVec_mulVec, pow_succ]
    calc ‖(A ^ N) *ᵥ ((A ^ (q * N + r)) *ᵥ x)‖
        ≤ (1 / 2) * ‖(A ^ (q * N + r)) *ᵥ x‖ := hN _
      _ ≤ (1 / 2) * ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) :=
          mul_le_mul_of_nonneg_left (norm_pow_mulVec_le hN x r q) (by norm_num)
      _ = (1 / 2) ^ q * (1 / 2) * ‖(A ^ r) *ᵥ x‖ := by ring

omit [Fintype m] [Fintype p] in
theorem summable_quad_pow_mulVec [DecidableEq n] {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : ∀ v, 0 ≤ quad Q v) (x : n → ℝ) :
    Summable fun k => quad Q ((A ^ k) *ᵥ x) := by
  obtain ⟨N, hNpos, hN⟩ := exists_pow_contraction hA
  obtain ⟨C, hC, hCQ⟩ := exists_quad_upper Q
  set g : ℕ → ℝ := fun k => quad Q ((A ^ k) *ᵥ x)
  set M : ℝ := ∑ r ∈ Finset.range N, ‖(A ^ r) *ᵥ x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg0 : ∀ k, 0 ≤ g k := fun k => hQ _
  have hblock : ∀ q, ∑ r ∈ Finset.range N, g (q * N + r) ≤ C * M * (1 / 4) ^ q := by
    intro q
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    have h1 := norm_pow_mulVec_le hN x r q
    have h2 : ‖(A ^ (q * N + r)) *ᵥ x‖ ^ 2 ≤ ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc g (q * N + r) ≤ C * ‖(A ^ (q * N + r)) *ᵥ x‖ ^ 2 := hCQ _
      _ ≤ C * ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hC.le
      _ = C * ‖(A ^ r) *ᵥ x‖ ^ 2 * (1 / 4) ^ q := by
          rw [mul_pow, ← pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
          ring
  have hblocks : ∀ q, ∑ k ∈ Finset.range (q * N), g k ≤ C * M * (4 / 3) := by
    have hgeom : ∀ q, ∑ k ∈ Finset.range (q * N), g k ≤
        C * M * ∑ j ∈ Finset.range q, (1 / 4 : ℝ) ^ j := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [show (q + 1) * N = q * N + N by ring, Finset.sum_range_add, Finset.sum_range_succ,
          mul_add]
        exact add_le_add ih (hblock q)
    intro q
    refine (hgeom q).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le hM))
    have h := geom_sum_eq (show (1 / 4 : ℝ) ≠ 1 by norm_num) q
    rw [h]
    have hp : 0 ≤ (1 / 4 : ℝ) ^ q := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  refine summable_of_sum_range_le hg0 (c := C * M * (4 / 3)) fun k => ?_
  refine le_trans ?_ (hblocks k)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hg0 i
  exact Finset.range_subset_range.2 (Nat.le_mul_of_pos_right k hNpos)

omit [Fintype m] [Fintype p] in
theorem lyapunovSum_tendsto_of_schur [DecidableEq n] {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : SymPSD Q) :
    ∃ S : Matrix n n ℝ, Tendsto (lyapunovSum A Q) atTop (𝓝 S) := by
  refine ⟨polarMatrix fun x => ∑' k, quad Q ((A ^ k) *ᵥ x), ?_⟩
  refine tendsto_polarMatrix (fun N => lyapunovSum_transpose A Q hQ.1 N) fun x => ?_
  have h := (summable_quad_pow_mulVec hA hQ.2 x).hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  rw [quad_lyapunovSum]

omit [Fintype m] [Fintype p] in
theorem lyapunov_tail_tendsto_zero_of_schur [DecidableEq n] {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : Qᵀ = Q) :
    Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0) := by
  have h := tendsto_polarMatrix (q := fun _ => 0)
    (fun N => lyapunovTerm_transpose A Q hQ N) fun x => by
      have h0 := ((continuous_quad Q).tendsto 0).comp (hA x)
      simp only [quad, mulVec_zero, dotProduct_zero] at h0
      refine h0.congr fun N => ?_
      simp only [Function.comp_apply]
      exact (quad_lyapunovTerm A Q N x).symm
  have hzero : polarMatrix (n := n) (fun _ => 0) = 0 := by
    ext i j
    simp [polarMatrix]
  rwa [hzero] at h

omit [Fintype m] [Fintype p] in
/-- **Converse discrete Lyapunov theorem from Schur stability.** If $A^k x \to 0$ for every $x$
and $Q$ is symmetric PSD, then there is a symmetric PSD $S \succeq Q$ with $A^\top S A - S = -Q$. -/
theorem converse_lyapunov_of_schur [DecidableEq n] {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : SymPSD Q) :
    ∃ S : Matrix n n ℝ, SymPSD S ∧ Aᵀ * S * A - S = -Q ∧ LoewnerLE Q S := by
  obtain ⟨S, hS⟩ := lyapunovSum_tendsto_of_schur hA hQ
  obtain ⟨hstein, hsym, hdom⟩ := converse_lyapunov_of_tendsto_semidef A Q S hS
    (lyapunov_tail_tendsto_zero_of_schur hA hQ.1) hQ.1 hQ.2
  exact ⟨S, ⟨hsym, fun x => (hQ.2 x).trans (hdom x)⟩, hstein, hdom⟩

omit [Fintype m] [Fintype p] in
theorem eq_zero_of_quad_eq_zero {M : Matrix n n ℝ} (hM : Mᵀ = M)
    (h : ∀ x, quad M x = 0) : M = 0 := by
  classical
  ext i j
  rw [entry_eq_polar hM, h, h]
  simp

omit [Fintype m] [Fintype p] in
theorem LoewnerLE.antisymm {P P' : Matrix n n ℝ} (hP : Pᵀ = P) (hP' : P'ᵀ = P')
    (h₁ : LoewnerLE P P') (h₂ : LoewnerLE P' P) : P = P' := by
  have hD : (P - P')ᵀ = P - P' := by rw [transpose_sub, hP, hP']
  have h0 := eq_zero_of_quad_eq_zero hD fun x => by
    rw [quad_sub]
    linarith [h₁ x, h₂ x]
  exact sub_eq_zero.1 h0

omit [Fintype p] in
theorem dare_sub_le_closedLoop [DecidableEq m] {A Q : Matrix n n ℝ} {B : Matrix n m ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) {P P' : Matrix n n ℝ} (hP : SymPSD P)
    (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P') (x : n → ℝ) :
    quad P x - quad P' x ≤
      quad P (lqrClosedLoop A B (riccatiGain A B R P') *ᵥ x) -
        quad P' (lqrClosedLoop A B (riccatiGain A B R P') *ᵥ x) := by
  have h1 := riccatiMap_le_joseph (A := A) (B := B) (Q := Q) hR hP (riccatiGain A B R P') x
  rw [hfix, quad_lqrJosephUpdate] at h1
  have h2 : quad P' x = quad (lqrJosephUpdate P' A B Q R (riccatiGain A B R P')) x := by
    change quad P' x = quad (riccatiMap A B Q R P') x
    rw [hfix']
  rw [quad_lqrJosephUpdate] at h2
  linarith

omit [Fintype p] in
theorem dare_sub_le_closedLoop_pow [DecidableEq n] [DecidableEq m]
    {A Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) {P P' : Matrix n n ℝ}
    (hP : SymPSD P) (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P') :
    ∀ (k : ℕ) (x : n → ℝ), quad P x - quad P' x ≤
      quad P ((lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x) -
        quad P' ((lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x)
  | 0, x => by simp
  | k + 1, x => by
    refine (dare_sub_le_closedLoop hR hP hfix hfix' x).trans ?_
    have h := dare_sub_le_closedLoop_pow hR hP hfix hfix' k
      (lqrClosedLoop A B (riccatiGain A B R P') *ᵥ x)
    rwa [mulVec_mulVec, ← pow_succ] at h

omit [Fintype p] in
theorem dare_le_of_stabilizing [DecidableEq n] [DecidableEq m]
    {A Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) {P P' : Matrix n n ℝ}
    (hP : SymPSD P) (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P')
    (hstab : ∀ x : n → ℝ, Tendsto
      (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x) atTop (𝓝 0)) :
    LoewnerLE P P' := by
  intro x
  have hlim : Tendsto (fun k : ℕ =>
      quad P ((lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x) -
        quad P' ((lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x)) atTop
      (𝓝 (quad P 0 - quad P' 0)) :=
    (((continuous_quad P).tendsto 0).comp (hstab x)).sub
      (((continuous_quad P').tendsto 0).comp (hstab x))
  have hzero : quad P 0 - quad P' 0 = 0 := by simp [quad]
  rw [hzero] at hlim
  have h := ge_of_tendsto' hlim fun k => dare_sub_le_closedLoop_pow hR hP hfix hfix' k x
  linarith

omit [Fintype p] in
theorem dare_unique_of_stabilizing [DecidableEq n] [DecidableEq m]
    {A Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) {P P' : Matrix n n ℝ}
    (hP : SymPSD P) (hP' : SymPSD P')
    (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P')
    (hstab : ∀ x : n → ℝ, Tendsto
      (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x) atTop (𝓝 0))
    (hstab' : ∀ x : n → ℝ, Tendsto
      (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x) atTop (𝓝 0)) :
    P = P' :=
  LoewnerLE.antisymm hP.1 hP'.1 (dare_le_of_stabilizing hR hP hfix hfix' hstab')
    (dare_le_of_stabilizing hR hP' hfix' hfix hstab)

/-- **Headline Theorem 2 — Uniqueness of the PSD DARE Solution under Detectability**:
If $(A, C)$ is detectable and $R \succ 0$, the DARE for $Q = C^\top C$ has **at most one**
symmetric positive semidefinite solution. -/
theorem dare_unique_of_detectable [DecidableEq n] [DecidableEq m]
    {P P' A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hdet : IsDetectable A C)
    (hP : SymPSD P) (hP' : SymPSD P')
    (hfix : riccatiMap A B (Cᵀ * C) R P = P)
    (hfix' : riccatiMap A B (Cᵀ * C) R P' = P') :
    P = P' :=
  dare_unique_of_stabilizing hR hP hP' hfix hfix'
    (dare_schur_of_detectable hR hP hdet hfix)
    (dare_schur_of_detectable hR hP' hdet hfix')

/-! ### 6. LQR Return-Difference & Quadratic Gain-Margin Robustness Identities -/

omit [Fintype p] in
/-- **Perturbed Gain Joseph Matrix Identity**:
For any gain perturbation $\Delta K$ around a gain $K^*$ satisfying the LQR normal equation
$(R + B^\top P B) K^* = B^\top P A$,
$$\mathcal{R}_{K^* + \Delta K}(P) =
  \mathcal{R}_{K^*}(P) + (\Delta K)^\top (R + B^\top P B) (\Delta K).$$ -/
theorem lqr_perturbed_joseph_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) (ΔK : Matrix m n ℝ) :
    lqrJosephUpdate P A B Q R (Kstar + ΔK) =
      lqrJosephUpdate P A B Q R Kstar + ΔKᵀ * lqrHessian P B R * ΔK := by
  have h := lqr_joseph_completion_of_squares (Q := Q) hP hR hKstar (Kstar + ΔK)
  rwa [add_sub_cancel_left] at h

omit [Fintype p] in
/-- **Quadratic Form of the Perturbed Joseph Update**:
$$x^\top \mathcal{R}_{K^* + \Delta K}(P) x =
  x^\top \mathcal{R}_{K^*}(P) x + (\Delta K x)^\top (R + B^\top P B) (\Delta K x).$$ -/
theorem quad_lqr_perturbed_joseph {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    quad (lqrJosephUpdate P A B Q R (Kstar + ΔK)) x =
      quad (lqrJosephUpdate P A B Q R Kstar) x +
        quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  rw [lqr_perturbed_joseph_eq hP hR hKstar ΔK, quad_add, quad_mulVec_rect]

omit [Fintype p] in
/-- **Discrete-Time Bellman Return-Difference Identity**:
If $P = \mathcal{R}_{K^*}(P)$ solves the DARE with optimal gain $K^*$ satisfying
$(R + B^\top P B) K^* = B^\top P A$, then for every state $x$ and control input $u$,
$$\ell(x, u) + (A x + B u)^\top P (A x + B u) - x^\top P x =
  (u + K^* x)^\top (R + B^\top P B) (u + K^* x).$$ -/
theorem dare_bellman_return_difference {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (x : n → ℝ) (u : m → ℝ) :
    lqrStage Q R x u + quad P (A *ᵥ x + B *ᵥ u) - quad P x =
      quad (lqrHessian P B R) (u + Kstar *ᵥ x) := by
  unfold lqrStage
  have h := lqr_bellman_completion_of_squares (Q := Q) hP hR hKstar x u
  rw [hfix] at h
  linarith

omit [Fintype p] in
/-- **Headline Theorem 3 — Perturbed Closed-Loop Lyapunov Dissipation Identity**:
At a DARE solution $P = \mathcal{R}_{K^*}(P)$, the one-step Lyapunov decrease of $V(x) = x^\top P x$
along the perturbed closed loop $A_{K^* + \Delta K} = A - B (K^* + \Delta K)$ is given by
$$x^\top P x - (A_{K^* + \Delta K} x)^\top P (A_{K^* + \Delta K} x) =
  x^\top Q x + ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x) -
  (\Delta K x)^\top (R + B^\top P B) (\Delta K x).$$ -/
theorem dare_perturbed_lyapunov_dissipation {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) =
      quad Q x + quad R ((Kstar + ΔK) *ᵥ x) -
        quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  have h1 := quad_lqr_perturbed_joseph (Q := Q) hP hR hKstar ΔK x
  rw [hfix, quad_lqrJosephUpdate] at h1
  linarith

omit [Fintype p] in
/-- **Optimal Gain Dominance over Perturbed Gains**:
The optimal LQR gain $K^*$ dominates any perturbed gain $K^* + \Delta K$ in one-step net
Bellman dissipation (Lyapunov decrease minus stage cost) by the exact nonnegative quadratic
return-difference form $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \ge 0$. -/
theorem dare_optimal_dominates_perturbed_bellman {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : SymPSD P) (hR : R.PosDef)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    (quad P x - quad P (lqrClosedLoop A B Kstar *ᵥ x) -
        (quad Q x + quad R (Kstar *ᵥ x))) -
      (quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) -
        (quad Q x + quad R ((Kstar + ΔK) *ᵥ x))) =
      quad (lqrHessian P B R) (ΔK *ᵥ x) ∧
    0 ≤ quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hopt := quad_lqrJosephUpdate P A B Q R Kstar x
  rw [hfix] at hopt
  have hpert := dare_perturbed_lyapunov_dissipation hP.1 hR'.1 hKstar hfix ΔK x
  refine ⟨by linarith, quad_nonneg_of_posDef (lqrHessian_posDef hR hP) (ΔK *ᵥ x)⟩

omit [Fintype p] in
/-- **Quadratic Disk-Margin / Gain-Margin Robustness Theorem**:
If a gain perturbation $\Delta K$ satisfies the quadratic disk-margin inequality
$$(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \le
  ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x),$$
then the perturbed closed loop $A - B (K^* + \Delta K)$ still decreases the Lyapunov function
$V(x) = x^\top P x$ by at least the state cost $x^\top Q x$ at every step:
$$x^\top Q x \le x^\top P x - (A_{K^* + \Delta K} x)^\top P (A_{K^* + \Delta K} x).$$ -/
theorem dare_perturbed_dissipation_ge_of_margin {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    {ΔK : Matrix m n ℝ} {x : n → ℝ}
    (hmargin : quad (lqrHessian P B R) (ΔK *ᵥ x) ≤ quad R ((Kstar + ΔK) *ᵥ x)) :
    quad Q x ≤ quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) := by
  rw [dare_perturbed_lyapunov_dissipation hP hR hKstar hfix ΔK x]
  linarith

end ControlsLean.Controls
