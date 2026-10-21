/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.SchurLyapunov

/-!
# Uniqueness of the DARE Solution

This file completes the existence theory in `DAREExistence.lean` and `SchurLyapunov.lean` with
uniqueness.

- `dare_sub_le_closedLoop`: for two DARE solutions $P, P'$, the difference $D = P - P'$ satisfies
  $x^\top D x \le (A_{K'} x)^\top D (A_{K'} x)$, where $K' = K(P')$. This follows from the
  variational characterization of the Riccati map.
- `dare_le_of_stabilizing`: if the closed loop $A - BK(P')$ is Schur stable, then $P \preceq P'$
  for every PSD solution $P$. In words, the stabilizing solution is the *maximal* PSD solution.
- `dare_unique_of_stabilizing`: there is at most one stabilizing PSD solution.
- `dare_unique_of_posDef`: if $Q \succ 0$, every PSD solution is stabilizing, so the DARE has
  **exactly one** PSD solution, and it is the limit of Riccati value iteration.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology ControlsLean.Tactics

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
variable {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}

omit [Fintype m] [DecidableEq m] in
/-- A symmetric matrix whose quadratic form vanishes identically is zero. -/
theorem eq_zero_of_quad_eq_zero {M : Matrix n n ℝ} (hM : Mᵀ = M)
    (h : ∀ x, quad M x = 0) : M = 0 := by
  classical
  ext i j
  rw [entry_eq_polar hM, h, h]
  simp

omit [Fintype m] [DecidableEq m] in
/-- Two symmetric matrices that are mutually Loewner-dominated are equal. -/
theorem LoewnerLE.antisymm {P P' : Matrix n n ℝ} (hP : Pᵀ = P) (hP' : P'ᵀ = P')
    (h₁ : LoewnerLE P P') (h₂ : LoewnerLE P' P) : P = P' := by
  have hD : (P - P')ᵀ = P - P' := by rw [transpose_sub, hP, hP']
  have h0 := eq_zero_of_quad_eq_zero hD fun x => by
    rw [quad_sub]
    linarith [h₁ x, h₂ x]
  exact sub_eq_zero.1 h0

/-- **Comparison step**: for DARE solutions $P = \mathcal{T}(P)$ and $P' = \mathcal{T}(P')$, with
$P$ symmetric PSD, and $K' = K(P')$,
$x^\top (P - P') x \le (A_{K'} x)^\top (P - P') (A_{K'} x)$. -/
theorem dare_sub_le_closedLoop (hR : R.PosDef) {P P' : Matrix n n ℝ} (hP : SymPSD P)
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

/-- Iterating the comparison step along the closed loop of $P'$. -/
theorem dare_sub_le_closedLoop_pow [DecidableEq n] (hR : R.PosDef) {P P' : Matrix n n ℝ}
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

/-- **The stabilizing solution is maximal.** If $P'$ solves the DARE and its optimal closed loop
is Schur stable, then $P \preceq P'$ for every symmetric PSD solution $P$. -/
theorem dare_le_of_stabilizing [DecidableEq n] (hR : R.PosDef) {P P' : Matrix n n ℝ}
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

/-- **Uniqueness of the stabilizing DARE solution.** Two symmetric PSD solutions of the DARE whose
optimal closed loops are both Schur stable coincide. -/
theorem dare_unique_of_stabilizing [DecidableEq n] (hR : R.PosDef) {P P' : Matrix n n ℝ}
    (hP : SymPSD P) (hP' : SymPSD P')
    (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P')
    (hstab : ∀ x : n → ℝ, Tendsto
      (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x) atTop (𝓝 0))
    (hstab' : ∀ x : n → ℝ, Tendsto
      (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P') ^ k) *ᵥ x) atTop (𝓝 0)) :
    P = P' :=
  LoewnerLE.antisymm hP.1 hP'.1 (dare_le_of_stabilizing hR hP hfix hfix' hstab')
    (dare_le_of_stabilizing hR hP' hfix' hfix hstab)

/-- With $Q \succ 0$, every symmetric PSD DARE solution is stabilizing. -/
theorem dare_stabilizing_of_posDef [DecidableEq n] (hR : R.PosDef) (hQ : Q.PosDef)
    {P : Matrix n n ℝ} (hP : SymPSD P) (hfix : riccatiMap A B Q R P = P) (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀) atTop (𝓝 0) := by
  rw [posDef_iff_quad_pos] at hQ
  have hPpos : ∀ x ≠ 0, 0 < quad P x := fun x hx => by
    have h := quad_le_riccatiMap (A := A) (B := B) (Q := Q) hR hP x
    rw [hfix] at h
    exact (hQ.2 x hx).trans_le h
  refine dare_closedLoop_tendsto_zero hPpos hfix (fun x hx => ?_) x₀
  rw [quad_add, ← quad_mulVec_rect]
  exact add_pos_of_pos_of_nonneg (hQ.2 x hx) (quad_nonneg_of_posDef hR _)

/-- **Uniqueness of the DARE solution for $Q \succ 0$.** The DARE has at most one symmetric
positive semidefinite solution. -/
theorem dare_unique_of_posDef (hR : R.PosDef) (hQ : Q.PosDef)
    {P P' : Matrix n n ℝ} (hP : SymPSD P) (hP' : SymPSD P')
    (hfix : riccatiMap A B Q R P = P) (hfix' : riccatiMap A B Q R P' = P') : P = P' := by
  classical
  exact dare_unique_of_stabilizing hR hP hP' hfix hfix'
    (dare_stabilizing_of_posDef hR hQ hP hfix) (dare_stabilizing_of_posDef hR hQ hP' hfix')

/-- **Discrete-time LQR: existence and uniqueness.** If $R \succ 0$, $Q \succ 0$ and $(A, B)$ is
stabilizable, then the DARE has exactly one symmetric PSD solution $P$. That solution is positive
definite, it is the limit of Riccati value iteration from $0$, and its optimal gain is
stabilizing. -/
theorem lqr_existsUnique_of_stabilizable [DecidableEq n] (hR : R.PosDef) (hQ : Q.PosDef)
    (K₀ : Matrix m n ℝ)
    (hK₀ : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B K₀ ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ P : Matrix n n ℝ, (SymPSD P ∧ riccatiMap A B Q R P = P) ∧
      (∀ P', SymPSD P' ∧ riccatiMap A B Q R P' = P' → P' = P) ∧
      P.PosDef ∧ Tendsto (riccatiIter A B Q R) atTop (𝓝 P) ∧
      ∀ x₀ : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀)
        atTop (𝓝 0) := by
  obtain ⟨P, hPpd, hfix, hT, hstab⟩ := lqr_exists_of_stabilizable hR hQ K₀ hK₀
  have hP' := hPpd
  rw [posDef_iff_quad_pos] at hP'
  have hP : SymPSD P := ⟨hP'.1, fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [quad]
    · exact (hP'.2 x hx).le⟩
  exact ⟨P, ⟨hP, hfix⟩, fun P' ⟨hP'', hfix'⟩ => dare_unique_of_posDef hR hQ hP'' hP hfix' hfix,
    hPpd, hT, hstab⟩

end ControlsLean.Controls
