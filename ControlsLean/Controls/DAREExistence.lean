/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.LQR
import ControlsLean.Controls.ConverseLyapunov
import Mathlib.Topology.Instances.Matrix

/-!
# Existence of the Stabilizing DARE Solution via Riccati Value Iteration

`LQR.lean` shows that a solution of the discrete algebraic Riccati equation (DARE), if one exists,
makes the closed loop asymptotically stable. This file supplies the missing half: **existence**.

For the LTI system $x_{k+1} = A x_k + B u_k$ with stage cost $x^\top Q x + u^\top R u$,
$Q = Q^\top \succeq 0$ and $R \succ 0$, define the Riccati map
$$\mathcal{T}(P) = \mathcal{R}_{K(P)}(P), \qquad K(P) = (R + B^\top P B)^{-1} B^\top P A,$$
where $\mathcal{R}_K(P) = Q + K^\top R K + (A - BK)^\top P (A - BK)$ is the Joseph form.
Value iteration runs $P_0 = 0$, $P_{k+1} = \mathcal{T}(P_k)$.

## Main results

- `riccatiMap_le_joseph`: $\mathcal{T}(P) \preceq \mathcal{R}_K(P)$ for every gain $K$
  (variational characterization, from completion of squares).
- `riccatiMap_mono`: $\mathcal{T}$ is monotone in the Loewner order on symmetric PSD matrices.
- `riccatiIter_mono`, `riccatiIter_le_of_certificate`: value iteration is nondecreasing and is
  bounded above by any Lyapunov certificate of any stabilizing gain.
- `dare_exists_of_certificate`: the iterates converge to a symmetric PSD fixed point
  $P_\infty = \mathcal{T}(P_\infty)$, which is the **minimal** PSD solution (`dare_minimal`).
- `dare_standard_form`: $P_\infty$ solves the textbook DARE
  $P = Q + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$.
- `dare_stabilizing_of_certificate`: if moreover $Q \succ 0$, then $P_\infty \succ 0$ and the
  optimal closed loop $A - B K(P_\infty)$ is globally asymptotically stable.
- `certificate_of_converse_lyapunov`: the stabilizability hypothesis can be discharged by the
  converse Lyapunov limit of `ConverseLyapunov.lean`.

The stabilizability hypothesis is stated as a *Lyapunov certificate*: a gain $K_0$ and a symmetric
PSD $S$ with $\mathcal{R}_{K_0}(S) \preceq S$. Such an $S$ exists exactly when $A - B K_0$ is Schur
stable (take $S = \sum_k ((A - BK_0)^k)^\top (Q + K_0^\top R K_0) (A - BK_0)^k$).

## References

- D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. I, §4.1 (Riccati iteration).
- P. Lancaster, L. Rodman, *Algebraic Riccati Equations* (1995), Ch. 13.
- B. D. O. Anderson, J. B. Moore, *Optimal Filtering* (1979), App. E.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology ControlsLean.Tactics

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]

/-! ### 1. Loewner order, Riccati gain and Riccati map -/

/-- Loewner order expressed through quadratic forms: $P \preceq P'$. -/
def LoewnerLE (P P' : Matrix n n ℝ) : Prop := ∀ x : n → ℝ, quad P x ≤ quad P' x

omit [Fintype m] [DecidableEq m] in
theorem LoewnerLE.refl (P : Matrix n n ℝ) : LoewnerLE P P := fun _ => le_rfl

omit [Fintype m] [DecidableEq m] in
theorem LoewnerLE.trans {P P' P'' : Matrix n n ℝ} (h₁ : LoewnerLE P P') (h₂ : LoewnerLE P' P'') :
    LoewnerLE P P'' := fun x => (h₁ x).trans (h₂ x)

/-- Symmetric positive semidefinite, in quadratic-form language. -/
def SymPSD (P : Matrix n n ℝ) : Prop := Pᵀ = P ∧ ∀ x : n → ℝ, 0 ≤ quad P x

/-- The optimal Riccati gain $K(P) = (R + B^\top P B)^{-1} B^\top P A$. -/
noncomputable def riccatiGain (A : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ)
    (P : Matrix n n ℝ) : Matrix m n ℝ :=
  (lqrHessian P B R)⁻¹ * (Bᵀ * P * A)

/-- The Riccati map $\mathcal{T}(P) = \mathcal{R}_{K(P)}(P)$. -/
noncomputable def riccatiMap (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) : Matrix n n ℝ :=
  lqrJosephUpdate P A B Q R (riccatiGain A B R P)

/-- Riccati value iteration $P_0 = 0$, $P_{k+1} = \mathcal{T}(P_k)$. -/
noncomputable def riccatiIter (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) : ℕ → Matrix n n ℝ
  | 0 => 0
  | k + 1 => riccatiMap A B Q R (riccatiIter A B Q R k)

/-! ### 2. Quadratic form of the Joseph update -/

omit [DecidableEq m] in
/-- $x^\top \mathcal{R}_K(P) x = x^\top Q x + (Kx)^\top R (Kx) + ((A-BK)x)^\top P ((A-BK)x)$. -/
theorem quad_lqrJosephUpdate (P A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (K : Matrix m n ℝ) (x : n → ℝ) :
    quad (lqrJosephUpdate P A B Q R K) x =
      quad Q x + quad R (K *ᵥ x) + quad P (lqrClosedLoop A B K *ᵥ x) := by
  unfold lqrJosephUpdate
  rw [quad_add, quad_add, quad_mulVec_rect, quad_mulVec]

omit [DecidableEq m] in
/-- For a fixed gain, the Joseph update is monotone in $P$. -/
theorem lqrJosephUpdate_mono {P P' A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (K : Matrix m n ℝ) (h : LoewnerLE P P') :
    LoewnerLE (lqrJosephUpdate P A B Q R K) (lqrJosephUpdate P' A B Q R K) := by
  intro x
  rw [quad_lqrJosephUpdate, quad_lqrJosephUpdate]
  linarith [h (lqrClosedLoop A B K *ᵥ x)]

omit [DecidableEq m] in
/-- The Joseph update of a symmetric matrix is symmetric. -/
theorem lqrJosephUpdate_transpose {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (K : Matrix m n ℝ) (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hR : Rᵀ = R) :
    (lqrJosephUpdate P A B Q R K)ᵀ = lqrJosephUpdate P A B Q R K := by
  unfold lqrJosephUpdate
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hQ, hR, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- The Joseph update dominates the state cost:
$Q \preceq \mathcal{R}_K(P)$ when $R, P \succeq 0$. -/
theorem quad_le_lqrJosephUpdate {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (K : Matrix m n ℝ) (hR : ∀ v, 0 ≤ quad R v) (hP : ∀ x, 0 ≤ quad P x)
    (x : n → ℝ) : quad Q x ≤ quad (lqrJosephUpdate P A B Q R K) x := by
  rw [quad_lqrJosephUpdate]
  linarith [hR (K *ᵥ x), hP (lqrClosedLoop A B K *ᵥ x)]

/-! ### 3. The input Hessian is positive definite; the gain solves the normal equation -/

omit [DecidableEq m] in
theorem quad_lqrHessian (P : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ) (v : m → ℝ) :
    quad (lqrHessian P B R) v = quad R v + quad P (B *ᵥ v) := by
  unfold lqrHessian
  rw [quad_add, quad_mulVec_rect]

set_option linter.unusedFintypeInType false in
omit [DecidableEq m] in
/-- $R \succ 0$ and $P \succeq 0$ symmetric imply $R + B^\top P B \succ 0$. -/
theorem lqrHessian_posDef {P : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) : (lqrHessian P B R).PosDef := by
  rw [posDef_iff_quad_pos] at hR ⊢
  refine ⟨lqrHessian_transpose B hP.1 hR.1, fun v hv => ?_⟩
  rw [quad_lqrHessian]
  linarith [hR.2 v hv, hP.2 (B *ᵥ v)]

omit [DecidableEq m] in
theorem quad_nonneg_of_posDef {R : Matrix m m ℝ} (hR : R.PosDef) (v : m → ℝ) : 0 ≤ quad R v := by
  rw [posDef_iff_quad_pos] at hR
  rcases eq_or_ne v 0 with rfl | hv
  · simp [quad]
  · exact (hR.2 v hv).le

/-- The Riccati gain solves the LQR normal equation $(R + B^\top P B) K(P) = B^\top P A$. -/
theorem riccatiGain_normal_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) :
    lqrHessian P B R * riccatiGain A B R P = Bᵀ * P * A := by
  unfold riccatiGain
  have hdet : IsUnit (lqrHessian P B R).det := (lqrHessian_posDef hR hP).det_pos.ne'.isUnit
  exact mul_nonsing_inv_cancel_left _ _ hdet

/-! ### 4. Variational characterization and monotonicity of the Riccati map -/

/-- **Variational characterization**:
$\mathcal{T}(P) \preceq \mathcal{R}_K(P)$ for every gain $K$. -/
theorem riccatiMap_le_joseph {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) (hP : SymPSD P) (K : Matrix m n ℝ) :
    LoewnerLE (riccatiMap A B Q R P) (lqrJosephUpdate P A B Q R K) := by
  intro x
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  rw [lqr_joseph_completion_of_squares (Q := Q) hP.1 hR'.1 (riccatiGain_normal_eq hR hP) K,
    quad_add, ← quad_mulVec_rect]
  unfold riccatiMap
  linarith [quad_nonneg_of_posDef (lqrHessian_posDef (B := B) hR hP)
    ((K - riccatiGain A B R P) *ᵥ x)]

/-- The Riccati map preserves symmetric positive semidefiniteness. -/
theorem riccatiMap_symPSD {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) (hQ : SymPSD Q) (hP : SymPSD P) :
    SymPSD (riccatiMap A B Q R P) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  refine ⟨lqrJosephUpdate_transpose _ hP.1 hQ.1 hR'.1, fun x => ?_⟩
  exact (hQ.2 x).trans (quad_le_lqrJosephUpdate _ (quad_nonneg_of_posDef hR) hP.2 x)

/-- $Q \preceq \mathcal{T}(P)$. -/
theorem quad_le_riccatiMap {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) (hP : SymPSD P) (x : n → ℝ) :
    quad Q x ≤ quad (riccatiMap A B Q R P) x :=
  quad_le_lqrJosephUpdate _ (quad_nonneg_of_posDef hR) hP.2 x

/-- **Monotonicity of the Riccati map** in the Loewner order. -/
theorem riccatiMap_mono {P P' A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) (hP : SymPSD P) (h : LoewnerLE P P') :
    LoewnerLE (riccatiMap A B Q R P) (riccatiMap A B Q R P') :=
  (riccatiMap_le_joseph hR hP (riccatiGain A B R P')).trans (lqrJosephUpdate_mono _ h)

/-! ### 5. Value iteration: monotone and bounded by any stabilizing certificate -/

section Iteration

variable {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}

omit [Fintype m] [DecidableEq m] in
theorem symPSD_zero : SymPSD (0 : Matrix n n ℝ) := ⟨by simp, fun x => by simp [quad]⟩

omit [Fintype m] [DecidableEq m] in
theorem LoewnerLE.zero_left {S : Matrix n n ℝ} (hS : SymPSD S) : LoewnerLE 0 S := fun x => by
  simpa [quad] using hS.2 x

/-- Every Riccati iterate is symmetric positive semidefinite. -/
theorem riccatiIter_symPSD (hR : R.PosDef) (hQ : SymPSD Q) :
    ∀ k, SymPSD (riccatiIter A B Q R k)
  | 0 => symPSD_zero
  | k + 1 => riccatiMap_symPSD hR hQ (riccatiIter_symPSD hR hQ k)

/-- Value iteration from $P_0 = 0$ is nondecreasing: $P_k \preceq P_{k+1}$. -/
theorem riccatiIter_le_succ (hR : R.PosDef) (hQ : SymPSD Q) :
    ∀ k, LoewnerLE (riccatiIter A B Q R k) (riccatiIter A B Q R (k + 1))
  | 0 => LoewnerLE.zero_left (riccatiIter_symPSD hR hQ 1)
  | k + 1 => riccatiMap_mono hR (riccatiIter_symPSD hR hQ k) (riccatiIter_le_succ hR hQ k)

theorem riccatiIter_quad_monotone (hR : R.PosDef) (hQ : SymPSD Q) (x : n → ℝ) :
    Monotone fun k => quad (riccatiIter A B Q R k) x :=
  monotone_nat_of_le_succ fun k => riccatiIter_le_succ hR hQ k x

/-- **Upper bound**: if $K_0$ admits a Lyapunov certificate $\mathcal{R}_{K_0}(S) \preceq S$ with
$S \succeq 0$, every Riccati iterate satisfies $P_k \preceq S$. -/
theorem riccatiIter_le_of_certificate (hR : R.PosDef) (hQ : SymPSD Q) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ} (hS : SymPSD S) (hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S) :
    ∀ k, LoewnerLE (riccatiIter A B Q R k) S
  | 0 => LoewnerLE.zero_left hS
  | k + 1 =>
    (riccatiMap_le_joseph hR (riccatiIter_symPSD hR hQ k) K₀).trans
      ((lqrJosephUpdate_mono K₀ (riccatiIter_le_of_certificate hR hQ K₀ hS hcert k)).trans hcert)

/-- Every PSD solution of the DARE dominates every Riccati iterate. -/
theorem riccatiIter_le_of_fixed (hR : R.PosDef) (hQ : SymPSD Q) {P : Matrix n n ℝ}
    (hP : SymPSD P) (hfix : riccatiMap A B Q R P = P) :
    ∀ k, LoewnerLE (riccatiIter A B Q R k) P
  | 0 => LoewnerLE.zero_left hP
  | k + 1 => by
    have h := riccatiMap_mono (A := A) (B := B) (Q := Q) hR (riccatiIter_symPSD hR hQ k)
      (riccatiIter_le_of_fixed hR hQ hP hfix k)
    rwa [hfix] at h

end Iteration

/-! ### 6. Polarization: convergence of quadratic forms gives convergence of matrices -/

section Polarization

variable [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Polarization identity for symmetric matrices. -/
theorem quad_add_sub_quad_sub {M : Matrix n n ℝ} (hM : Mᵀ = M) (u v : n → ℝ) :
    quad M (u + v) - quad M (u - v) = 4 * (u ⬝ᵥ (M *ᵥ v)) := by
  have hsw : v ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ v) := by
    rw [dotProduct_comm, mulVec_dotProduct_eq, hM]
  simp only [quad, mulVec_add, mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub,
    sub_dotProduct, hsw]
  ring

omit [Fintype m] [DecidableEq m] in
theorem entry_eq_polar {M : Matrix n n ℝ} (hM : Mᵀ = M) (i j : n) :
    M i j = (quad M (Pi.single i 1 + Pi.single j 1) -
      quad M (Pi.single i 1 - Pi.single j 1)) / 4 := by
  rw [quad_add_sub_quad_sub hM]
  simp

/-- The matrix reconstructed from a limiting quadratic form by polarization. -/
noncomputable def polarMatrix (q : (n → ℝ) → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1 - Pi.single j 1)) / 4

omit [Fintype m] [DecidableEq m] in
/-- If symmetric matrices have pointwise convergent quadratic forms, the matrices converge. -/
theorem tendsto_polarMatrix {M : ℕ → Matrix n n ℝ} (hM : ∀ k, (M k)ᵀ = M k)
    {q : (n → ℝ) → ℝ} (hq : ∀ x, Tendsto (fun k => quad (M k) x) atTop (𝓝 (q x))) :
    Tendsto M atTop (𝓝 (polarMatrix q)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := ((hq (Pi.single i 1 + Pi.single j 1)).sub
    (hq (Pi.single i 1 - Pi.single j 1))).div_const 4
  refine h.congr fun k => ?_
  exact (entry_eq_polar (hM k) i j).symm

end Polarization

/-! ### 7. Continuity of the Riccati map -/

omit [Fintype m] [DecidableEq m] in
theorem continuous_lqrHessian (B : Matrix n m ℝ) (R : Matrix m m ℝ) :
    Continuous fun P : Matrix n n ℝ => lqrHessian P B R := by
  unfold lqrHessian
  fun_prop

/-- The Riccati map is continuous at every symmetric PSD matrix
(where the Hessian is invertible). -/
theorem riccatiMap_continuousAt {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hR : R.PosDef) {P : Matrix n n ℝ} (hP : SymPSD P) :
    ContinuousAt (riccatiMap A B Q R) P := by
  have hdet : (lqrHessian P B R).det ≠ 0 := (lqrHessian_posDef hR hP).det_pos.ne'
  have hinvAt : ContinuousAt Inv.inv (lqrHessian P B R) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hinv : ContinuousAt (fun P : Matrix n n ℝ => (lqrHessian P B R)⁻¹) P :=
    hinvAt.comp (f := fun P : Matrix n n ℝ => lqrHessian P B R)
      (continuous_lqrHessian B R).continuousAt
  -- Factor the map through `P ↦ (P, (R + Bᵀ P B)⁻¹)`; the outer map is polynomial.
  have hF : Continuous fun p : Matrix n n ℝ × Matrix m m ℝ =>
      lqrJosephUpdate p.1 A B Q R (p.2 * (Bᵀ * p.1 * A)) := by
    unfold lqrJosephUpdate lqrClosedLoop
    fun_prop
  have hfac : riccatiMap A B Q R = (fun p : Matrix n n ℝ × Matrix m m ℝ =>
      lqrJosephUpdate p.1 A B Q R (p.2 * (Bᵀ * p.1 * A))) ∘
        (fun P => (P, (lqrHessian P B R)⁻¹)) := rfl
  rw [hfac]
  exact hF.continuousAt.comp (continuousAt_id.prodMk hinv)

/-! ### 8. Existence, minimality and the standard form of the DARE -/

section Existence

variable {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
  [DecidableEq n]

omit [DecidableEq n] in
/-- **Existence of the minimal DARE solution** (Riccati value iteration).

If $R \succ 0$, $Q = Q^\top \succeq 0$, and some gain $K_0$ admits a PSD Lyapunov certificate
$\mathcal{R}_{K_0}(S) \preceq S$, then the Riccati iterates $P_k$ converge to a symmetric PSD
matrix $P_\infty$ with $\mathcal{T}(P_\infty) = P_\infty$, $P_k \preceq P_\infty \preceq S$, and
$P_\infty \preceq P'$ for every PSD solution $P'$ of the DARE. -/
theorem dare_exists_of_certificate (hR : R.PosDef) (hQ : SymPSD Q) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ} (hS : SymPSD S) (hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S) :
    ∃ P : Matrix n n ℝ,
      Tendsto (riccatiIter A B Q R) atTop (𝓝 P) ∧
      riccatiMap A B Q R P = P ∧
      SymPSD P ∧
      (∀ k, LoewnerLE (riccatiIter A B Q R k) P) ∧
      LoewnerLE P S ∧
      (∀ P' : Matrix n n ℝ, SymPSD P' → riccatiMap A B Q R P' = P' → LoewnerLE P P') := by
  classical
  set q : (n → ℝ) → ℝ := fun x => ⨆ k, quad (riccatiIter A B Q R k) x with hq_def
  have hbdd : ∀ x, BddAbove (Set.range fun k => quad (riccatiIter A B Q R k) x) := fun x =>
    ⟨quad S x, by
      rintro _ ⟨k, rfl⟩
      exact riccatiIter_le_of_certificate hR hQ K₀ hS hcert k x⟩
  have hq : ∀ x, Tendsto (fun k => quad (riccatiIter A B Q R k) x) atTop (𝓝 (q x)) := fun x =>
    tendsto_atTop_ciSup (riccatiIter_quad_monotone hR hQ x) (hbdd x)
  have hT : Tendsto (riccatiIter A B Q R) atTop (𝓝 (polarMatrix q)) :=
    tendsto_polarMatrix (fun k => (riccatiIter_symPSD hR hQ k).1) hq
  set P := polarMatrix q
  -- quadratic form of the limit
  have hquadP : ∀ x, quad P x = q x := fun x =>
    tendsto_nhds_unique (tendsto_quad_of_tendsto hT x) (hq x)
  have hPsym : Pᵀ = P := by
    have h1 := tendsto_transpose hT
    have h_eq : (fun k => (riccatiIter A B Q R k)ᵀ) = riccatiIter A B Q R := by
      funext k
      exact (riccatiIter_symPSD hR hQ k).1
    rw [h_eq] at h1
    exact tendsto_nhds_unique h1 hT
  have hle : ∀ k, LoewnerLE (riccatiIter A B Q R k) P := fun k x => by
    rw [hquadP]
    exact (riccatiIter_quad_monotone hR hQ x).ge_of_tendsto (hq x) k
  have hPpsd : SymPSD P := ⟨hPsym, fun x => by
    have := hle 0 x
    simpa [riccatiIter, quad] using this⟩
  have hfix : riccatiMap A B Q R P = P := by
    have h1 : Tendsto (fun k => riccatiMap A B Q R (riccatiIter A B Q R k)) atTop
        (𝓝 (riccatiMap A B Q R P)) :=
      (riccatiMap_continuousAt hR hPpsd).tendsto.comp hT
    have h2 : Tendsto (fun k => riccatiIter A B Q R (k + 1)) atTop (𝓝 P) :=
      (tendsto_add_atTop_iff_nat 1).2 hT
    exact tendsto_nhds_unique h1 h2
  refine ⟨P, hT, hfix, hPpsd, hle, ?_, ?_⟩
  · intro x
    rw [hquadP]
    exact ciSup_le fun k => riccatiIter_le_of_certificate hR hQ K₀ hS hcert k x
  · intro P' hP' hfix' x
    rw [hquadP]
    exact ciSup_le fun k => riccatiIter_le_of_fixed hR hQ hP' hfix' k x

omit [DecidableEq n] in
/-- **Standard form of the DARE**: for symmetric PSD $P$,
$\mathcal{T}(P) = Q + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$. -/
theorem riccatiMap_standard_form (hR : R.PosDef) {P : Matrix n n ℝ} (hP : SymPSD P) :
    riccatiMap A B Q R P =
      Q + Aᵀ * P * A - Aᵀ * P * B * (lqrHessian P B R)⁻¹ * (Bᵀ * P * A) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hnorm := riccatiGain_normal_eq (A := A) (B := B) hR hP
  have hGsym : (lqrHessian P B R)ᵀ = lqrHessian P B R := lqrHessian_transpose B hP.1 hR'.1
  unfold riccatiMap
  rw [lqrJosephUpdate_opt_eq hP.1 hR'.1 hnorm, Matrix.mul_assoc _ _ (riccatiGain A B R P), hnorm]
  congr 1
  unfold riccatiGain
  rw [transpose_mul, transpose_nonsing_inv, hGsym]
  simp only [transpose_mul, transpose_transpose, hP.1, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- **The minimal DARE solution in textbook form.** Under the hypotheses of
`dare_exists_of_certificate`, there is a symmetric PSD $P$ with
$P = Q + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$. -/
theorem dare_standard_form (hR : R.PosDef) (hQ : SymPSD Q) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ} (hS : SymPSD S) (hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S) :
    ∃ P : Matrix n n ℝ, SymPSD P ∧
      P = Q + Aᵀ * P * A - Aᵀ * P * B * (lqrHessian P B R)⁻¹ * (Bᵀ * P * A) := by
  obtain ⟨P, -, hfix, hP, -⟩ := dare_exists_of_certificate hR hQ K₀ hS hcert
  exact ⟨P, hP, by rw [← riccatiMap_standard_form hR hP, hfix]⟩

/-- **LQR existence and stability.** If $R \succ 0$, $Q \succ 0$, and some gain $K_0$ admits a PSD
Lyapunov certificate, then the DARE has a positive definite solution $P$, and the optimal
feedback $u = -K(P) x$ makes the closed loop $x_{k+1} = (A - B K(P)) x_k$ globally
asymptotically stable. -/
theorem dare_stabilizing_of_certificate (hR : R.PosDef) (hQ : Q.PosDef) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ} (hS : SymPSD S) (hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ riccatiMap A B Q R P = P ∧
      ∀ x₀ : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀)
        atTop (𝓝 0) := by
  have hQ' := hQ
  rw [posDef_iff_quad_pos] at hQ'
  have hQpsd : SymPSD Q := ⟨hQ'.1, quad_nonneg_of_posDef hQ⟩
  obtain ⟨P, -, hfix, hP, -⟩ := dare_exists_of_certificate hR hQpsd K₀ hS hcert
  have hPpos : ∀ x ≠ 0, 0 < quad P x := fun x hx => by
    have h := quad_le_riccatiMap (A := A) (B := B) (Q := Q) hR hP x
    rw [hfix] at h
    exact (hQ'.2 x hx).trans_le h
  refine ⟨P, (posDef_iff_quad_pos P).2 ⟨hP.1, hPpos⟩, hfix, fun x₀ => ?_⟩
  refine dare_closedLoop_tendsto_zero hPpos hfix (fun x hx => ?_) x₀
  rw [quad_add, ← quad_mulVec_rect]
  exact add_pos_of_pos_of_nonneg (hQ'.2 x hx) (quad_nonneg_of_posDef hR _)

omit [DecidableEq m] in
/-- **Discharging the certificate by converse Lyapunov.** If for some gain $K_0$ the closed-loop
Lyapunov sums $\sum_{k<N} ((A-BK_0)^k)^\top (Q + K_0^\top R K_0)(A-BK_0)^k$ converge to $S$ and the
tail terms vanish (as they do whenever $A - BK_0$ is Schur stable), then $S$ is a PSD Lyapunov
certificate for $K_0$, with equality $\mathcal{R}_{K_0}(S) = S$. -/
theorem certificate_of_converse_lyapunov (hR : R.PosDef) (hQ : SymPSD Q) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ}
    (hS : Tendsto (lyapunovSum (lqrClosedLoop A B K₀) (Q + K₀ᵀ * R * K₀)) atTop (𝓝 S))
    (htail : Tendsto (fun N => (lqrClosedLoop A B K₀ ^ N)ᵀ * (Q + K₀ᵀ * R * K₀) *
      (lqrClosedLoop A B K₀ ^ N)) atTop (𝓝 0)) :
    SymPSD S ∧ lqrJosephUpdate S A B Q R K₀ = S := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hQk_symm : (Q + K₀ᵀ * R * K₀)ᵀ = Q + K₀ᵀ * R * K₀ := by
    simp only [transpose_add, transpose_mul, transpose_transpose, hQ.1, hR'.1, Matrix.mul_assoc]
  have hQk_nonneg : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ ((Q + K₀ᵀ * R * K₀) *ᵥ v) := fun v => by
    change 0 ≤ quad (Q + K₀ᵀ * R * K₀) v
    rw [quad_add, ← quad_mulVec_rect]
    exact add_nonneg (hQ.2 v) (quad_nonneg_of_posDef hR _)
  obtain ⟨hstein, hSsym, hdom⟩ :=
    converse_lyapunov_of_tendsto_semidef _ _ S hS htail hQk_symm hQk_nonneg
  refine ⟨⟨hSsym, fun x => (hQk_nonneg x).trans (hdom x)⟩, ?_⟩
  have h2 : (lqrClosedLoop A B K₀)ᵀ * S * lqrClosedLoop A B K₀ = S - (Q + K₀ᵀ * R * K₀) := by
    calc (lqrClosedLoop A B K₀)ᵀ * S * lqrClosedLoop A B K₀
        = ((lqrClosedLoop A B K₀)ᵀ * S * lqrClosedLoop A B K₀ - S) + S := by abel
      _ = -(Q + K₀ᵀ * R * K₀) + S := by rw [hstein]
      _ = S - (Q + K₀ᵀ * R * K₀) := by abel
  unfold lqrJosephUpdate
  rw [h2]
  abel

/-- **LQR from a stabilizing gain** (end-to-end). If $R \succ 0$, $Q \succ 0$ and some gain $K_0$
has convergent closed-loop Lyapunov sums with vanishing tail, then value iteration converges to a
positive definite DARE solution whose optimal gain stabilizes the system. -/
theorem lqr_stabilizing_of_stabilizable (hR : R.PosDef) (hQ : Q.PosDef) (K₀ : Matrix m n ℝ)
    {S : Matrix n n ℝ}
    (hS : Tendsto (lyapunovSum (lqrClosedLoop A B K₀) (Q + K₀ᵀ * R * K₀)) atTop (𝓝 S))
    (htail : Tendsto (fun N => (lqrClosedLoop A B K₀ ^ N)ᵀ * (Q + K₀ᵀ * R * K₀) *
      (lqrClosedLoop A B K₀ ^ N)) atTop (𝓝 0)) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ riccatiMap A B Q R P = P ∧
      ∀ x₀ : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀)
        atTop (𝓝 0) := by
  have hQ' := hQ
  rw [posDef_iff_quad_pos] at hQ'
  obtain ⟨hSpsd, hSeq⟩ :=
    certificate_of_converse_lyapunov hR ⟨hQ'.1, quad_nonneg_of_posDef hQ⟩ K₀ hS htail
  exact dare_stabilizing_of_certificate hR hQ K₀ hSpsd (by rw [hSeq]; exact LoewnerLE.refl S)

end Existence

end ControlsLean.Controls
