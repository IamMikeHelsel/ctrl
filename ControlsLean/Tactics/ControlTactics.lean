/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import ControlsLean.Controls.DiscreteLyapunov

/-!
# Reusable Tactics and Helper Lemmas for Control Engineering

This module provides dedicated lemmas, macros, and tactics for control engineering
and applied mathematics formalization in Lean 4:

1. **Quadratic Form Simplification & Matrix.PosDef Conversions**:
   - Reductions for quadratic forms `x ⬝ᵥ (M *ᵥ x)` and `quad M x` across block matrices
     (`fromBlocks`, block diagonal, symmetric blocks).
   - Transpose and symmetry identities (invariance under transpose, vanishing of skew-symmetric
     quadratic forms, projection onto the symmetric part).
   - Rectangular and feedback transformations `quad M (K *ᵥ x) = quad (Kᵀ * M * K) x` and
     LQR stage-cost identities.
   - Bidirectional characterization and conversion between `Matrix.PosDef` / `Matrix.PosSemidef`
     and strict positivity / nonnegativity of `quad M x`.

2. **Linear Fractional Transformations & Algebraic Riccati Normalization**:
   - The parallel sum / precision inversion identity `(P * R / (P + R))⁻¹ = P⁻¹ + R⁻¹`.
   - Normalization of algebraic Riccati expressions to linear fractional (Möbius) form
     `((R + Q) * P + Q * R) / (P + R)`.
   - Invariance and noise cancellation in precision coordinates.
   - Reduction of the algebraic Riccati fixed-point equation to quadratic root conditions.

3. **Discrete Lyapunov Stability**:
   - Geometric contraction chaining: `V (f x) ≤ ρ * V x` implies
     `V (f^[k] x₀) ≤ ρ^k * V x₀`.
   - Generalization to linear dynamics `V ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * V x₀` and quadratic
     Lyapunov functions `quad P ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * quad P x₀`.
   - Dissipation rate conversions and discrete-time Lyapunov difference identities.

4. **Macros and Automation**:
   - `quad_simp`: simplifies block quadratic forms, transpose symmetries, and transformations.
   - `riccati_lft_norm`: normalizes Riccati and linear fractional expressions.
   - `lyapunov_step_simp`: expands discrete Lyapunov step differences.
   - `posdef_to_quad` / `possemidef_to_quad`: rewrites between matrix definiteness and
     quadratic forms.
-/

namespace ControlsLean.Tactics

open Matrix ControlsLean.Controls

-- Re-export core quadratic form definitions from ControlsLean.Controls
export ControlsLean.Controls (quad quad_smul continuous_quad quad_mulVec quad_sub)

/-! ### 1. Quadratic Form Symmetries, Block Reductions & PosDef Conversions -/

/-- Definitional equivalence between `quad` and `dotProduct`. -/
theorem quad_def {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad M x = x ⬝ᵥ (M *ᵥ x) := rfl

/-- Definitional equivalence between `dotProduct` and `quad`. -/
theorem dotProduct_mulVec_eq_quad {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = quad M x := rfl

/-- For real matrices, Hermitian symmetry is equivalent to transpose symmetry. -/
theorem isHermitian_iff_transpose_eq {n : Type*} (M : Matrix n n ℝ) :
    M.IsHermitian ↔ Mᵀ = M := by
  constructor
  · intro h
    ext i j
    have := congr_fun (congr_fun h i) j
    simpa [conjTranspose] using this
  · intro h
    ext i j
    simp [conjTranspose, h]

/-- Conversion: `M.PosDef` is equivalent to symmetry `Mᵀ = M` and positivity `0 < quad M x`
for all non-zero vectors. -/
theorem posDef_iff_quad_pos {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    M.PosDef ↔ Mᵀ = M ∧ ∀ x : n → ℝ, x ≠ 0 → 0 < quad M x := by
  rw [posDef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp [quad]

/-- Conversion: `M.PosDef` in terms of explicit `dotProduct`. -/
theorem posDef_iff_dotProduct_pos {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    M.PosDef ↔ Mᵀ = M ∧ ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
  rw [posDef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp

/-- Conversion: `M.PosSemidef` is equivalent to symmetry `Mᵀ = M` and nonnegativity
`0 ≤ quad M x`. -/
theorem posSemidef_iff_quad_nonneg {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x : n → ℝ, 0 ≤ quad M x := by
  rw [posSemidef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp [quad]

/-- Conversion: `M.PosSemidef` in terms of explicit `dotProduct`. -/
theorem posSemidef_iff_dotProduct_nonneg {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp

/-- If `M` is positive definite, its quadratic form is strictly positive on non-zero vectors. -/
theorem PosDef.quad_pos {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (hM : M.PosDef) {x : n → ℝ} (hx : x ≠ 0) : 0 < quad M x :=
  (posDef_iff_quad_pos M).1 hM |>.2 x hx

/-- Construct positive definiteness from symmetry and positivity of `quad M x`. -/
theorem PosDef.of_quad_pos {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (h_symm : Mᵀ = M) (h_pos : ∀ x : n → ℝ, x ≠ 0 → 0 < quad M x) : M.PosDef :=
  (posDef_iff_quad_pos M).2 ⟨h_symm, h_pos⟩

/-- If `M` is positive semidefinite, its quadratic form is non-negative everywhere. -/
theorem PosSemidef.quad_nonneg {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (x : n → ℝ) : 0 ≤ quad M x :=
  (posSemidef_iff_quad_nonneg M).1 hM |>.2 x

/-- Construct positive semidefiniteness from symmetry and non-negativity of `quad M x`. -/
theorem PosSemidef.of_quad_nonneg {n : Type*} [Fintype n] {M : Matrix n n ℝ}
    (h_symm : Mᵀ = M) (h_nonneg : ∀ x : n → ℝ, 0 ≤ quad M x) : M.PosSemidef :=
  (posSemidef_iff_quad_nonneg M).2 ⟨h_symm, h_nonneg⟩

/-! ### Quadratic Forms on Block Matrices and Transpose Relations -/

/-- Reduction of quadratic forms with general 2×2 block matrices. -/
theorem dotProduct_fromBlocks_mulVec {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (B : Matrix l m ℝ) (C : Matrix m l ℝ) (D : Matrix m m ℝ)
    (u : l → ℝ) (v : m → ℝ) :
    Sum.elim u v ⬝ᵥ (fromBlocks A B C D *ᵥ Sum.elim u v) =
      u ⬝ᵥ (A *ᵥ u) + u ⬝ᵥ (B *ᵥ v) + v ⬝ᵥ (C *ᵥ u) + v ⬝ᵥ (D *ᵥ v) := by
  simp only [fromBlocks_mulVec, sumElim_dotProduct_sumElim,
    Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
  ring

/-- Reduction of quadratic forms with block diagonal matrices. -/
theorem dotProduct_fromBlocks_diag_mulVec {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (D : Matrix m m ℝ) (u : l → ℝ) (v : m → ℝ) :
    Sum.elim u v ⬝ᵥ (fromBlocks A 0 0 D *ᵥ Sum.elim u v) =
      u ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (D *ᵥ v) := by
  rw [dotProduct_fromBlocks_mulVec]
  simp [dotProduct_zero]

/-- Reduction of quadratic forms with symmetric block matrices. -/
theorem dotProduct_fromBlocks_symm_mulVec {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (B : Matrix l m ℝ) (D : Matrix m m ℝ)
    (u : l → ℝ) (v : m → ℝ) :
    Sum.elim u v ⬝ᵥ (fromBlocks A B Bᵀ D *ᵥ Sum.elim u v) =
      u ⬝ᵥ (A *ᵥ u) + 2 * (u ⬝ᵥ (B *ᵥ v)) + v ⬝ᵥ (D *ᵥ v) := by
  rw [dotProduct_fromBlocks_mulVec]
  have h : v ⬝ᵥ (Bᵀ *ᵥ u) = u ⬝ᵥ (B *ᵥ v) := dotProduct_transpose_mulVec B v u
  rw [h]
  ring

/-- A vector quadratic form is invariant under matrix transposition. -/
theorem dotProduct_mulVec_transpose_self {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (Mᵀ *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_transpose_mulVec]

/-- The quadratic form of a skew-symmetric matrix vanishes identically. -/
theorem dotProduct_mulVec_skew {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : Mᵀ = -M) (x : n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = 0 := by
  have h1 : x ⬝ᵥ (Mᵀ *ᵥ x) = x ⬝ᵥ ((-M) *ᵥ x) := by rw [hM]
  have h2 : x ⬝ᵥ ((-M) *ᵥ x) = - (x ⬝ᵥ (M *ᵥ x)) := by
    simp only [neg_mulVec, dotProduct_neg]
  rw [dotProduct_mulVec_transpose_self] at h1
  linarith

/-- The quadratic form of any square matrix equals that of its symmetric part. -/
theorem dotProduct_mulVec_symm_part {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (((1/2 : ℝ) • (M + Mᵀ)) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  simp only [smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add,
    dotProduct_mulVec_transpose_self, smul_eq_mul]
  ring

/-- Quadratic form of a 2×2 block matrix. -/
theorem quad_fromBlocks {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (B : Matrix l m ℝ) (C : Matrix m l ℝ) (D : Matrix m m ℝ)
    (u : l → ℝ) (v : m → ℝ) :
    quad (fromBlocks A B C D) (Sum.elim u v) =
      quad A u + u ⬝ᵥ (B *ᵥ v) + v ⬝ᵥ (C *ᵥ u) + quad D v :=
  dotProduct_fromBlocks_mulVec A B C D u v

/-- Quadratic form of a block diagonal matrix decomposes into the sum of subsystem forms. -/
theorem quad_fromBlocks_diag {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (D : Matrix m m ℝ) (u : l → ℝ) (v : m → ℝ) :
    quad (fromBlocks A 0 0 D) (Sum.elim u v) = quad A u + quad D v :=
  dotProduct_fromBlocks_diag_mulVec A D u v

/-- Quadratic form of a symmetric block matrix with cross term doubled. -/
theorem quad_fromBlocks_symm {l m : Type*} [Fintype l] [Fintype m]
    (A : Matrix l l ℝ) (B : Matrix l m ℝ) (D : Matrix m m ℝ)
    (u : l → ℝ) (v : m → ℝ) :
    quad (fromBlocks A B Bᵀ D) (Sum.elim u v) =
      quad A u + 2 * (u ⬝ᵥ (B *ᵥ v)) + quad D v :=
  dotProduct_fromBlocks_symm_mulVec A B D u v

/-- Quadratic form is invariant under matrix transpose: `quad Mᵀ x = quad M x`. -/
theorem quad_transpose {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad Mᵀ x = quad M x :=
  dotProduct_mulVec_transpose_self M x

/-- Additivity of quadratic forms over matrices. -/
theorem quad_add {n : Type*} [Fintype n] (M N : Matrix n n ℝ) (x : n → ℝ) :
    quad (M + N) x = quad M x + quad N x := by
  simp only [quad, add_mulVec, dotProduct_add]

/-- Negation of quadratic forms over matrices. -/
theorem quad_neg {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad (-M) x = - quad M x := by
  simp only [quad, neg_mulVec, dotProduct_neg]

/-- Scalar scaling of matrices in quadratic forms. -/
theorem quad_smul_mat {n : Type*} [Fintype n] (c : ℝ) (M : Matrix n n ℝ) (x : n → ℝ) :
    quad (c • M) x = c * quad M x := by
  simp only [quad, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The quadratic form of a skew-symmetric matrix vanishes. -/
theorem quad_skew {n : Type*} [Fintype n] (M : Matrix n n ℝ) (hM : Mᵀ = -M) (x : n → ℝ) :
    quad M x = 0 :=
  dotProduct_mulVec_skew M hM x

/-- The quadratic form of any square matrix equals that of its symmetric part. -/
theorem quad_symm_part {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad ((1/2 : ℝ) • (M + Mᵀ)) x = quad M x :=
  dotProduct_mulVec_symm_part M x

/-- Quadratic form transformation by a rectangular matrix `K`:
`quad M (K x) = quad (Kᵀ M K) x`. -/
theorem quad_mulVec_rect {l m : Type*} [Fintype l] [Fintype m]
    (M : Matrix m m ℝ) (K : Matrix m l ℝ) (x : l → ℝ) :
    quad M (K *ᵥ x) = quad (Kᵀ * M * K) x := by
  simp only [quad, ← mulVec_mulVec, dotProduct_mulVec _ Kᵀ, vecMul_transpose]

/-- Stage-cost reduction in LQR optimal control under state feedback `u = K x`:
the combined state-input cost `quad (diag Q R) [x; K x]` equals `quad (Q + Kᵀ R K) x`. -/
theorem quad_lqr_feedback {l m : Type*} [Fintype l] [Fintype m]
    (Q : Matrix l l ℝ) (R : Matrix m m ℝ) (K : Matrix m l ℝ) (x : l → ℝ) :
    quad (fromBlocks Q 0 0 R) (Sum.elim x (K *ᵥ x)) = quad (Q + Kᵀ * R * K) x := by
  rw [quad_fromBlocks_diag, quad_mulVec_rect, quad_add]

/-! ### 2. Normalization of Linear Fractional & Algebraic Riccati Expressions -/

section LFT

variable {K : Type*} [Field K]

/-- The parallel sum / precision inversion identity: `(P * R / (P + R))⁻¹ = P⁻¹ + R⁻¹`. -/
theorem inv_parallel_sum {P R : K} (hP : P ≠ 0) (hR : R ≠ 0) (_hPR : P + R ≠ 0) :
    (P * R / (P + R))⁻¹ = P⁻¹ + R⁻¹ := by
  field_simp
  ring

/-- The harmonic sum / parallel sum inverted: `(P⁻¹ + R⁻¹)⁻¹ = P * R / (P + R)`. -/
theorem parallel_sum_eq_inv_inv {P R : K} (hP : P ≠ 0) (hR : R ≠ 0)
    (h_sum : P⁻¹ + R⁻¹ ≠ 0) :
    (P⁻¹ + R⁻¹)⁻¹ = P * R / (P + R) := by
  have hPR : P + R ≠ 0 := by
    intro hc
    have : P⁻¹ + R⁻¹ = 0 := by
      field_simp
      linear_combination hc
    exact h_sum this
  rw [← inv_parallel_sum hP hR hPR, inv_inv]

/-- Linear fractional transformation (LFT) / Möbius form of the algebraic Riccati step:
`P * R / (P + R) + Q = ((R + Q) * P + Q * R) / (P + R)`. -/
theorem riccati_lft_form (P R Q : K) (_hPR : P + R ≠ 0) :
    P * R / (P + R) + Q = ((R + Q) * P + Q * R) / (P + R) := by
  field_simp
  ring

/-- Commuted form: `Q + P * R / (P + R) = ((R + Q) * P + Q * R) / (P + R)`. -/
theorem riccati_lft_form_comm (P R Q : K) (hPR : P + R ≠ 0) :
    Q + P * R / (P + R) = ((R + Q) * P + Q * R) / (P + R) := by
  rw [add_comm, riccati_lft_form P R Q hPR]

/-- Riccati step in terms of precision / inverse addition. -/
theorem riccati_inv_form {P R : K} (Q : K) (hP : P ≠ 0) (hR : R ≠ 0)
    (h_sum : P⁻¹ + R⁻¹ ≠ 0) :
    (P⁻¹ + R⁻¹)⁻¹ + Q = P * R / (P + R) + Q := by
  rw [parallel_sum_eq_inv_inv hP hR h_sum]

/-- Difference of two Riccati steps: quadratic numerator in sensor noise variance `R`. -/
theorem riccati_lft_sub (P₁ P₂ R Q : K) (_h₁ : P₁ + R ≠ 0) (_h₂ : P₂ + R ≠ 0) :
    (P₁ * R / (P₁ + R) + Q) - (P₂ * R / (P₂ + R) + Q) =
      R ^ 2 * (P₁ - P₂) / ((P₁ + R) * (P₂ + R)) := by
  field_simp
  ring

/-- In precision space, sensor noise cancels additively:
`(P₁⁻¹ + R⁻¹) - (P₂⁻¹ + R⁻¹) = P₁⁻¹ - P₂⁻¹`. -/
theorem riccati_inv_sub (P₁ P₂ R : K) :
    (P₁⁻¹ + R⁻¹) - (P₂⁻¹ + R⁻¹) = P₁⁻¹ - P₂⁻¹ := by
  ring

/-- Algebraic Riccati equation fixed point reduces to quadratic equation:
`P * R / (P + R) + Q = P ↔ P² - Q P - Q R = 0`. -/
theorem riccati_fixed_iff_quadratic (P R Q : K) (hPR : P + R ≠ 0) :
    P * R / (P + R) + Q = P ↔ P ^ 2 - Q * P - Q * R = 0 := by
  rw [div_add' _ _ _ hPR, div_eq_iff hPR]
  constructor
  · intro h
    calc P ^ 2 - Q * P - Q * R = P * (P + R) - (P * R + Q * (P + R)) := by ring
      _ = P * (P + R) - P * (P + R) := by rw [h]
      _ = 0 := by ring
  · intro h
    calc P * R + Q * (P + R) = P * (P + R) - (P ^ 2 - Q * P - Q * R) := by ring
      _ = P * (P + R) - 0 := by rw [h]
      _ = P * (P + R) := by ring

/-- Fixed point equivalence in precision / inverse form. -/
theorem riccati_fixed_inv_iff_quadratic (P R Q : K) (hP : P ≠ 0) (hR : R ≠ 0)
    (h_sum : P⁻¹ + R⁻¹ ≠ 0) (hPR : P + R ≠ 0) :
    (P⁻¹ + R⁻¹)⁻¹ + Q = P ↔ P ^ 2 - Q * P - Q * R = 0 := by
  rw [riccati_inv_form Q hP hR h_sum]
  exact riccati_fixed_iff_quadratic P R Q hPR

end LFT

/-! ### 3. Discrete Lyapunov Stability Contraction and Helper Lemmas -/

section Lyapunov

variable {α : Type*}

/-- Chaining geometric contraction along iterates of an arbitrary function `f`:
`V (f x) ≤ ρ * V x` implies `V (f^[k] x₀) ≤ ρ^k * V x₀`. -/
theorem lyapunov_geometric_iterate (V : α → ℝ) (f : α → α) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hstep : ∀ x, V (f x) ≤ ρ * V x) (x₀ : α) (k : ℕ) :
    V (f^[k] x₀) ≤ ρ ^ k * V x₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    calc V (f (f^[k] x₀)) ≤ ρ * V (f^[k] x₀) := hstep _
      _ ≤ ρ * (ρ ^ k * V x₀) := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (k + 1) * V x₀ := by ring

/-- Dissipation rate `V(fx) - V(x) ≤ -c * V(x)` converts to contraction rate
`V(fx) ≤ (1 - c) V(x)`. -/
theorem lyapunov_contraction_of_dissipation (V : α → ℝ) (f : α → α) (c : ℝ)
    (hstep : ∀ x, V (f x) - V x ≤ -c * V x) (x : α) :
    V (f x) ≤ (1 - c) * V x := by
  have := hstep x
  linarith

/-- Chaining dissipation rate into geometric decay: `V (f^[k] x₀) ≤ (1 - c)^k * V x₀`. -/
theorem lyapunov_geometric_dissipation (V : α → ℝ) (f : α → α) (c : ℝ)
    (hc : 0 ≤ 1 - c)
    (hstep : ∀ x, V (f x) - V x ≤ -c * V x) (x₀ : α) (k : ℕ) :
    V (f^[k] x₀) ≤ (1 - c) ^ k * V x₀ := by
  refine lyapunov_geometric_iterate V f (1 - c) hc ?_ x₀ k
  intro x
  exact lyapunov_contraction_of_dissipation V f c hstep x

variable {n : Type*} [Fintype n]

section Decidable

variable [DecidableEq n]

/-- Matrix power vector multiplication equals iterated linear map. -/
theorem mulVec_pow_eq_iterate (A : Matrix n n ℝ) (k : ℕ) (x₀ : n → ℝ) :
    (A ^ k) *ᵥ x₀ = (fun x => A *ᵥ x)^[k] x₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, Function.iterate_succ', Function.comp_apply]

/-- Chaining geometric contraction for LTI system `x ↦ A *ᵥ x`:
`V (A x) ≤ ρ * V x` implies `V (A^k x₀) ≤ ρ^k * V x₀`. -/
theorem lyapunov_geometric_mulVec (V : (n → ℝ) → ℝ) (A : Matrix n n ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hstep : ∀ x, V (A *ᵥ x) ≤ ρ * V x) (x₀ : n → ℝ) (k : ℕ) :
    V ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * V x₀ := by
  rw [mulVec_pow_eq_iterate]
  exact lyapunov_geometric_iterate V (fun x => A *ᵥ x) ρ hρ0 hstep x₀ k

/-- Chaining geometric contraction for quadratic Lyapunov functions:
`quad P (A x) ≤ ρ * quad P x` implies `quad P (A^k x₀) ≤ ρ^k * quad P x₀`. -/
theorem quad_lyapunov_geometric (A P : Matrix n n ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hstep : ∀ x, quad P (A *ᵥ x) ≤ ρ * quad P x) (x₀ : n → ℝ) (k : ℕ) :
    quad P ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * quad P x₀ :=
  lyapunov_geometric_mulVec (quad P) A ρ hρ0 hstep x₀ k

end Decidable

/-- Discrete-time Lyapunov step difference identity:
`quad P (A x) - quad P x = - quad (P - Aᵀ P A) x`. -/
theorem quad_lyapunov_step (A P : Matrix n n ℝ) (x : n → ℝ) :
    quad P (A *ᵥ x) - quad P x = - quad (P - Aᵀ * P * A) x := by
  rw [quad_sub, quad_mulVec]
  ring

/-- Discrete Lyapunov algebraic relation: if `P - Aᵀ P A = Q`, then
`quad P (A x) - quad P x = - quad Q x`. -/
theorem quad_lyapunov_step_dlyap (A P Q : Matrix n n ℝ)
    (h : P - Aᵀ * P * A = Q) (x : n → ℝ) :
    quad P (A *ᵥ x) - quad P x = - quad Q x := by
  rw [quad_lyapunov_step, h]

end Lyapunov

/-! ### 4. Macros and Tactics for Control Formalization -/

/-- Tactic macro for simplifying quadratic forms and block matrix expressions. -/
macro "quad_simp" : tactic =>
  `(tactic| simp only [ControlsLean.Tactics.quad_fromBlocks_diag,
    ControlsLean.Tactics.quad_fromBlocks_symm,
    ControlsLean.Tactics.quad_fromBlocks,
    ControlsLean.Tactics.quad_mulVec_rect,
    ControlsLean.Controls.quad_mulVec,
    ControlsLean.Tactics.quad_transpose,
    ControlsLean.Tactics.quad_add,
    ControlsLean.Controls.quad_sub,
    ControlsLean.Tactics.quad_neg,
    ControlsLean.Tactics.quad_smul_mat])

/-- Tactic macro for normalizing linear fractional and Riccati expressions. -/
macro "riccati_lft_norm" : tactic =>
  `(tactic| simp only [ControlsLean.Tactics.riccati_lft_form,
    ControlsLean.Tactics.riccati_lft_form_comm,
    ControlsLean.Tactics.riccati_inv_sub])

/-- Tactic macro for expanding discrete Lyapunov difference steps. -/
macro "lyapunov_step_simp" : tactic =>
  `(tactic| simp only [ControlsLean.Tactics.quad_lyapunov_step,
    ControlsLean.Controls.quad_sub,
    ControlsLean.Controls.quad_mulVec])

/-- Tactic macro for converting positive definiteness `M.PosDef` to quadratic form positivity. -/
macro "posdef_to_quad" : tactic =>
  `(tactic| rw [ControlsLean.Tactics.posDef_iff_quad_pos])

/-- Tactic macro for converting `M.PosSemidef` to quadratic form nonnegativity. -/
macro "possemidef_to_quad" : tactic =>
  `(tactic| rw [ControlsLean.Tactics.posSemidef_iff_quad_nonneg])

end ControlsLean.Tactics
