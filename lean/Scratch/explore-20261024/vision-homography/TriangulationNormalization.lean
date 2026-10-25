import ControlsLean.Vision.Triangulation
import ControlsLean.Vision.EightPoint
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix
open scoped Kronecker

namespace VisionExplore
open ControlsLean.Vision

variable {K : Type*} [Field K]

/-! ### Triangulation degeneracies -/

/-- **Parallel rays ⇒ the point is on the baseline.** If the scene equation holds and the rays
`x₂`, `R x₁` are parallel, then the baseline `t` is parallel to both rays. -/
theorem baseline_parallel_of_parallel_rays {R : Matrix (Fin 3) (Fin 3) K} {t x₁ x₂ : Fin 3 → K}
    {d₁ d₂ : K} (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) (hpar : x₂ ⨯₃ (R *ᵥ x₁) = 0) :
    x₂ ⨯₃ t = 0 ∧ (R *ᵥ x₁) ⨯₃ t = 0 := by
  have h1 := smul_cross_eq_of_scene h
  have h2 := smul_cross_eq_of_scene' h
  rw [hpar, smul_zero] at h1 h2
  exact ⟨neg_eq_zero.mp h1.symm, neg_eq_zero.mp h2.symm⟩

/-- **Parallel rays ⇒ a whole line of depth solutions** (triangulation genuinely fails). -/
theorem depths_family_of_parallel {R : Matrix (Fin 3) (Fin 3) K} {t x₁ x₂ : Fin 3 → K}
    {d₁ d₂ μ : K} (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) (hpar : x₂ = μ • (R *ᵥ x₁)) (s : K) :
    (d₂ + s) • x₂ = R *ᵥ ((d₁ + μ * s) • x₁) + t := by
  rw [add_smul, h, add_smul, mulVec_add, mulVec_smul (v := x₁) (b := μ * s), hpar, smul_smul,
    mul_comm s μ]
  abel

/-- **Zero baseline (pure rotation).** With `t = 0` and non-parallel rays, the only solution has
both depths zero: nothing can be triangulated. -/
theorem depths_zero_of_zero_baseline {R : Matrix (Fin 3) (Fin 3) K} {x₁ x₂ : Fin 3 → K}
    {d₁ d₂ : K} (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + 0) :
    d₁ = 0 ∧ d₂ = 0 := by
  have h1 := smul_cross_eq_of_scene h
  have h2 := smul_cross_eq_of_scene' h
  simp only [map_zero, neg_zero, smul_eq_zero] at h1 h2
  exact ⟨h1.resolve_right hn, h2.resolve_right hn⟩

/-! ### Hartley normalisation -/

/-- Changing image coordinates by `x ↦ T x` conjugates the epipolar solution set:
`Ê` solves the normalised problem iff `T₂ᵀ Ê T₁` solves the original one. -/
theorem constraint_normalize (T₁ T₂ Ê : Matrix (Fin 3) (Fin 3) K) (x₁ x₂ : Fin 3 → K) :
    (T₂ *ᵥ x₂) ⬝ᵥ (Ê *ᵥ (T₁ *ᵥ x₁)) = x₂ ⬝ᵥ ((T₂ᵀ * Ê * T₁) *ᵥ x₁) := by
  rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← vecMul_transpose,
    dotProduct_comm, ← dotProduct_mulVec]

/-- The normalised constraint matrix is the original one times a Kronecker factor. -/
theorem constraintMatrix_normalize {n : ℕ} (T₁ T₂ : Matrix (Fin 3) (Fin 3) K)
    (x₁ x₂ : Fin n → Fin 3 → K) :
    constraintMatrix (fun i => T₁ *ᵥ x₁ i) (fun i => T₂ *ᵥ x₂ i) =
      constraintMatrix x₁ x₂ * (T₂ᵀ ⊗ₖ T₁ᵀ) := by
  ext i ⟨a, b⟩
  simp only [constraintMatrix, of_apply, mul_apply, kroneckerMap_apply, transpose_apply,
    Fintype.sum_prod_type, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring

/-- **Hartley normalisation cannot cure (or cause) degeneracy**: with invertible `T₁, T₂` the
rank of the eight-point constraint matrix is unchanged; normalisation only improves numerical
conditioning. -/
theorem rank_constraintMatrix_normalize {n : ℕ} (T₁ T₂ : Matrix (Fin 3) (Fin 3) K)
    (h₁ : T₁.det ≠ 0) (h₂ : T₂.det ≠ 0) (x₁ x₂ : Fin n → Fin 3 → K) :
    (constraintMatrix (fun i => T₁ *ᵥ x₁ i) (fun i => T₂ *ᵥ x₂ i)).rank =
      (constraintMatrix x₁ x₂).rank := by
  rw [constraintMatrix_normalize]
  refine rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr ?_)
  rw [det_kronecker, det_transpose, det_transpose]
  exact mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ h₁)

/-- **Normalised eight-point recovery.** If the normalised problem has rank 8 and `Ê ≠ 0` solves
it, then the de-normalised `T₂ᵀ Ê T₁` is a nonzero multiple of the true essential matrix. -/
theorem eq_smul_essential_normalized {n : ℕ} (R T₁ T₂ : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    (h₁ : T₁.det ≠ 0) (h₂ : T₂.det ≠ 0)
    {x₁ x₂ : Fin n → Fin 3 → K} {d₁ d₂ : Fin n → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t)
    (hrank : (constraintMatrix (fun i => T₁ *ᵥ x₁ i) (fun i => T₂ *ᵥ x₂ i)).rank = 8)
    (hess : essential R t ≠ 0) {Ê : Matrix (Fin 3) (Fin 3) K} (hÊ0 : Ê ≠ 0)
    (hÊ : ∀ i, (T₂ *ᵥ x₂ i) ⬝ᵥ (Ê *ᵥ (T₁ *ᵥ x₁ i)) = 0) :
    ∃ c : K, c ≠ 0 ∧ T₂ᵀ * Ê * T₁ = c • essential R t := by
  rw [rank_constraintMatrix_normalize T₁ T₂ h₁ h₂] at hrank
  have hne : T₂ᵀ * Ê * T₁ ≠ 0 := by
    intro h
    have hu₁ : IsUnit T₁.det := isUnit_iff_ne_zero.mpr h₁
    have hu₂ : IsUnit T₂ᵀ.det := isUnit_iff_ne_zero.mpr (by rwa [det_transpose])
    apply hÊ0
    calc Ê = (T₂ᵀ)⁻¹ * (T₂ᵀ * Ê * T₁) * T₁⁻¹ := by
          simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hu₂, Matrix.one_mul]
          rw [Matrix.mul_assoc, mul_nonsing_inv _ hu₁, Matrix.mul_one]
      _ = 0 := by rw [h]; simp
  exact eq_smul_essential R t hd₂ hscene hrank hess hne fun i => by
    rw [← constraint_normalize]; exact hÊ i

end VisionExplore
