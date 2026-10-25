import Mathlib

/-!
A continuous-time Lyapunov certificate `AᵀP + PA = -Q` (Q positive definite) is automatically a
discrete-time certificate for the sampled matrix `exp(T • A)`, for every `T > 0`:
`x ⬝ (exp(TA)ᵀ P exp(TA) - P) x < 0` for `x ≠ 0`. No positivity of `P` is needed.
-/

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace SampledExplore

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form `M ↦ x ⬝ (M x)` as a continuous linear functional on matrices. -/
noncomputable def quadL (x : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => x ⬝ᵥ (M *ᵥ x)
      map_add' := fun M N => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun c M => by simp [smul_mulVec, dotProduct_smul] }

omit [DecidableEq n] in
@[simp] lemma quadL_apply (x : n → ℝ) (M : Matrix n n ℝ) : quadL x M = x ⬝ᵥ (M *ᵥ x) := rfl

lemma exp_mulVec_ne_zero (A : Matrix n n ℝ) (t : ℝ) {x : n → ℝ} (hx : x ≠ 0) :
    exp (t • A) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have h1 : exp (-(t • A)) * exp (t • A) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • A)).neg_left), neg_add_cancel,
      exp_zero]
  calc x = (exp (-(t • A)) * exp (t • A)) *ᵥ x := by rw [h1, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h, mulVec_zero]

theorem discreteLyapunov_of_continuous {A P Q : Matrix n n ℝ}
    (hlyap : Aᵀ * P + P * A = -Q) (hQ : ∀ y ≠ 0, 0 < y ⬝ᵥ (Q *ᵥ y)) {T : ℝ} (hT : 0 < T)
    (x : n → ℝ) (hx : x ≠ 0) :
    x ⬝ᵥ (((exp (T • A))ᵀ * P * exp (T • A) - P) *ᵥ x) < 0 := by
  set F : ℝ → Matrix n n ℝ := fun t => exp (t • Aᵀ) * P * exp (t • A) with hF
  have hderF : ∀ t, HasDerivAt F (-(exp (t • Aᵀ) * Q * exp (t • A))) t := by
    intro t
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Aᵀ t
    have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
    have := (h1.mul_const P).mul h2
    refine this.congr_deriv ?_
    calc exp (t • Aᵀ) * Aᵀ * P * exp (t • A) + exp (t • Aᵀ) * P * (A * exp (t • A))
        = exp (t • Aᵀ) * (Aᵀ * P + P * A) * exp (t • A) := by noncomm_ring
      _ = -(exp (t • Aᵀ) * Q * exp (t • A)) := by rw [hlyap]; noncomm_ring
  let f : ℝ → ℝ := fun t => quadL x (F t)
  have hderf : ∀ t, HasDerivAt f (quadL x (-(exp (t • Aᵀ) * Q * exp (t • A)))) t :=
    fun t => (quadL x).hasFDerivAt.comp_hasDerivAt t (hderF t)
  have hneg : ∀ t, deriv f t < 0 := by
    intro t
    rw [(hderf t).deriv, quadL_apply, neg_mulVec, dotProduct_neg, neg_neg_iff_pos,
      ← transpose_smul, exp_transpose, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose]
    exact hQ _ (exp_mulVec_ne_zero A t hx)
  have hanti := strictAnti_of_deriv_neg hneg
  have hlt := hanti hT
  simp only [f, hF, quadL_apply, zero_smul, exp_zero, one_mul, mul_one] at hlt
  rw [sub_mulVec, dotProduct_sub, sub_neg, ← exp_transpose, transpose_smul]
  exact hlt

end SampledExplore

#print axioms SampledExplore.discreteLyapunov_of_continuous
