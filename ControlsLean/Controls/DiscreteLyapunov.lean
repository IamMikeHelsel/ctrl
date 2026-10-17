/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Discrete-time Lyapunov stability

For `x_{k+1} = A x_k`, if there is a matrix `P` with `xᵀ P x > 0` and `xᵀ (P - Aᵀ P A) x > 0`
for all `x ≠ 0`, then every trajectory converges to `0` geometrically.

Symmetry of `P` is not needed. The proof bounds quadratic forms above and below by multiples
of `‖x‖²` (via compactness of the unit sphere), shows `V(Ax) ≤ ρ V(x)` for some `ρ < 1`
with `V(x) = xᵀ P x`, and concludes.
-/

open Matrix Filter Topology

namespace ControlsLean.Controls

variable {n : Type*} [Fintype n]

/-- The quadratic form `x ↦ xᵀ M x`. -/
def quad (M : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

theorem quad_smul (M : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) :
    quad M (t • x) = t ^ 2 * quad M x := by
  simp [quad, mulVec_smul, smul_dotProduct, dotProduct_smul, pow_two, mul_assoc]

theorem continuous_quad (M : Matrix n n ℝ) : Continuous (quad M) := by
  unfold quad dotProduct mulVec dotProduct
  fun_prop

theorem quad_mulVec (M A : Matrix n n ℝ) (x : n → ℝ) :
    quad M (A *ᵥ x) = quad (Aᵀ * M * A) x := by
  simp only [quad, ← mulVec_mulVec, dotProduct_mulVec _ Aᵀ, vecMul_transpose]

theorem quad_sub (M N : Matrix n n ℝ) (x : n → ℝ) : quad (M - N) x = quad M x - quad N x := by
  simp [quad, sub_mulVec, dotProduct_sub]

/-- Write `x = ‖x‖ • u` with `‖u‖ = 1`; quadratic forms scale by `‖x‖²`. -/
private lemma quad_eq_norm_sq (M : Matrix n n ℝ) {x : n → ℝ} (hx : x ≠ 0) :
    quad M x = ‖x‖ ^ 2 * quad M (‖x‖⁻¹ • x) := by
  rw [quad_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_pow,
    one_mul]

private lemma norm_inv_smul {x : n → ℝ} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- A positive definite quadratic form dominates a positive multiple of `‖x‖²`. -/
theorem exists_quad_lower {M : Matrix n n ℝ} (hM : ∀ x ≠ 0, 0 < quad M x) :
    ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ quad M x := by
  cases isEmpty_or_nonempty n
  · exact ⟨1, one_pos, fun x => by simp [Subsingleton.elim x 0, quad]⟩
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) (continuous_quad M).continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl; simp at hu
  refine ⟨quad M u, hM u hu0, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [quad]
  rw [quad_eq_norm_sq M hx, mul_comm]
  gcongr
  exact hmin (by simpa using norm_inv_smul hx)

/-- Every quadratic form is bounded by a multiple of `‖x‖²`. -/
theorem exists_quad_upper (M : Matrix n n ℝ) : ∃ C > 0, ∀ x, quad M x ≤ C * ‖x‖ ^ 2 := by
  cases isEmpty_or_nonempty n
  · exact ⟨1, one_pos, fun x => by simp [Subsingleton.elim x 0, quad]⟩
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) (continuous_quad M).continuousOn
  refine ⟨max (quad M u) 1, by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [quad]
  rw [quad_eq_norm_sq M hx, mul_comm]
  gcongr
  exact (hmax (by simpa using norm_inv_smul hx)).trans (le_max_left _ _)

variable {A P : Matrix n n ℝ}

/-- **Geometric decrease of the Lyapunov function.** -/
theorem exists_lyapunov_contraction (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) :
    ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, quad P (A *ᵥ x) ≤ ρ * quad P x := by
  obtain ⟨c, hc, hcQ⟩ := exists_quad_lower hQ
  obtain ⟨C, hC, hCP⟩ := exists_quad_upper P
  refine ⟨max (1 - c / C) 0, le_max_right _ _, max_lt (by linarith [div_pos hc hC]) one_pos,
    fun x => ?_⟩
  have hdec : quad P (A *ᵥ x) = quad P x - quad (P - Aᵀ * P * A) x := by
    rw [quad_sub, quad_mulVec]; ring
  have h1 : c / C * quad P x ≤ quad (P - Aᵀ * P * A) x := by
    calc c / C * quad P x ≤ c / C * (C * ‖x‖ ^ 2) := by gcongr; exact hCP x
      _ = c * ‖x‖ ^ 2 := by field_simp
      _ ≤ _ := hcQ x
  have hV : 0 ≤ quad P x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [quad]
    · exact (hP x hx).le
  calc quad P (A *ᵥ x) ≤ (1 - c / C) * quad P x := by rw [hdec]; linarith
    _ ≤ _ := by gcongr; exact le_max_left _ _

/-- **Discrete-time Lyapunov theorem**: the origin is globally asymptotically stable. -/
theorem tendsto_pow_mulVec_zero [DecidableEq n] (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_lyapunov_contraction hP hQ
  obtain ⟨c, hc, hcP⟩ := exists_quad_lower hP
  have hV : ∀ k : ℕ, quad P ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * quad P x₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec]
      calc _ ≤ ρ * quad P ((A ^ k) *ᵥ x₀) := hρ _
        _ ≤ ρ * (ρ ^ k * quad P x₀) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * quad P x₀ := by ring
  have hsq : Tendsto (fun k : ℕ => ‖(A ^ k) *ᵥ x₀‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => ρ ^ k * quad P x₀ / c) atTop (𝓝 0) := by
      simpa using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (quad P x₀)).div_const c
    refine squeeze_zero (fun _ => by positivity) (fun k => ?_) hlim
    rw [le_div_iff₀ hc, mul_comm]
    exact (hcP _).trans (hV k)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-- Matrix-API form: `P ≻ 0` and `P - Aᵀ P A ≻ 0` imply `Aᵏ x₀ → 0`. -/
theorem PosDef.tendsto_pow_mulVec_zero [DecidableEq n] (hP : P.PosDef)
    (hQ : (P - Aᵀ * P * A).PosDef) (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) atTop (𝓝 0) := by
  refine ControlsLean.Controls.tendsto_pow_mulVec_zero (P := P)
    (fun x hx => ?_) (fun x hx => ?_) x₀
  · simpa [quad] using (posDef_iff_dotProduct_mulVec.1 hP).2 hx
  · simpa [quad] using (posDef_iff_dotProduct_mulVec.1 hQ).2 hx

end ControlsLean.Controls
