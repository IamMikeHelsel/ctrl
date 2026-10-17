/-
Copyright (c) 2026 ControlsLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ControlsLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scalar Kalman filter

Prior estimate with error variance `P > 0`; measurement `z = x + v` with noise variance `R > 0`.
A linear update `x̂⁺ = x̂ + k (z - x̂)` has posterior error variance `(1 - k)² P + k² R`.

* The Kalman gain `K = P / (P + R)` is the unique minimiser of this variance.
* The optimal posterior variance is `P R / (P + R)`, and information adds: `1/P⁺ = 1/P + 1/R`.
* Fusing a measurement strictly reduces uncertainty below both `P` and `R`.
* For the random walk `x_{k+1} = x_k + w`, `Var w = Q > 0`, the Riccati recursion
  `P ↦ P R / (P + R) + Q` has a unique positive fixed point, and is a contraction on `(0, ∞)`.
-/

namespace ControlsLean.Estimation

variable {P R Q : ℝ}

/-- Posterior error variance using gain `k`. -/
def postVar (P R k : ℝ) : ℝ := (1 - k) ^ 2 * P + k ^ 2 * R

/-- The Kalman gain. -/
noncomputable def gain (P R : ℝ) : ℝ := P / (P + R)

/-- The optimal posterior variance. -/
noncomputable def postVarOpt (P R : ℝ) : ℝ := P * R / (P + R)

theorem postVar_gain (hP : 0 < P) (hR : 0 < R) : postVar P R (gain P R) = postVarOpt P R := by
  have : P + R ≠ 0 := by positivity
  unfold postVar gain postVarOpt
  field_simp
  ring

/-- Completing the square: `postVar` exceeds the optimum by `(P + R) (k - K)²`. -/
theorem postVar_eq (hP : 0 < P) (hR : 0 < R) (k : ℝ) :
    postVar P R k = postVarOpt P R + (P + R) * (k - gain P R) ^ 2 := by
  have : P + R ≠ 0 := by positivity
  unfold postVar gain postVarOpt
  field_simp
  ring

/-- **Optimality of the Kalman gain.** -/
theorem postVarOpt_le_postVar (hP : 0 < P) (hR : 0 < R) (k : ℝ) :
    postVarOpt P R ≤ postVar P R k := by
  rw [postVar_eq hP hR]
  have : 0 < P + R := by positivity
  nlinarith [sq_nonneg (k - gain P R)]

/-- The Kalman gain is the *unique* minimiser. -/
theorem postVar_eq_opt_iff (hP : 0 < P) (hR : 0 < R) (k : ℝ) :
    postVar P R k = postVarOpt P R ↔ k = gain P R := by
  rw [postVar_eq hP hR]
  have : 0 < P + R := by positivity
  constructor
  · intro h
    have : (P + R) * (k - gain P R) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      ((mul_eq_zero.1 this).resolve_left (by positivity))
    linarith
  · rintro rfl; simp

theorem gain_mem_Ioo (hP : 0 < P) (hR : 0 < R) : 0 < gain P R ∧ gain P R < 1 := by
  unfold gain
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- **Information form**: precisions add. -/
theorem inv_postVarOpt (hP : 0 < P) (hR : 0 < R) :
    (postVarOpt P R)⁻¹ = P⁻¹ + R⁻¹ := by
  unfold postVarOpt
  field_simp
  ring

theorem postVarOpt_pos (hP : 0 < P) (hR : 0 < R) : 0 < postVarOpt P R := by
  unfold postVarOpt; positivity

/-- A measurement strictly reduces uncertainty below the prior. -/
theorem postVarOpt_lt_prior (hP : 0 < P) (hR : 0 < R) : postVarOpt P R < P := by
  unfold postVarOpt
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- ... and below the sensor noise. -/
theorem postVarOpt_lt_noise (hP : 0 < P) (hR : 0 < R) : postVarOpt P R < R := by
  unfold postVarOpt
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- Fusing two measurements sequentially is order independent. -/
theorem postVarOpt_comm_seq (hP : 0 < P) {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    postVarOpt (postVarOpt P R₁) R₂ = postVarOpt (postVarOpt P R₂) R₁ := by
  have a := postVarOpt_pos hP h₁
  have b := postVarOpt_pos hP h₂
  apply inv_injective
  rw [inv_postVarOpt a h₂, inv_postVarOpt b h₁, inv_postVarOpt hP h₁, inv_postVarOpt hP h₂]
  ring

/-! ### Steady state for a random walk -/

/-- One predict+update step of the Riccati recursion (prior variance to prior variance). -/
noncomputable def riccati (R Q P : ℝ) : ℝ := postVarOpt P R + Q

/-- The steady-state prior variance `(Q + √(Q² + 4 Q R)) / 2`. -/
noncomputable def steadyState (R Q : ℝ) : ℝ := (Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2

/-- Positive fixed points of the Riccati map are exactly roots of `P² - Q P - Q R = 0`. -/
theorem riccati_fixed_iff (hR : 0 < R) (hP : 0 < P) :
    riccati R Q P = P ↔ P ^ 2 - Q * P - Q * R = 0 := by
  unfold riccati postVarOpt
  have : P + R ≠ 0 := by positivity
  rw [div_add' _ _ _ this, div_eq_iff this]
  constructor <;> intro h <;> linarith

theorem steadyState_pos (R : ℝ) (hQ : 0 < Q) : 0 < steadyState R Q := by
  unfold steadyState
  have := Real.sqrt_nonneg (Q ^ 2 + 4 * Q * R)
  linarith

theorem riccati_steadyState (hR : 0 < R) (hQ : 0 < Q) :
    riccati R Q (steadyState R Q) = steadyState R Q := by
  rw [riccati_fixed_iff hR (steadyState_pos R hQ)]
  unfold steadyState
  have hs := Real.sq_sqrt (show 0 ≤ Q ^ 2 + 4 * Q * R by positivity)
  nlinarith

/-- **Uniqueness**: the steady state is the only positive fixed point. -/
theorem riccati_fixed_unique (hR : 0 < R) (hQ : 0 < Q) (hP : 0 < P) (h : riccati R Q P = P) :
    P = steadyState R Q := by
  rw [riccati_fixed_iff hR hP] at h
  have h' := (riccati_fixed_iff hR (steadyState_pos R hQ)).1 (riccati_steadyState hR hQ)
  set S := steadyState R Q
  have hS := steadyState_pos R hQ
  -- `(P - S) (P + S - Q) = 0`, and `P + S - Q > 0` because `S > Q`.
  have hSQ : Q < S := by
    unfold S steadyState
    have : Q < Real.sqrt (Q ^ 2 + 4 * Q * R) := by
      rw [Real.lt_sqrt hQ.le]; nlinarith
    linarith
  have : (P - S) * (P + S - Q) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1 <;> linarith

/-- The Riccati map is a strict contraction on `(0, ∞)`: it is monotone with slope `< 1`. -/
theorem riccati_lipschitz (hR : 0 < R) {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) :
    |riccati R Q P₁ - riccati R Q P₂| ≤ (R / (min P₁ P₂ + R)) ^ 2 * |P₁ - P₂| := by
  unfold riccati postVarOpt
  have e : P₁ * R / (P₁ + R) + Q - (P₂ * R / (P₂ + R) + Q)
      = R ^ 2 / ((P₁ + R) * (P₂ + R)) * (P₁ - P₂) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < R ^ 2 / ((P₁ + R) * (P₂ + R)))]
  gcongr
  rw [div_pow, pow_two (min P₁ P₂ + R)]
  gcongr <;> first | exact min_le_left _ _ | exact min_le_right _ _

end ControlsLean.Estimation
