import Mathlib
import ControlsLean.Estimation.KalmanOptimality
import ControlsLean.Estimation.POMDPBelief

namespace ExploreKalman

open Matrix Finset

set_option linter.unusedSectionVars false

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Rectangular information-filter equivalence** (`C : m × n`, `m ≠ n` allowed), via
Mathlib's Woodbury `Matrix.add_mul_mul_inv_eq_sub`:
`(P⁻¹ + Cᵀ R⁻¹ C)⁻¹ = P - P Cᵀ (R + C P Cᵀ)⁻¹ C P`. -/
theorem info_cov_equiv (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hP : IsUnit P) (hR : IsUnit R) (hS : IsUnit (R + C * P * Cᵀ)) :
    (P⁻¹ + Cᵀ * R⁻¹ * C)⁻¹ = P - P * Cᵀ * (R + C * P * Cᵀ)⁻¹ * C * P := by
  have hPi : IsUnit P⁻¹ := (isUnit_nonsing_inv_iff).2 (by simpa [isUnit_iff_isUnit_det] using hP)
  have hRi : IsUnit R⁻¹ := (isUnit_nonsing_inv_iff).2 (by simpa [isUnit_iff_isUnit_det] using hR)
  have hPP : P⁻¹⁻¹ = P := nonsing_inv_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  have hRR : R⁻¹⁻¹ = R := nonsing_inv_nonsing_inv R ((isUnit_iff_isUnit_det R).1 hR)
  have h := add_mul_mul_inv_eq_sub P⁻¹ Cᵀ R⁻¹ C hPi hRi (by rwa [hPP, hRR])
  rw [h, hPP, hRR]

/-- Information-form gain equals covariance-form gain: `P⁺ Cᵀ R⁻¹ = P Cᵀ S⁻¹`. -/
theorem info_gain_eq (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hR : IsUnit R) (hS : IsUnit (R + C * P * Cᵀ)) :
    (P - P * Cᵀ * (R + C * P * Cᵀ)⁻¹ * C * P) * Cᵀ * R⁻¹ = P * Cᵀ * (R + C * P * Cᵀ)⁻¹ := by
  set S := R + C * P * Cᵀ with hSdef
  have hSi : S⁻¹ * S = 1 := nonsing_inv_mul S ((isUnit_iff_isUnit_det S).1 hS)
  have hRi : R * R⁻¹ = 1 := mul_nonsing_inv R ((isUnit_iff_isUnit_det R).1 hR)
  have hCPC : C * P * Cᵀ = S - R := by rw [hSdef]; abel
  calc (P - P * Cᵀ * S⁻¹ * C * P) * Cᵀ * R⁻¹
      = P * Cᵀ * R⁻¹ - P * Cᵀ * S⁻¹ * (C * P * Cᵀ) * R⁻¹ := by
        simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = P * Cᵀ * R⁻¹ - P * Cᵀ * (S⁻¹ * S) * R⁻¹ + P * Cᵀ * S⁻¹ * (R * R⁻¹) := by
        rw [hCPC]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    _ = P * Cᵀ * S⁻¹ := by rw [hSi, hRi]; simp

/-- The optimal gain *exists* when `S` is invertible: `K* = P Cᵀ S⁻¹` satisfies the
normal equation assumed throughout `KalmanOptimality`. -/
theorem kstar_normal_eq (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hS : IsUnit (ControlsLean.Estimation.innovCov P C R)) :
    P * Cᵀ * (ControlsLean.Estimation.innovCov P C R)⁻¹ *
      ControlsLean.Estimation.innovCov P C R = P * Cᵀ := by
  rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hS), Matrix.mul_one]

/-- Measurement never hurts (matrix version, Loewner order): with PSD `S` and an optimal
gain, the Joseph posterior is `≼ P` (take `K = 0` in the completion of squares). -/
theorem quad_post_le_prior {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hK : Kstar * ControlsLean.Estimation.innovCov P C R = P * Cᵀ)
    (hS : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (ControlsLean.Estimation.innovCov P C R *ᵥ y)) (x : n → ℝ) :
    x ⬝ᵥ (ControlsLean.Estimation.josephCov P C R Kstar *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) := by
  have h := ControlsLean.Estimation.quad_josephCov_le hP hR hK hS 0 x
  simpa [ControlsLean.Estimation.josephCov] using h

/-! ### POMDP belief: extra facts -/

open ControlsLean.Estimation.POMDPBelief

/-- If every observation likelihood is strictly positive, the normaliser is automatically
positive for any belief (so `beliefUpdate_isBelief` needs no `Z > 0` hypothesis). -/
theorem obsNormConst_pos_of_pos {k : ℕ} {T : Fin k → Fin k → ℝ} {O : Fin k → ℝ}
    {b : Fin k → ℝ} (hT : IsTransitionKernel T) (hO : ∀ s, 0 < O s) (hb : IsBelief b) :
    0 < obsNormConst T O b := by
  -- Z = ∑ O(s') pred(s') ≥ (min O) · ∑ pred = min O > 0
  have hpred := beliefPredict_obsNormConst_eq_one hT hb
  unfold obsNormConst unnormBeliefUpdate at hpred ⊢
  simp only [one_mul] at hpred
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < ∑ s'' : Fin k, T s'' s * b s'' := by
    by_contra hc
    push Not at hc
    have : ∑ s' : Fin k, ∑ s : Fin k, T s s' * b s ≤ 0 := sum_nonpos fun s _ => hc s
    linarith
  calc 0 < O s₀ * ∑ s : Fin k, T s s₀ * b s := mul_pos (hO s₀) hs₀
    _ ≤ _ := single_le_sum (f := fun s' => O s' * ∑ s : Fin k, T s s' * b s)
        (fun s' _ => mul_nonneg (hO s').le
          (sum_nonneg fun s _ => mul_nonneg (hT.1 s s') (hb.1 s))) (mem_univ s₀)

/-- Without positivity, `Z = 0` is possible and `beliefUpdate` collapses to the zero vector,
which is *not* a belief: concrete counterexample with `n = 1`, `O = 0`. -/
theorem beliefUpdate_not_isBelief_example :
    ¬ IsBelief (beliefUpdate (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ => 0) (fun _ => 1)) := by
  rintro ⟨-, h⟩
  simp [beliefUpdate, obsNormConst, unnormBeliefUpdate] at h

/-- Sequential Bayes = batch Bayes: with static state (`T = 1`), updating with `O₁` then `O₂`
equals updating once with the product likelihood `O₁ · O₂`. -/
theorem beliefUpdate_seq {k : ℕ} (O₁ O₂ : Fin k → ℝ) (b : Fin k → ℝ)
    (hZ₁ : obsNormConst (1 : Matrix (Fin k) (Fin k) ℝ) O₁ b ≠ 0) :
    beliefUpdate (1 : Matrix (Fin k) (Fin k) ℝ) O₂
        (beliefUpdate (1 : Matrix (Fin k) (Fin k) ℝ) O₁ b) =
      beliefUpdate (1 : Matrix (Fin k) (Fin k) ℝ) (fun s => O₁ s * O₂ s) b := by
  have hid : ∀ (O : Fin k → ℝ) (c : Fin k → ℝ) s',
      unnormBeliefUpdate (1 : Matrix (Fin k) (Fin k) ℝ) O c s' = O s' * c s' := by
    intro O c s'
    simp [unnormBeliefUpdate, Matrix.one_apply]
  funext s'
  simp only [beliefUpdate, obsNormConst, hid]
  set Z := ∑ x, O₁ x * b x
  have hZ : Z ≠ 0 := by simpa [obsNormConst, hid] using hZ₁
  have hden : ∑ x, O₂ x * (O₁ x * b x / Z) = (∑ x, O₁ x * O₂ x * b x) / Z := by
    rw [Finset.sum_div]; congr 1; funext x; ring
  rw [hden, mul_div_assoc', div_div_div_cancel_right₀ hZ]
  ring

end ExploreKalman
