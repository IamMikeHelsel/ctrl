import ControlsLean.Robotics.SO3Rodrigues
import Mathlib

open Matrix ControlsLean.Vision ControlsLean.Robotics NormedSpace
open scoped Nat

namespace RoboticsLieScratch

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ω : Fin 3 → ℝ}

theorem skew_pow_odd (hω : ω ⬝ᵥ ω = 1) (m : ℕ) :
    skew ω ^ (2 * m + 1) = ((-1 : ℝ) ^ m) • skew ω := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, ih, pow_two, smul_mul_assoc,
      skew_cube, hω, pow_succ, mul_smul]

theorem skew_pow_even_succ (hω : ω ⬝ᵥ ω = 1) (m : ℕ) :
    skew ω ^ (2 * m + 2) = ((-1 : ℝ) ^ m) • (skew ω * skew ω) := by
  rw [pow_succ, skew_pow_odd hω, smul_mul_assoc]

/-- **Rodrigues = matrix exponential**: `exp(θ [ω]×) = I + sin θ [ω]× + (1 - cos θ) [ω]×²`. -/
theorem exp_smul_skew (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    exp (θ • skew ω) = rodrigues ω θ := by
  set K := skew ω
  refine ((exp_series_hasSum_exp' (𝕂 := ℝ) (θ • K)).unique ?_)
  rw [rodrigues, add_assoc, add_comm (Real.sin θ • K), ← add_assoc]
  refine HasSum.even_add_odd ?_ ?_
  · have hc := ((Real.hasSum_cos θ).smul_const (K * K))
    have hi := hasSum_ite_eq (0 : ℕ) (1 + K * K)
    have h := hi.sub hc
    have hfun : (fun m : ℕ => (if m = 0 then 1 + K * K else 0) -
        ((-1) ^ m * θ ^ (2 * m) / ↑(2 * m)! : ℝ) • (K * K)) =
        fun m : ℕ => ((2 * m)! : ℝ)⁻¹ • (θ • K) ^ (2 * m) := by
      funext m
      rcases m with _ | k
      · simp
      · rw [smul_pow, show 2 * (k + 1) = 2 * k + 2 by ring, skew_pow_even_succ hω, smul_smul,
          smul_smul, if_neg (Nat.succ_ne_zero k), zero_sub, ← neg_smul]
        congr 1
        rw [pow_succ]
        field_simp
    have hval : 1 + K * K - Real.cos θ • (K * K) = 1 + (1 - Real.cos θ) • (K * K) := by
      rw [sub_smul, one_smul]; abel
    rw [hfun, hval] at h
    exact h
  · have h := (Real.hasSum_sin θ).smul_const K
    have hfun : (fun m : ℕ => ((-1) ^ m * θ ^ (2 * m + 1) / ↑(2 * m + 1)! : ℝ) • K) =
        fun m : ℕ => ((2 * m + 1)! : ℝ)⁻¹ • (θ • K) ^ (2 * m + 1) := by
      funext m
      rw [smul_pow, skew_pow_odd hω, smul_smul, smul_smul]
      congr 1
      field_simp
    rw [hfun] at h
    exact h

end RoboticsLieScratch
