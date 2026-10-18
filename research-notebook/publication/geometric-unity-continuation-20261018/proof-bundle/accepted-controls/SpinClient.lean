import SpinEquivariance
noncomputable section
namespace SpinReview
open HyperbolicSpinor GUClifford

theorem spin_has_identity : (1 : Cl) ∈ spinGroup Q := one_mem _

theorem scalar_even (r : ℝ) : algebraMap ℝ Cl r ∈ CliffordAlgebra.even Q :=
  (CliffordAlgebra.even Q).algebraMap_mem r

theorem all_commute_is_false : ¬ (∀ x : Cl, chirality * x = x * chirality) := by
  intro h
  have ha := chirality_anticommutes_gamma 0
  rw [h (gamma 0)] at ha
  have hb := congrArg (fun x : Cl => gamma 0 * x) ha
  have hc : chirality = -chirality := by
    simpa [← mul_assoc, gamma_sq, eps, smul_mul_assoc, one_mul, mul_neg] using hb
  have hz : (2 : ℝ) • chirality = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hc
  have hc0 := (smul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hs := chirality_square
  rw [hc0, zero_mul] at hs
  exact zero_ne_one hs

end SpinReview
