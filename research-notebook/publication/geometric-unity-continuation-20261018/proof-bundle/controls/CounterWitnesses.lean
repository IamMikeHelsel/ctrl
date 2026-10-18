import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
namespace ReviewerCounterWitnesses

theorem missing_sign_is_false : K *ᵥ unitCoord {6} ≠ unitCoord ({6} : Finset J)ᶜ := by
  intro h
  rw [ReviewerSignature.singleton_last_sign] at h
  have he := congrFun h (({6} : Finset J)ᶜ)
  norm_num [unitCoord, Pi.single_apply] at he

theorem missing_complement_is_false : K ∅ ∅ ≠ 1 := by
  rw [K_zero_diagonal]
  norm_num

theorem unit_normalization_is_false : (U.transpose * K * U) ∅ ∅ ≠ 1 := by
  rw [real_positive_direction]
  norm_num

theorem real_positive_only_is_false : (U.transpose * K * U) {0,6} {0,6} ≠ 2 := by
  rw [ReviewerSignature.real_negative_value]
  norm_num

theorem complex_positive_only_is_false : (Uc.conjTranspose * Kc * Uc) {0,6} {0,6} ≠ 2 := by
  rw [ReviewerSignature.complex_negative_value]
  norm_num

theorem unscaled_inverse_is_false : (U.transpose * U) ∅ ∅ ≠ 1 := by
  rw [U_orthogonal_scaled]
  norm_num

theorem wrong_half_count_is_false :
    (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card ≠ 63 := by
  rw [positive_half_count]
  norm_num

theorem ignoring_scalar_conjugation_is_false :
    complexMatrixEquiv (bar (Complex.I • (1 : CCl))) ∅ ∅ ≠ Complex.I := by
  rw [complexMatrixEquiv_bar_I]
  norm_num [Matrix.one_apply, Complex.ext_iff]

theorem omitted_D_is_false :
    ((1+K) *ᵥ (unitCoord ∅ - K *ᵥ unitCoord ∅)) ∅ ≠ 1 := by
  rw [unpaired_projector_kills]
  norm_num

end ReviewerCounterWitnesses
