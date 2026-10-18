import SkewLie
noncomputable section
namespace SkewReview
open HyperbolicSpinor GUClifford Matrix

theorem scalar_identity_not_skew : ¬ FormSkew K (1 : SpinMatrix) := by
  intro h
  rw [formSkew_iff_adjoint, realAdjoint_one] at h
  have he := congrArg (fun A : SpinMatrix => A ∅ ∅) h
  norm_num at he

theorem positive_generator_is_skew : FormSkew K (splitMatrixEquiv (gamma 0)) := by
  rw [← cliffordSkew_iff_formSkew]
  exact CliffordAlgebra.star_ι (e 0)

theorem positive_generator_square_not_skew :
    ¬ FormSkew K (splitMatrixEquiv (gamma 0) * splitMatrixEquiv (gamma 0)) := by
  simpa only [splitMatrixEquiv_apply, positive_square] using scalar_identity_not_skew

theorem split_generator_is_skew :
    FormSkew D (splitCoordinates (splitMatrixEquiv (gamma 0))) := by
  rw [splitCoordinates_formSkew_iff]
  exact positive_generator_is_skew

end SkewReview
