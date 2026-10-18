import RationalBoost
noncomputable section
namespace BoostReview
open HyperbolicSpinor GUClifford

theorem not_unit_norm : star boostElement * boostElement ≠ (1 : Cl) := by
  rw [boost_star_mul]
  intro h
  have hm := congrArg splitMatrixEquiv h
  have he := congrArg (fun A : SpinMatrix => A ∅ ∅) hm
  norm_num at he

theorem missing_denominator_product :
    boostElement * ((2 : ℝ) • (1 : Cl) - chirality) = (3 : ℝ) • (1 : Cl) := by
  simp only [boostElement, mul_sub, add_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, chirality_square]
  module

theorem missing_denominator_not_inverse :
    boostElement * ((2 : ℝ) • (1 : Cl) - chirality) ≠ (1 : Cl) := by
  rw [missing_denominator_product]
  intro h
  have hm := congrArg splitMatrixEquiv h
  have he := congrArg (fun A : SpinMatrix => A ∅ ∅) hm
  norm_num at he

end BoostReview
