import GeneralBoost
import HermitianFamily
import ComplexFormUniqueness
import LiftEquivalence
noncomputable section
namespace FinalReview
open GUClifford HyperbolicSpinor GUComplex GUQuadraticTwist GUGeneralBoost

theorem invariant_form_not_fully_compatible : ¬ ComplexCompatible (hermitianFamily 1) := by
  intro h
  obtain ⟨c,hc⟩ := complexCompatible_scalar _ h
  exact hermitianFamily_one_not_scalar c hc

theorem singular_denominator_fails : element 1 1 * inverse 1 1 ≠ (1 : Cl) := by
  simp [inverse]

theorem negative_exception_not_unitary : star chirality * chirality ≠ (1 : Cl) := by
  rw [chirality_star, neg_mul, chirality_square]
  intro h
  have hm := congrArg splitMatrixEquiv h
  have he := congrArg (fun A : SpinMatrix => A ∅ ∅) hm
  norm_num at he

theorem rational_automorphism_not_identity :
    twistedLift (5/3) (4/3) rational_choice_normalized (gamma 0) ≠ gamma 0 := by
  change twistedLift (5/3) (4/3) rational_choice_normalized (CliffordAlgebra.ι Q (e 0)) ≠ gamma 0
  rw [twistedLift_on_vector]
  exact rational_twist_nontrivial

end FinalReview
