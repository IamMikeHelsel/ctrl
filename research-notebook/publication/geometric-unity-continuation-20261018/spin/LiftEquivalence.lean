import RationalBoost
import QuadraticTwist

noncomputable section
namespace HyperbolicSpinor
open GUClifford GUQuadraticTwist

/-- Equality on all Clifford elements, beyond the already checked vector formula. -/
theorem rational_lift_inner (x : Cl) :
    twistedLift (5/3) (4/3) rational_choice_normalized x =
      boostElement * x * boostInverse := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      mul_smul_comm, mul_one, smul_mul_assoc, boost_right_inverse]
  | ι v =>
    rw [twistedLift_on_vector, rationalBoost_vector]
    rfl
  | add a b ha hb => simp only [map_add, mul_add, add_mul, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, ha, hb]
    calc
      (boostElement * a * boostInverse) * (boostElement * b * boostInverse) =
          boostElement * a * (boostInverse * boostElement) * b * boostInverse := by
            simp only [mul_assoc]
      _ = boostElement * (a*b) * boostInverse := by rw [boost_left_inverse, mul_one, mul_assoc boostElement]

/-- The rational choice extends to a bijective algebra homomorphism. -/
theorem rational_lift_bijective :
    Function.Bijective (twistedLift (5/3) (4/3) rational_choice_normalized) := by
  constructor
  · intro x y h
    rw [rational_lift_inner, rational_lift_inner] at h
    have hh := congrArg (fun z : Cl => boostInverse*z*boostElement) h
    have hc (z : Cl) : boostInverse*(boostElement*z*boostInverse)*boostElement = z := by
      calc
        _ = (boostInverse*boostElement)*z*(boostInverse*boostElement) := by simp only [mul_assoc]
        _ = z := by rw [boost_left_inverse, one_mul, mul_one]
    simpa only [hc] using hh
  · intro y
    refine ⟨boostInverse*y*boostElement, ?_⟩
    rw [rational_lift_inner]
    calc
      _ = (boostElement*boostInverse)*y*(boostElement*boostInverse) := by simp only [mul_assoc]
      _ = y := by rw [boost_right_inverse, one_mul, mul_one]

end HyperbolicSpinor
