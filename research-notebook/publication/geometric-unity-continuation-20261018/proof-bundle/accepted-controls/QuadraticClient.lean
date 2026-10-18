import QuadraticTwist
import RationalBoost
noncomputable section
namespace QuadraticReview
open GUClifford GUQuadraticTwist HyperbolicSpinor

theorem affine_one_is_not_normalized :
    ¬ (∀ v : V, twistedVector 1 1 v * twistedVector 1 1 v = Q v • (1 : Cl)) := by
  rw [twistedVector_preserves_square_iff]
  norm_num

theorem rational_boost_agrees (v : V) :
    boostElement * CliffordAlgebra.ι Q v * boostInverse = twistedVector (5/3) (4/3) v := by
  exact rationalBoost_vector v

end QuadraticReview
