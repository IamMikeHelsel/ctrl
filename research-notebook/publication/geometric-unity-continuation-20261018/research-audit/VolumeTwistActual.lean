import VolumeTwist
import Chirality

noncomputable section
namespace GUVolumeTwistActual
open GUClifford HyperbolicSpinor

/-- An actual invertible Clifford generator, not an assumed test vector. -/
def firstGeneratorUnit : Clˣ where
  val := gamma 0
  inv := gamma 0
  val_inv := by simpa [eps] using gamma_sq (0 : Ix)
  inv_val := by simpa [eps] using gamma_sq (0 : Ix)

/-- The actual volume-twisted first vector is independent of the first vector. -/
theorem actual_vector_pair_independent :
    ∀ a b : ℝ, a • gamma 0 + b • (chirality * gamma 0) = 0 → a = 0 ∧ b = 0 := by
  apply GUVolumeTwist.independent_unit_twist chirality firstGeneratorUnit
  intro r
  simpa [Algebra.algebraMap_eq_smul_one] using chirality_not_scalar r

/-- Independence of the two actual generator-indexed maps. This theorem does
not define or quantify over Spin representations or invariant tensor spaces. -/
theorem actual_generator_maps_independent :
    ∀ a b : ℝ,
      a • (fun j : Ix => gamma j) + b • (fun j : Ix => chirality * gamma j) = 0 →
      a = 0 ∧ b = 0 := by
  exact GUVolumeTwist.function_independence_of_evaluation
    (fun j : Ix => gamma j) (fun j : Ix => chirality * gamma j) 0
    actual_vector_pair_independent

/-- Varying the real twisting coefficient changes the actual generator family. -/
theorem actual_generator_family_injective :
    Function.Injective (fun t : ℝ =>
      (fun j : Ix => gamma j) + t • (fun j : Ix => chirality * gamma j)) := by
  exact GUVolumeTwist.independent_affine_family_injective _ _ actual_generator_maps_independent

/-- Every member remains skew at each generator. -/
theorem actual_generator_family_skew (t : ℝ) (j : Ix) :
    star (gamma j + t • (chirality * gamma j)) =
      -(gamma j + t • (chirality * gamma j)) := by
  have hj : star (gamma j) = -gamma j := by simp [gamma]
  have ht := GUVolumeTwist.skew_twist_of_anticommute chirality (gamma j)
    chirality_star hj (chirality_anticommutes_gamma j)
  rw [star_add, star_smul, hj, ht]
  simp [add_comm]

#print axioms GUVolumeTwistActual.actual_vector_pair_independent
#print axioms GUVolumeTwistActual.actual_generator_maps_independent
#print axioms GUVolumeTwistActual.actual_generator_family_injective
#print axioms GUVolumeTwistActual.actual_generator_family_skew
end GUVolumeTwistActual
