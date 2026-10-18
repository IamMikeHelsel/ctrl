import FockOperators

noncomputable section
namespace HyperbolicSpinor
open GUClifford

theorem low_positive (j : J) : low (e (Fin.castAdd 7 j)) = basisVector j := by
  funext k
  fin_cases j <;> fin_cases k <;> norm_num [low, e, basisVector, Pi.single_apply, Fin.ext_iff]
theorem high_positive (j : J) : high (e (Fin.castAdd 7 j)) = 0 := by
  funext k
  fin_cases j <;> fin_cases k <;> norm_num [high, e]
theorem low_negative (j : J) : low (e (Fin.addNat j 7)) = 0 := by
  funext k
  fin_cases j <;> fin_cases k <;> norm_num [low, e]
theorem high_negative (j : J) : high (e (Fin.addNat j 7)) = basisVector j := by
  funext k
  fin_cases j <;> fin_cases k <;> norm_num [high, e, basisVector, Pi.single_apply, Fin.ext_iff]

theorem dot_basis (j : J) : dotProductEquiv ℝ J (basisVector j) = coordinate j := by
  apply LinearMap.ext
  intro v
  simp [dotProductEquiv, basisVector, coordinate]

theorem split_positive (j : J) : splitLinear (e (Fin.castAdd 7 j)) = (coordinate j, basisVector j) := by
  simp [splitLinear, low_positive, high_positive, dot_basis]
theorem split_negative (j : J) : splitLinear (e (Fin.addNat j 7)) = (-coordinate j, basisVector j) := by
  simp [splitLinear, low_negative, high_negative, dot_basis]

theorem gamma_positive_action (j : J) : splitAction (gamma (Fin.castAdd 7 j)) = annihilate j + create j := by
  rw [splitAction_gamma, split_positive]
  rfl

theorem gamma_negative_action (j : J) : splitAction (gamma (Fin.addNat j 7)) = create j - annihilate j := by
  rw [splitAction_gamma, split_negative]
  apply LinearMap.ext
  intro x
  simp [cliffordVector_apply, create_apply, annihilate_apply]
  abel

def creatorElement (j : J) : Cl := (1/2 : ℝ) • (gamma (Fin.castAdd 7 j) + gamma (Fin.addNat j 7))
def annihilatorElement (j : J) : Cl := (1/2 : ℝ) • (gamma (Fin.castAdd 7 j) - gamma (Fin.addNat j 7))

theorem creator_image (j : J) : splitAction (creatorElement j) = create j := by
  simp only [creatorElement, map_smul, map_add, gamma_positive_action, gamma_negative_action]
  module

theorem annihilator_image (j : J) : splitAction (annihilatorElement j) = annihilate j := by
  simp only [annihilatorElement, map_smul, map_sub, gamma_positive_action, gamma_negative_action]
  module

end HyperbolicSpinor
