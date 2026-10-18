import RealEquivalence

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- The opposite single-factor order kills the vacuum. -/
theorem wrongFactor_vacuum (j : J) : (create j * annihilate j) (1 : S7) = 0 := by
  change create j (annihilate j 1) = 0
  rw [annihilate_vacuum, map_zero]

theorem wrongFactor_not_vacuum (j : J) : create j * annihilate j ≠ vacuum := by
  intro h
  have he := congrArg (fun f : Module.End ℝ S7 => f 1) h
  rw [wrongFactor_vacuum, vacuum_one] at he
  exact zero_ne_one he

/-- Reversing the intended sign changes the annihilator. -/
def wrongAnnihilatorElement (j : J) : Cl :=
  (1/2 : ℝ) • (gamma (Fin.addNat j 7) - gamma (Fin.castAdd 7 j))

theorem wrongAnnihilator_image (j : J) :
    splitAction (wrongAnnihilatorElement j) = -annihilate j := by
  simp only [wrongAnnihilatorElement, map_smul, map_sub,
    gamma_positive_action, gamma_negative_action]
  module

theorem wrongAnnihilator_created_vacuum (j : J) :
    splitAction (wrongAnnihilatorElement j) (create j (1 : S7)) = -1 := by
  rw [wrongAnnihilator_image]
  change -annihilate j (create j 1) = -1
  rw [annihilate_create]
  simp

/-- The unreversed two-annihilator order has the opposite sign. -/
theorem wrongTwoOrder :
    vacuum ((annihilate 0 * annihilate 1) (word [0,1])) = (-1 : S7) := by
  change vacuum (annihilate 0 (annihilate 1 (create 0 (create 1 1)))) = -1
  rw [annihilate_create]
  norm_num only [show (1 : J) ≠ 0 by decide, ↓reduceIte, zero_smul, zero_sub]
  rw [annihilate_create]
  simp only [↓reduceIte, one_smul, annihilate_vacuum, map_zero, sub_zero,
    map_neg, annihilate_create]
  simp

theorem correctTwoOrder : vacuum (annihilators [0,1] (word [0,1])) = (1 : S7) := by
  apply (annihilators_vacuum_pairing [0,1] [0,1] (by decide) (by decide)).trans
  simp

end HyperbolicSpinor
