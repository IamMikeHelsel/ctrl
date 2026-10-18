module
public import WeightedEntry
@[expose] public section
noncomputable section
namespace CriticLateBox
open LeanControls.DigitalHold LeanControls.WeightedEntry

def testState : State := ![-459/10000,1827/5000,-1818/625]
/-- Algebraic state scope only: no sampled trajectory from this state is claimed. -/
theorem weighted_box_allows_motion :
    (∀ i, |coordinates 0 testState i| ≤ weight i*target) ∧
    weightedRadius (coordinates 0 testState) = target ∧ 0 < testState 1 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [coordinates,testState,weight,target]
  · norm_num [weightedRadius,coordinates,testState,target]
end CriticLateBox
