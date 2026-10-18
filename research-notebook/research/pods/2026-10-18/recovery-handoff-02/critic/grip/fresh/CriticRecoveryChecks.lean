import RecoveryWitness
open Set LeanControls.Recovery
namespace IndependentRecoveryCritic
example : travelBudget (1/100) 0 0 1 8 = (729/80000:ℝ) := by
 norm_num [travelBudget,velocityBudget]
example : travelBudget (1/100) 0 0 1 8 < travelBudget (1/100) 0 0 2 8 := by
 norm_num [travelBudget,velocityBudget]
example : travelBudget 0 0 0 1 8 = (1/128:ℝ) := by
 norm_num [travelBudget,velocityBudget]
example : Witness.state 1 = ![(1:ℝ),1,0] := by norm_num [Witness.state,coast]
example {t : ℝ} (ht : t ≤ 1) : Witness.state t 1 = 1 ∧ Witness.state t 2 = 0 := by
 simp [Witness.state,ht,coast]
example : Witness.state 3 1 < 0 := by
 norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
 positivity
example : Witness.state 3 1 = -Real.exp (-2) := by
 norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
 ring
example : ¬ (∀ t : ℝ, 0 ≤ Witness.state t 1) := by
 intro h
 have hn : Witness.state 3 1 < 0 := by
  norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
  positivity
 linarith [h 3]
end IndependentRecoveryCritic
