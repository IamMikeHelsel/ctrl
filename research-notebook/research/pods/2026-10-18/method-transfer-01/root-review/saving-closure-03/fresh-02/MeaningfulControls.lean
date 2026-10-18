import Erdos128.OneStepSaving

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

namespace SavingReplayControls
open Erdos128
open scoped BigOperators
noncomputable section

def triangle : SimpleGraph (Fin 3) := ⊤

def thirds : RatProbabilityWeight (Fin 3) where
  weight := fun _ => 1 / 3
  positive := by intro v; norm_num
  sum_eq_one := by norm_num

theorem triangle_mean (π : Fin 3 → ℚ) :
    weightedMean thirds π = (π 0 + π 1 + π 2) / 3 := by
  norm_num [weightedMean, thirds, Fin.sum_univ_succ] <;> ring

theorem triangle_cost (π : Fin 3 → ℚ) :
    weightedObjective triangle thirds (fun _ => 0) π =
      (π 0 * π 1 + π 0 * π 2 + π 1 * π 2) / 9 := by
  classical
  norm_num [weightedObjective, triangle, thirds, weightedMean,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Fin.sum_univ_succ] <;> ring

theorem triangle_budget :
    weightedObjective triangle thirds (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
      4 * savingLQ (1 / 2) * edgeMass triangle thirds ^ 3 = 5 / 108 := by
  classical
  norm_num [weightedObjective, triangle, thirds, weightedMean, edgeMass,
    weightedDegree, savingLQ, centerRadiusQ,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

theorem triangle_cost_lower (π : Fin 3 → ℚ)
    (hunit : IsUnitProfile π) (hmean : weightedMean thirds π = 1 / 2) :
    (1 / 18 : ℚ) ≤ weightedObjective triangle thirds (fun _ => 0) π := by
  have h0 := hunit 0
  have h1 := hunit 1
  have h2 := hunit 2
  rw [triangle_mean] at hmean
  have hp : 0 ≤ (1 - π 0) * (1 - π 1) * (1 - π 2) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h1.2))
      (sub_nonneg.mpr h2.2)
  have hq : 0 ≤ π 0 * π 1 * π 2 :=
    mul_nonneg (mul_nonneg h0.1 h1.1) h2.1
  rw [triangle_cost]
  nlinarith

/-- Removing triangle-freeness makes the saving conclusion false, even for
positive probability weights, zero linear term, and alpha=1/2. -/
theorem triangle_refutes_unrestricted_saving :
    ¬ ∃ π : Fin 3 → ℚ,
      IsUnitProfile π ∧ weightedMean thirds π = 1 / 2 ∧
        weightedObjective triangle thirds (fun _ => 0) π ≤
          weightedObjective triangle thirds (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
            4 * savingLQ (1 / 2) * edgeMass triangle thirds ^ 3 := by
  rintro ⟨π, hunit, hmean, hcost⟩
  have hlo := triangle_cost_lower π hunit hmean
  rw [triangle_budget] at hcost
  norm_num at *
  linarith

/-- Two unit masses cannot inhabit the probability-weight input structure. -/
theorem two_unit_masses_not_normalized :
    ¬ ∃ W : RatProbabilityWeight (Fin 2), W.weight = fun _ => 1 := by
  rintro ⟨W, hw⟩
  have hsum := W.sum_eq_one
  rw [hw] at hsum
  norm_num at hsum

def edge : SimpleGraph (Fin 2) := ⊤
def halves : RatProbabilityWeight (Fin 2) where
  weight := fun _ => 1 / 2
  positive := by intro v; norm_num
  sum_eq_one := by norm_num

/-- A real saving is required: the unchanged constant profile fails it on K2. -/
theorem unchanged_profile_does_not_save :
    ¬ weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) ≤
      weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
        4 * savingLQ (1 / 2) * edgeMass edge halves ^ 3 := by
  classical
  norm_num [weightedObjective, edge, halves, weightedMean, edgeMass,
    weightedDegree, savingLQ, centerRadiusQ,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

end
end SavingReplayControls

#print axioms SavingReplayControls.triangle_cost_lower
#print axioms SavingReplayControls.triangle_refutes_unrestricted_saving
#print axioms SavingReplayControls.two_unit_masses_not_normalized
#print axioms SavingReplayControls.unchanged_profile_does_not_save
