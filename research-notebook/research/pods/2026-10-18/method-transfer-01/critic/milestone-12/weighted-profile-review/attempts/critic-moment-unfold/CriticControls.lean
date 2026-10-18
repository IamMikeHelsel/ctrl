import ProfileControls

namespace CriticE8
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls
open scoped BigOperators
noncomputable section

def unequal : RatProbabilityWeight (Fin 2) where
  weight := fun v => if v = 0 then 1 / 3 else 2 / 3
  positive := by intro v; fin_cases v <;> norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_succ]

theorem unequal_degrees (v : Fin 2) :
    weightedDegree edge unequal v = if v = 0 then 2 / 3 else 1 / 3 := by
  classical
  fin_cases v <;>
    norm_num [weightedDegree, edge, unequal, SimpleGraph.neighborFinset_eq_filter,
      Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

theorem unequal_moments :
    weightedMean unequal (weightedSecondDegree edge unequal) = 2 / 9 ∧
    weightedMean unequal (fun v => weightedDegree edge unequal v ^ 2) = 2 / 9 ∧
    (weightedMean unequal (weightedDegree edge unequal)) ^ 2 = 16 / 81 := by
  rw [mean_second_degree]
  simp_rw [unequal_degrees]
  norm_num [weightedMean, unequal, Fin.sum_univ_succ]

theorem unequal_candidates :
    IsUnitProfile (lowProfile edge unequal (2 / 3) 1) ∧
    weightedMean unequal (lowProfile edge unequal (2 / 3) 1) = 2 / 3 ∧
    weightedObjective edge unequal (fun _ => 0) (lowProfile edge unequal (2 / 3) 1) = 0 ∧
    weightedObjective edge unequal (fun _ => 0) (highProfile edge unequal (2 / 3) 0) = 1 / 9 := by
  refine ⟨low_profile_unit edge unequal (by norm_num) (by norm_num) 1
    (by rw [unequal_degrees]; norm_num), low_profile_mean edge unequal _ 1, ?_, ?_⟩
  · classical
    norm_num [weightedObjective, weightedMean, lowProfile, twoLevel, indicator,
      weightedDegree, edge, unequal, SimpleGraph.neighborFinset_eq_filter,
      Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]
  · classical
    norm_num [weightedObjective, weightedMean, highProfile, twoLevel, indicator,
      weightedDegree, edge, unequal, SimpleGraph.neighborFinset_eq_filter,
      Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

theorem zero_degree_high_mean :
    weightedMean singletonWeight (highProfile emptyGraph singletonWeight (4 / 5) 0) = 1 := by
  classical
  norm_num [weightedMean, highProfile, twoLevel, indicator, weightedDegree,
    emptyGraph, singletonWeight, SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_filter, Fin.sum_univ_succ]

end
end CriticE8
