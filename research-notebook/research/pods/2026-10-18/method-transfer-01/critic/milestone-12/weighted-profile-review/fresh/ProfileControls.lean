import WeightedProfiles

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

namespace Erdos128.ProfileControls
open Erdos128.ProfileBridge
open scoped BigOperators
noncomputable section

def edge : SimpleGraph (Fin 2) := ⊤
def halves : RatProbabilityWeight (Fin 2) where
  weight := fun _ => 1 / 2
  positive := by intro v; norm_num
  sum_eq_one := by norm_num

theorem edge_triangle_free : edge.CliqueFree 3 :=
  edge.cliqueFree_of_card_lt (by norm_num)

theorem edge_degree (v : Fin 2) : weightedDegree edge halves v = 1 / 2 := by
  classical
  fin_cases v <;>
    norm_num [weightedDegree, edge, halves, SimpleGraph.neighborFinset_eq_filter,
      Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

theorem edge_second (v : Fin 2) : weightedSecondDegree edge halves v = 1 / 4 := by
  classical
  unfold weightedSecondDegree
  simp_rw [edge_degree]
  rw [← Finset.sum_mul]
  change weightedDegree edge halves v * (1 / 2) = 1 / 4
  rw [edge_degree]
  norm_num

theorem edge_mass : edgeMass edge halves = 1 / 4 := by
  unfold edgeMass weightedMean
  simp_rw [edge_degree]
  norm_num [halves, Fin.sum_univ_succ]

theorem edge_low_certificate (d : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 - (4 / 5 : ℚ)) :
    edgeMass edge halves - ((3 / 20 : ℚ) / (4 / 5 : ℚ) ^ 2) * (1 - d) ^ 2 - d ^ 2 ≤
      (-1 / 2 : ℚ) * (d - 2 * edgeMass edge halves) := by
  rw [edge_mass]
  norm_num at *
  nlinarith [sq_nonneg d]

theorem edge_high_certificate (d : ℚ) :
    d * (edgeMass edge halves - (3 / 20 : ℚ)) / (1 - (4 / 5 : ℚ)) - d ^ 2 ≤
      (-1 / 2 : ℚ) * (d - 2 * edgeMass edge halves) := by
  rw [edge_mass]
  norm_num
  nlinarith [sq_nonneg (d - 1 / 2)]

/-- Nonzero K2 instance of the full graph-to-profile endpoint. -/
theorem edge_affine_instance :
    ∃ π : Fin 2 → ℚ, IsUnitProfile π ∧ weightedMean halves π = 4 / 5 ∧
      weightedObjective edge halves (fun _ => 0) π ≤ 3 / 20 := by
  apply exists_affine_profile edge halves edge_triangle_free (4 / 5) (3 / 20) (-1 / 2)
    (by norm_num) (by norm_num)
  · exact edge_low_certificate
  · intro d _ _
    exact edge_high_certificate d

theorem edge_explicit_high_values :
    highProfile edge halves (4 / 5) 0 0 = 1 ∧
      highProfile edge halves (4 / 5) 0 1 = 3 / 5 := by
  classical
  simp only [highProfile, twoLevel, edge_degree]
  norm_num [indicator, edge]

theorem edge_explicit_high_profile :
    IsUnitProfile (highProfile edge halves (4 / 5) 0) ∧
      weightedMean halves (highProfile edge halves (4 / 5) 0) = 4 / 5 ∧
      weightedObjective edge halves (fun _ => 0) (highProfile edge halves (4 / 5) 0) = 3 / 20 := by
  refine ⟨high_profile_unit edge halves (by norm_num) (by norm_num) 0
    (by rw [edge_degree]; norm_num), ?_, ?_⟩
  · exact high_profile_mean edge halves _ 0 (by rw [edge_degree]; norm_num)
  · rw [high_profile_cost edge halves edge_triangle_free, edge_mass, edge_second, edge_degree]
    norm_num

theorem edge_branch_boundary :
    lowProfile edge halves (1 / 2) 0 = highProfile edge halves (1 / 2) 0 ∧
      IsUnitProfile (lowProfile edge halves (1 / 2) 0) ∧
      weightedMean halves (lowProfile edge halves (1 / 2) 0) = 1 / 2 ∧
      weightedObjective edge halves (fun _ => 0) (lowProfile edge halves (1 / 2) 0) = 0 := by
  refine ⟨profile_boundary edge halves (by norm_num) (by norm_num) 0
    (by rw [edge_degree]; norm_num), ?_, low_profile_mean edge halves _ 0, ?_⟩
  · exact low_profile_unit edge halves (by norm_num) (by norm_num) 0
      (by rw [edge_degree]; norm_num)
  · rw [low_profile_cost edge halves edge_triangle_free, edge_mass, edge_second]
    norm_num

def emptyGraph : SimpleGraph (Fin 1) := ⊥
def singletonWeight : RatProbabilityWeight (Fin 1) where
  weight := fun _ => 1
  positive := by intro v; norm_num
  sum_eq_one := by norm_num

theorem isolated_zero_degree :
    weightedDegree emptyGraph singletonWeight 0 = 0 ∧
      IsUnitProfile (lowProfile emptyGraph singletonWeight (4 / 5) 0) ∧
      weightedMean singletonWeight (lowProfile emptyGraph singletonWeight (4 / 5) 0) = 4 / 5 ∧
      weightedObjective emptyGraph singletonWeight (fun _ => 0)
        (lowProfile emptyGraph singletonWeight (4 / 5) 0) = 0 := by
  have hd : weightedDegree emptyGraph singletonWeight 0 = 0 := by
    classical
    norm_num [weightedDegree, emptyGraph, SimpleGraph.neighborFinset_eq_filter,
      Finset.sum_filter, Fin.sum_univ_succ]
  refine ⟨hd, ?_, low_profile_mean emptyGraph singletonWeight _ 0, ?_⟩
  · exact low_profile_unit emptyGraph singletonWeight (by norm_num) (by norm_num) 0
      (by rw [hd]; norm_num)
  · classical
    norm_num [weightedObjective, weightedMean, emptyGraph,
      SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Fin.sum_univ_succ]

/-- The branch restriction is substantive: the low profile is not feasible
on K2 at alpha=4/5, where d=1/2 is larger than b=1/5. -/
theorem wrong_low_branch_not_unit :
    ¬ IsUnitProfile (lowProfile edge halves (4 / 5) 0) := by
  intro h
  have h0 := (h 0).2
  classical
  simp only [lowProfile, twoLevel, edge_degree] at h0
  norm_num [indicator, edge] at h0

theorem unscaled_complement_has_wrong_mean :
    weightedMean halves (fun v : Fin 2 => if v = 0 then 4 / 5 else 0) = 2 / 5 ∧
      weightedMean halves (fun v : Fin 2 => if v = 0 then 4 / 5 else 0) ≠ 4 / 5 := by
  norm_num [weightedMean, halves, Fin.sum_univ_succ]

theorem two_unit_masses_not_probability :
    ¬ ∃ W : RatProbabilityWeight (Fin 2), W.weight = fun _ => 1 := by
  rintro ⟨W, hw⟩
  have hs := W.sum_eq_one
  rw [hw] at hs
  norm_num at hs

def triangle : SimpleGraph (Fin 3) := ⊤
def thirds : RatProbabilityWeight (Fin 3) where
  weight := fun _ => 1 / 3
  positive := by intro v; norm_num
  sum_eq_one := by norm_num

theorem triangle_mass : edgeMass triangle thirds = 1 / 3 := by
  classical
  norm_num [edgeMass, weightedMean, weightedDegree, triangle, thirds,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ]

theorem triangle_affine_low (d : ℚ) :
    edgeMass triangle thirds - ((0 : ℚ) / (1 / 2 : ℚ) ^ 2) * (1 - d) ^ 2 - d ^ 2 ≤
      (-2 / 3 : ℚ) * (d - 2 * edgeMass triangle thirds) := by
  rw [triangle_mass]
  norm_num
  nlinarith [sq_nonneg (d - 1 / 3)]

theorem triangle_affine_high (d : ℚ) :
    d * (edgeMass triangle thirds - (0 : ℚ)) / (1 - (1 / 2 : ℚ)) - d ^ 2 ≤
      (-2 / 3 : ℚ) * (d - 2 * edgeMass triangle thirds) := by
  rw [triangle_mass]
  norm_num
  nlinarith [sq_nonneg (d - 2 / 3)]

theorem triangle_mean (π : Fin 3 → ℚ) :
    weightedMean thirds π = (π 0 + π 1 + π 2) / 3 := by
  norm_num [weightedMean, thirds, Fin.sum_univ_succ] <;> ring

theorem triangle_cost (π : Fin 3 → ℚ) :
    weightedObjective triangle thirds (fun _ => 0) π =
      (π 0 * π 1 + π 0 * π 2 + π 1 * π 2) / 9 := by
  classical
  norm_num [weightedObjective, triangle, thirds, weightedMean,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne, Fin.sum_univ_succ] <;> ring

/-- This lower-bound proof is reused from the E3 semantic control, separately
rebuilt here against the actual new endpoint's alpha=1/2,T=0 test. -/
theorem triangle_half_cost_lower (π : Fin 3 → ℚ)
    (hu : IsUnitProfile π) (hm : weightedMean thirds π = 1 / 2) :
    (1 / 18 : ℚ) ≤ weightedObjective triangle thirds (fun _ => 0) π := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  rw [triangle_mean] at hm
  have hp : 0 ≤ (1 - π 0) * (1 - π 1) * (1 - π 2) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h1.2))
      (sub_nonneg.mpr h2.2)
  have hq : 0 ≤ π 0 * π 1 * π 2 :=
    mul_nonneg (mul_nonneg h0.1 h1.1) h2.1
  rw [triangle_cost]
  nlinarith

/-- Both scalar certificate branches above hold on K3, but the conclusion
at alpha=1/2,T=0 fails. Thus triangle-freeness cannot be dropped. -/
theorem triangle_refutes_missing_triangle_free :
    ¬ ∃ π : Fin 3 → ℚ, IsUnitProfile π ∧ weightedMean thirds π = 1 / 2 ∧
      weightedObjective triangle thirds (fun _ => 0) π ≤ 0 := by
  rintro ⟨π, hu, hm, hc⟩
  have hlo := triangle_half_cost_lower π hu hm
  linarith

def triangleHalf (v : Fin 3) : ℚ :=
  if v = 0 then 1 else if v = 1 then 1 / 2 else 0

theorem triangle_exact_min_witness :
    IsUnitProfile triangleHalf ∧ weightedMean thirds triangleHalf = 1 / 2 ∧
      weightedObjective triangle thirds (fun _ => 0) triangleHalf = 1 / 18 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    fin_cases v <;> norm_num [triangleHalf]
  · rw [triangle_mean]
    norm_num [triangleHalf]
  · rw [triangle_cost]
    norm_num [triangleHalf]

end
end Erdos128.ProfileControls
