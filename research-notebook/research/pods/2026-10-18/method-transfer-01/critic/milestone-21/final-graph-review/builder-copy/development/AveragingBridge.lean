import CompletionBranch
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Exact weighted double-counting for the neighborhood profiles in Case 2.
This is an equality on graph incidences, before any scalar bounds or averaging. -/
theorem weighted_neighborhood_double_count
    (G : SimpleGraph V) [DecidableRel G.Adj] (B D : Finset V) (f : V → ℚ) :
    (∑ v ∈ B, ∑ z ∈ D.filter (fun z => G.Adj v z), f z) =
      ∑ z ∈ D, ((B.filter fun v => G.Adj z v).card : ℚ) * f z := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hp (v : V) : (if G.Adj v z then f z else 0) =
      (if G.Adj z v then (1 : ℚ) else 0) * f z := by
    by_cases h : G.Adj z v
    · simp [h, G.adj_comm]
    · simp [h, G.adj_comm]
  simp_rw [hp]
  rw [← Finset.sum_mul]
  congr 1
  simp [Finset.sum_boole]

/-- Summing the neighborhood sizes counts every B--D incidence once. -/
theorem neighborhood_size_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (B D : Finset V) :
    (∑ v ∈ B, ((D.filter fun z => G.Adj v z).card : ℚ)) =
      ∑ z ∈ D, ((B.filter fun v => G.Adj z v).card : ℚ) := by
  simpa using weighted_neighborhood_double_count G B D (fun _ => 1)

/-- The total actual B-to-neighborhood cross cost is the sum of squared
B-degrees. This is the second-moment identity used by the paper's averaging. -/
theorem neighborhood_cross_cost_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (B D : Finset V) :
    (∑ v ∈ B, 2 * edgeBilin G
      (finsetIndicator (D.filter fun z => G.Adj v z)) (finsetIndicator B)) =
      ∑ z ∈ D, ((B.filter fun v => G.Adj z v).card : ℚ) ^ 2 := by
  simp_rw [cross_indicator_eq_degree_sum]
  simpa [pow_two] using weighted_neighborhood_double_count G B D
    (fun z => ((B.filter fun v => G.Adj z v).card : ℚ))

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.weighted_neighborhood_double_count
#print axioms Erdos128.CompletionBridge.neighborhood_size_sum
#print axioms Erdos128.CompletionBridge.neighborhood_cross_cost_sum
