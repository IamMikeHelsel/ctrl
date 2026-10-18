import CompletionBranch
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Adding one vertex increases induced edge count by exactly its current degree. -/
theorem edgeCount_insert
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) {v : V} (hv : v ∉ B) :
    (edgeCountOn G (insert v B) : ℚ) = (edgeCountOn G B : ℚ) +
      ((B.filter fun u => G.Adj v u).card : ℚ) := by
  have hind : G.IsIndepSet (({v} : Finset V) : Set V) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
    exact (hxy (hx.trans hy.symm)).elim
  have heq := independent_extension_cost G B {v}
    (Finset.disjoint_singleton_right.mpr hv) hind
  simpa using heq

/-- The finite greedy-extension stopping statement used in the paper.
A maximum-cardinality feasible extension realizes the same alternative as
successively adding vertices of degree at most k. No algorithm is assumed. -/
theorem exists_greedy_extension
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (t : ℕ) (k : ℚ) (hAt : A.card ≤ t) :
    ∃ B : Finset V, A ⊆ B ∧ B.card ≤ t ∧
      (edgeCountOn G B : ℚ) ≤ (edgeCountOn G A : ℚ) +
        k * ((B.card : ℚ) - (A.card : ℚ)) ∧
      (B.card = t ∨ ∀ v ∉ B, k < ((B.filter fun u => G.Adj v u).card : ℚ)) := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter fun B =>
    A ⊆ B ∧ B.card ≤ t ∧ (edgeCountOn G B : ℚ) ≤
      (edgeCountOn G A : ℚ) + k * ((B.card : ℚ) - (A.card : ℚ))
  have hAF : A ∈ F := by simp [F, hAt]
  obtain ⟨B, hBF, hmax⟩ := F.exists_max_image Finset.card ⟨A, hAF⟩
  have hb := (Finset.mem_filter.mp hBF).2
  refine ⟨B, hb.1, hb.2.1, hb.2.2, ?_⟩
  by_cases hBt : B.card = t
  · exact Or.inl hBt
  right
  intro v hv
  by_contra hn
  have hdegree : ((B.filter fun u => G.Adj v u).card : ℚ) ≤ k := le_of_not_gt hn
  have hcard : (insert v B).card = B.card + 1 := Finset.card_insert_of_notMem hv
  have hcost : (edgeCountOn G (insert v B) : ℚ) ≤
      (edgeCountOn G A : ℚ) + k * (((insert v B).card : ℚ) - (A.card : ℚ)) := by
    rw [edgeCount_insert G B hv, hcard, Nat.cast_add, Nat.cast_one]
    nlinarith [hb.2.2]
  have hCF : insert v B ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hb.1.trans (Finset.subset_insert _ _), by omega, hcost⟩
  have hle := hmax (insert v B) hCF
  omega

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.edgeCount_insert
#print axioms Erdos128.CompletionBridge.exists_greedy_extension
