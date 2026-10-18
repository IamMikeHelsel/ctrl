import WeightedProfile
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Mantel's bound for the exact induced-edge convention, obtained from
mathlib's checked Turán theorem rather than an external extremal premise. -/
theorem mantel_induced
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3) (F : Finset V) :
    (edgeCountOn G F : ℚ) ≤ (F.card : ℚ) ^ 2 / 4 := by
  classical
  letI : Fintype (F : Set V) := Subtype.fintype _
  have htriF : (G.induce (F : Set V)).CliqueFree 3 :=
    (SimpleGraph.cliqueFree_induce_iff G (F : Set V) 3).mpr htri.cliqueFreeOn
  have hmap := congrArg Finset.card
    (SimpleGraph.map_edgeFinset_induce (s := (F : Set V)) (G := G))
  have hcount : (G.induce (F : Set V)).edgeFinset.card = edgeCountOn G F := by
    simpa [edgeCountOn] using hmap
  have hm := htriF.card_edgeFinset_le (r := 2)
  have hcard : Fintype.card (F : Set V) = F.card := by simp
  rw [SimpleGraph.turanNumber_two, hcard, hcount] at hm
  have hm4 : 4 * edgeCountOn G F ≤ F.card ^ 2 := by omega
  have hmQ : (4 : ℚ) * (edgeCountOn G F : ℚ) ≤ (F.card : ℚ) ^ 2 := by exact_mod_cast hm4
  linarith

/-- The full graph-level cost bound on each Case 2 profile. The final
averaging and scalar optimization are separate; no low-cost existence is
assumed here. -/
theorem weighted_profile_cost_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B D E : Finset V) (w : ℚ) (hw : 0 ≤ w)
    (_hED : E ⊆ D) (hind : G.IsIndepSet (E : Set V))
    (hdegree : ∀ u ∈ D, ((B.filter fun v => G.Adj u v).card : ℚ) ≤ (B.card : ℚ) / 2) :
    edgeCost G (completionProfile B D E w) ≤
      (edgeCountOn G B : ℚ) +
      (∑ z ∈ E, ((B.filter fun v => G.Adj z v).card : ℚ)) +
      w * ((D \ E).card : ℚ) * (B.card : ℚ) / 2 +
      w * ((D \ E).card : ℚ) * (E.card : ℚ) +
      w ^ 2 * ((D \ E).card : ℚ) ^ 2 / 4 := by
  have hBsum : (∑ z ∈ D \ E, ((B.filter fun v => G.Adj z v).card : ℚ)) ≤
      ((D \ E).card : ℚ) * ((B.card : ℚ) / 2) := by
    calc
      _ ≤ ∑ _z ∈ D \ E, (B.card : ℚ) / 2 :=
        Finset.sum_le_sum (fun z hz => hdegree z (Finset.mem_sdiff.mp hz).1)
      _ = _ := by simp
  have hEsum : (∑ z ∈ D \ E, ((E.filter fun v => G.Adj z v).card : ℚ)) ≤
      ((D \ E).card : ℚ) * (E.card : ℚ) := by
    calc
      _ ≤ ∑ _z ∈ D \ E, (E.card : ℚ) := Finset.sum_le_sum (by
        intro z hz
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun v => G.Adj z v) E))
      _ = _ := by simp
  have hBw := mul_le_mul_of_nonneg_left hBsum hw
  have hEw := mul_le_mul_of_nonneg_left hEsum hw
  have hMw := mul_le_mul_of_nonneg_left (mantel_induced G htri (D \ E)) (sq_nonneg w)
  rw [weighted_profile_cost G B D E w hind]
  nlinarith

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.mantel_induced
#print axioms Erdos128.CompletionBridge.weighted_profile_cost_bound
