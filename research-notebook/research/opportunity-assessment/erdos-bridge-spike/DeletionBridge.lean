import Erdos128.GraphBasics
set_option maxHeartbeats 1000000

/-! A graph-level component of the deletion/completion argument for sparse halves.
The imported upstream definitions use rational fractional weights and unordered
simple-graph edges, each counted once. No completion theorem is assumed as an
axiom: the transfer result takes an explicit fractional-half existence premise.
-/

namespace Erdos128.DeletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def pairWeight (x : V → ℚ) : Sym2 V → ℚ :=
  Sym2.lift ⟨fun a b => x a * x b, fun _ _ => mul_comm _ _⟩

theorem edgeCost_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    edgeCost G x = ∑ e ∈ G.edgeFinset, pairWeight x e := by
  unfold edgeCost edgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
    change (x a * x b + x b * x a) / 2 = x a * x b
    ring

theorem pairWeight_bounds {x : V → ℚ} (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1)
    (e : Sym2 V) : 0 ≤ pairWeight x e ∧ pairWeight x e ≤ 1 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    change 0 ≤ x a * x b ∧ x a * x b ≤ 1
    exact ⟨mul_nonneg (hx a).1 (hx b).1,
      (mul_le_mul (hx a).2 (hx b).2 (hx b).1 (by norm_num)).trans_eq (by norm_num)⟩

/-- Delete precisely the original edges with both endpoints in X.
Vertices, the fractional profile, and its total mass are unchanged. -/
def deleteInside (G : SimpleGraph V) (X : Finset V) : SimpleGraph V :=
  G.deleteEdges (X.sym2 : Set (Sym2 V))

instance (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    DecidableRel (deleteInside G X).Adj := by
  unfold deleteInside
  infer_instance

theorem deleteInside_independent (G : SimpleGraph V) (X : Finset V) :
    (deleteInside G X).IsIndepSet (X : Set V) := by
  intro a ha b hb hab hadj
  have hd := SimpleGraph.deleteEdges_adj.mp hadj
  exact hd.2 (by simpa only [Finset.mem_coe, Finset.mk_mem_sym2_iff] using And.intro ha hb)

theorem deleteInside_cliqueFree (G : SimpleGraph V) (X : Finset V) {k : ℕ}
    (hG : G.CliqueFree k) : (deleteInside G X).CliqueFree k :=
  SimpleGraph.CliqueFree.anti (SimpleGraph.deleteEdges_le _) hG

/-- Exact restoration identity, before using any bound on fractional weights. -/
theorem restoration_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x : V → ℚ) :
    edgeCost G x = edgeCost (deleteInside G X) x +
      ∑ e ∈ G.edgeFinset ∩ X.sym2, pairWeight x e := by
  classical
  have hed : (deleteInside G X).edgeFinset = G.edgeFinset \ X.sym2 := by
    ext e
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset, Finset.mem_sdiff]
    change e ∈ (G.deleteEdges (X.sym2 : Set (Sym2 V))).edgeSet ↔
      e ∈ G.edgeSet ∧ e ∉ X.sym2
    rw [SimpleGraph.edgeSet_deleteEdges]
    rfl
  rw [edgeCost_eq_sum G x, edgeCost_eq_sum (deleteInside G X) x, hed]
  exact (Finset.sum_inter_add_sum_sdiff G.edgeFinset X.sym2 (pairWeight x)).symm.trans
    (add_comm _ _)

/-- Restoring internal edges costs at most their count for weights in [0,1].
This holds for every finite simple graph; triangle-freeness is unnecessary. -/
theorem restoration_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) {x : V → ℚ} (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1) :
    edgeCost G x ≤ edgeCost (deleteInside G X) x + (edgeCountOn G X : ℚ) := by
  rw [restoration_identity G X x]
  have hs : (∑ e ∈ G.edgeFinset ∩ X.sym2, pairWeight x e) ≤ (edgeCountOn G X : ℚ) := by
   calc
    (∑ e ∈ G.edgeFinset ∩ X.sym2, pairWeight x e) ≤
        ∑ _e ∈ G.edgeFinset ∩ X.sym2, (1 : ℚ) :=
      Finset.sum_le_sum (fun e _ => (pairWeight_bounds hx e).2)
    _ = (edgeCountOn G X : ℚ) := by simp [edgeCountOn]
  exact add_le_add le_rfl hs

/-- A fractional-half witness for the deleted graph is still a fractional half
of the original graph, with an explicit and exact restoration-cost allowance.
The difficult completion theorem must supply hcompletion separately. -/
theorem restore_fractional_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) {B : ℚ}
    (hcompletion : HasFractionalHalfBound (deleteInside G X) B) :
    HasFractionalHalfBound G (B + (edgeCountOn G X : ℚ)) := by
  obtain ⟨x, hx, hcost⟩ := hcompletion
  exact ⟨x, hx, (restoration_bound G X hx.1).trans (add_le_add hcost le_rfl)⟩

end
end Erdos128.DeletionBridge

#print axioms Erdos128.DeletionBridge.edgeCost_eq_sum
#print axioms Erdos128.DeletionBridge.pairWeight_bounds
#print axioms Erdos128.DeletionBridge.deleteInside_independent
#print axioms Erdos128.DeletionBridge.deleteInside_cliqueFree
#print axioms Erdos128.DeletionBridge.restoration_identity
#print axioms Erdos128.DeletionBridge.restoration_bound
#print axioms Erdos128.DeletionBridge.restore_fractional_half
