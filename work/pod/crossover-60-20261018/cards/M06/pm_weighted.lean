import Mathlib.Tactic
namespace CampaignM06Weighted
open scoped BigOperators
def labels : List Nat := [0,3,5,6,9,10,12,15,17,18,20,23,24,27,29,30]
def edges : List (Nat × Nat) := [(0,7),(0,11),(0,13),(0,14),(0,15),(1,6),(1,10),(1,12),(1,14),(1,15),(2,5),(2,9),(2,12),(2,13),(2,15),(3,4),(3,8),(3,12),(3,13),(3,14),(4,9),(4,10),(4,11),(4,15),(5,8),(5,10),(5,11),(5,14),(6,8),(6,9),(6,11),(6,13),(7,8),(7,9),(7,10),(7,12),(8,15),(9,14),(10,13),(11,12)]
def bit (v : Fin 16) (k : Fin 5) : Bool := (labels[v.val]!).testBit k.val
def Adj (u v : Fin 16) : Prop := (u.val,v.val)∈edges ∨ (v.val,u.val)∈edges
instance (u v : Fin 16) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ ∨ _))
theorem nat_identity : ∀ u v : Fin 16, Adj u v → (∑ k : Fin 5, if bit u k = bit v k then (1:Nat) else 0) = 1 := by decide
theorem real_identity (u v : Fin 16) (h : Adj u v) :
 (∑ k : Fin 5, if bit u k = bit v k then (1:ℝ) else 0) = 1 := by
 have hn := nat_identity u v h
 exact_mod_cast hn
theorem weighted_identity {ι : Type} [Fintype ι] (w : ι → ℝ) (u v : ι → Fin 16)
 (h : ∀ i, Adj (u i) (v i)) :
 (∑ k : Fin 5, ∑ i, w i * (if bit (u i) k = bit (v i) k then (1:ℝ) else 0)) = ∑ i, w i := by
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro i hi
 rw [← Finset.mul_sum, real_identity _ _ (h i), mul_one]
theorem finite_average (cost : Fin 5 → ℝ) (m : ℝ) (h : ∑ k, cost k = m) :
 ∃ k, cost k ≤ m/5 := by
 by_contra hn
 push_neg at hn
 have hs : ∑ k : Fin 5, m/5 < ∑ k : Fin 5, cost k := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i hi => hn i)
 norm_num at hs
 linarith
end CampaignM06Weighted
#print axioms CampaignM06Weighted.nat_identity
#print axioms CampaignM06Weighted.real_identity
#print axioms CampaignM06Weighted.weighted_identity
#print axioms CampaignM06Weighted.finite_average
