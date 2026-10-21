import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace M02JointCapacity
variable {α : Type*} [DecidableEq α]

/-- Maximum is over EVERY pair in the declared candidate families. -/
def jointCapacity (U : Finset α) (X Y : Finset (Finset α)) : ℕ :=
  (X ×ˢ Y).sup (fun pair => (U ∩ (pair.1 ∪ pair.2)).card)

theorem chosen_pair_bound (U A B : Finset α) (X Y : Finset (Finset α))
    (hA : A∈X) (hB : B∈Y) :
    (U ∩ (A∪B)).card ≤ jointCapacity U X Y := by
  unfold jointCapacity
  exact Finset.le_sup (s := X ×ˢ Y) (b := (A,B))
    (f := fun pair : Finset α × Finset α => (U ∩ (pair.1 ∪ pair.2)).card)
    (Finset.mem_product.mpr ⟨hA,hB⟩)

/-- Pair conditioning never weakens the separate maxima bound. -/
theorem joint_le_separate (U : Finset α) (X Y : Finset (Finset α)) :
    jointCapacity U X Y ≤ X.sup (fun A => (U∩A).card)+Y.sup (fun B => (U∩B).card) := by
  apply Finset.sup_le
  intro pair hp
  rcases Finset.mem_product.mp hp with ⟨hA,hB⟩
  rw [Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.le_sup (f := fun A => (U∩A).card) hA) (Finset.le_sup (f := fun B => (U∩B).card) hB))

/-- A uniform unavoidable intersection gives an explicit strict improvement. -/
theorem unavoidable_overlap_discount (U : Finset α) (X Y : Finset (Finset α))
    (K : ℕ) (hk : ∀ A∈X, ∀ B∈Y, K ≤ ((U∩A)∩(U∩B)).card) :
    jointCapacity U X Y ≤
      X.sup (fun A => (U∩A).card)+Y.sup (fun B => (U∩B).card)-K := by
  apply Finset.sup_le
  intro pair hp
  rcases Finset.mem_product.mp hp with ⟨hA,hB⟩
  rw [Finset.inter_union_distrib_left]
  have hc := Finset.card_union_add_card_inter (U∩pair.1) (U∩pair.2)
  have hi := hk pair.1 hA pair.2 hB
  have ha : (U∩pair.1).card ≤ X.sup (fun A => (U∩A).card) := Finset.le_sup (f := fun A => (U∩A).card) hA
  have hb : (U∩pair.2).card ≤ Y.sup (fun B => (U∩B).card) := Finset.le_sup (f := fun B => (U∩B).card) hB
  omega

/-- Joint pair replacement plus a separately justified remaining coverage bound
leaves an actual uncovered point when the budget is strict. C may be rational. -/
theorem strict_joint_budget_leaves_point (U A B T : Finset α)
    (X Y : Finset (Finset α)) (hA : A∈X) (hB : B∈Y) (C : ℝ)
    (hrest : ((U∩T).card:ℝ)≤C)
    (hgap : (jointCapacity U X Y:ℝ)+C<(U.card:ℝ)) :
    (U \ (A∪B∪T)).Nonempty := by
  have hc : (U∩(A∪B∪T)).card ≤ jointCapacity U X Y+(U∩T).card := by
    rw [Finset.inter_union_distrib_left]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (chosen_pair_bound U A B X Y hA hB) le_rfl)
  have hcr : ((U∩(A∪B∪T)).card:ℝ) ≤
      (jointCapacity U X Y:ℝ)+((U∩T).card:ℝ) := by exact_mod_cast hc
  have hlt : ((U∩(A∪B∪T)).card:ℝ)<(U.card:ℝ) := by linarith
  have hltn : (U∩(A∪B∪T)).card<U.card := by exact_mod_cast hlt
  have hs := Finset.card_sdiff_add_card_inter U (A∪B∪T)
  apply Finset.card_pos.mp
  omega

#print axioms chosen_pair_bound
#print axioms joint_le_separate
#print axioms unavoidable_overlap_discount
#print axioms strict_joint_budget_leaves_point
end M02JointCapacity
