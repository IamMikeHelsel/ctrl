import Mathlib.Tactic
/-! Finite weak duality for weighted single-class capacity certificates.
The index family may include ordinary residue classes and singleton tail classes.
This theorem proves an obstruction to the declared relaxation, not a covering. -/
set_option autoImplicit false
namespace M02WeightedDuality
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem fractional_cover_obstructs_weighted_bound
    (U : Finset α) (I : Finset β) (S : β → Finset α)
    (lam : β → ℝ) (w : α → ℝ) (cap : β → ℝ) (c : ℝ)
    (hlam : ∀ i∈I, 0≤lam i) (hw : ∀ x∈U, 0≤w x)
    (hcover : ∀ x∈U, c≤∑ i∈I, if x∈S i then lam i else 0)
    (hcap : ∀ i∈I, (∑ x∈U.filter (fun x => x∈S i), w x)≤cap i) :
    c*(∑ x∈U, w x) ≤ ∑ i∈I, lam i*cap i := by
  have he : (∑ x∈U, w x*(∑ i∈I, if x∈S i then lam i else 0)) =
      ∑ i∈I, lam i*(∑ x∈U.filter (fun x => x∈S i), w x) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> ring
  calc
    _ = ∑ x∈U, w x*c := by rw [← Finset.sum_mul]; ring
    _ ≤ ∑ x∈U, w x*(∑ i∈I, if x∈S i then lam i else 0) :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hcover x hx) (hw x hx))
    _ = _ := he
    _ ≤ _ := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hcap i hi) (hlam i hi))

theorem no_strict_weighted_exclusion
    (U : Finset α) (I : Finset β) (S : β → Finset α)
    (lam : β → ℝ) (w : α → ℝ) (cap : β → ℝ) (c : ℝ)
    (hlam : ∀ i∈I, 0≤lam i) (hw : ∀ x∈U, 0≤w x)
    (hcover : ∀ x∈U, c≤∑ i∈I, if x∈S i then lam i else 0)
    (hcap : ∀ i∈I, (∑ x∈U.filter (fun x => x∈S i), w x)≤cap i)
    (hc : 1≤c) : ¬(∑ i∈I, lam i*cap i)<∑ x∈U, w x := by
  have h := fractional_cover_obstructs_weighted_bound U I S lam w cap c hlam hw hcover hcap
  have hs : 0≤∑ x∈U, w x := Finset.sum_nonneg hw
  nlinarith

#print axioms fractional_cover_obstructs_weighted_bound
#print axioms no_strict_weighted_exclusion

/-- Grouped version: a residue-family budget can replace the sum of its
individual coefficients when every member has the same capacity ceiling. A
separate singleton family can represent the unconstrained tail mass. -/
theorem grouped_fractional_budget
    {γ : Type*} [DecidableEq γ]
    (U : Finset α) (G : Finset β) (R : Finset γ) (S : β → γ → Finset α)
    (lam : β → γ → ℝ) (w : α → ℝ) (cap budget : β → ℝ) (c : ℝ)
    (hlam : ∀ g∈G, ∀ r∈R, 0≤lam g r) (hw : ∀ x∈U, 0≤w x)
    (hcover : ∀ x∈U, c≤∑ g∈G, ∑ r∈R, if x∈S g r then lam g r else 0)
    (hcap : ∀ g∈G, ∀ r∈R, (∑ x∈U.filter (fun x => x∈S g r), w x)≤cap g)
    (hcap0 : ∀ g∈G, 0≤cap g)
    (hbudget : ∀ g∈G, (∑ r∈R, lam g r)≤budget g) :
    c*(∑ x∈U, w x) ≤ ∑ g∈G, budget g*cap g := by
  have h := fractional_cover_obstructs_weighted_bound U (G ×ˢ R)
    (fun p => S p.1 p.2) (fun p => lam p.1 p.2) w (fun p => cap p.1) c
    (by intro p hp; rcases Finset.mem_product.mp hp with ⟨hg,hr⟩; exact hlam _ hg _ hr)
    hw (by simpa only [Finset.sum_product] using hcover)
    (by intro p hp; rcases Finset.mem_product.mp hp with ⟨hg,hr⟩; exact hcap _ hg _ hr)
  simp only [Finset.sum_product, ← Finset.sum_mul] at h
  exact h.trans (Finset.sum_le_sum (fun g hg =>
    mul_le_mul_of_nonneg_right (hbudget g hg) (hcap0 g hg)))

#print axioms grouped_fractional_budget
end M02WeightedDuality
