import Research.CoveringCapacity
import Research.CoveringCRT
import Research.CoveringMass
import Research.CoveringTail

/-! Assembly of the seven-smooth exclusion. AI-assisted research, October2026.
All substantive assumptions remain explicit; no external solver is trusted. -/

namespace Research.CoveringAssembly

set_option maxRecDepth 4096

open CoveringCapacity CoveringMass CoveringTail

def modulus (x : Exponents) : ℕ :=
  2 ^ (x.1.1 + 1) * 3 ^ x.1.2 * 5 ^ x.2.1 * 7 ^ x.2.2

theorem modulus_pos (x : Exponents) : 0 < modulus x := by
  unfold modulus
  positivity

theorem weight_eq_reciprocal (x : Exponents) : weight x = 1 / (modulus x : ℝ) := by
  simp [weight, modulus, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]

def pool : Finset ℕ := remainderBox.toFinset

def groups : Finset ℕ := {4, 6, 10, 12, 20, 30, 60}

def massBound (g : ℕ) : ℕ :=
  if g = 4 then 120 else if g = 6 then 101 else if g = 10 then 21 else
  if g = 12 then 85 else if g = 20 then 47 else if g = 30 then 56 else
  if g = 60 then 40 else 0

theorem pool_exact (m : ℕ) (h : m ∈ pool) : 0 < m ∧ denominator % m = 0 := by
  apply grid_division_exact m
  have hm : m ∈ remainderBox := List.mem_toFinset.mp h
  exact (List.mem_filter.mp hm).1

theorem pool_groups (m : ℕ) (h : m ∈ pool) : m.gcd 60 ∈ groups := by
  have := gcd_groups_complete m (List.mem_toFinset.mp h)
  simpa [groups] using this

/-- Finset version of the integer certificate; independently reduced in the kernel. -/
theorem pool_integer_bound : ∀ g ∈ groups,
    1000 * (∑ m ∈ pool.filter (fun m => m.gcd 60 = g), denominator / m) ≤
      massBound g * denominator := by
  set_option maxRecDepth 4096 in decide +kernel

attribute [irreducible] pool

theorem pool_reciprocal_bound (g : ℕ) (hg : g ∈ groups) :
    ∑ m ∈ pool.filter (fun m => m.gcd 60 = g), (1 / (m : ℝ)) ≤
      (massBound g : ℝ) / 1000 := by
  have hd : (0 : ℝ) < denominator := by norm_num [denominator]
  have hi := pool_integer_bound g hg
  have hdiv (m : ℕ) (hm : m ∈ pool) :
      (1 / (m : ℝ)) = (denominator / m : ℕ) / (denominator : ℝ) := by
    have hp := pool_exact m hm
    have he : denominator / m * m = denominator :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hp.2)
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
    have he' : (denominator / m : ℕ) * (m : ℝ) = (denominator : ℝ) := by
      exact_mod_cast he
    apply (div_eq_div_iff hm' hd.ne').mpr
    simpa only [one_mul] using he'.symm
  calc
    _ = (∑ m ∈ pool.filter (fun m => m.gcd 60 = g),
        ((denominator / m : ℕ) : ℝ)) / (denominator : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m hm
      exact hdiv m (Finset.mem_filter.mp hm).1
    _ ≤ _ := by
      apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 1000)).mpr
      have hi' : 1000 * (∑ m ∈ pool.filter (fun m => m.gcd 60 = g),
          ((denominator / m : ℕ) : ℝ)) ≤ (massBound g : ℝ) * denominator := by
        exact_mod_cast hi
      simpa only [mul_comm] using hi'

theorem pool_capacity_bound (U : Finset (Fin 60)) :
    (∑ m ∈ pool, (m.gcd 60 : ℝ) * fiberCapacity U (m.gcd 60) / (m : ℝ)) + 300 / 1000 ≤
      (scaledRemainderCapacity U : ℝ) / 1000 := by
  have hgroup :
      (∑ m ∈ pool, (m.gcd 60 : ℝ) * fiberCapacity U (m.gcd 60) / (m : ℝ)) =
      ∑ g ∈ groups, (g : ℝ) * fiberCapacity U g *
        (∑ m ∈ pool.filter (fun m => m.gcd 60 = g), (1 / (m : ℝ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun m hm => pool_groups m hm)]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [(Finset.mem_filter.mp hm).2]
    ring
  have hb : (∑ m ∈ pool, (m.gcd 60 : ℝ) * fiberCapacity U (m.gcd 60) / (m : ℝ)) ≤
      ∑ g ∈ groups, (g : ℝ) * fiberCapacity U g * ((massBound g : ℝ) / 1000) := by
    rw [hgroup]
    apply Finset.sum_le_sum
    intro g hg
    exact mul_le_mul_of_nonneg_left (pool_reciprocal_bound g hg)
      (mul_nonneg (Nat.cast_nonneg g) (Nat.cast_nonneg _))
  have hl := large_fibers_bounded U
  have h20 : (fiberCapacity U 20 : ℝ) ≤ 3 := by exact_mod_cast hl.1
  have h30 : (fiberCapacity U 30 : ℝ) ≤ 2 := by exact_mod_cast hl.2.1
  have h60 : (fiberCapacity U 60 : ℝ) ≤ 1 := by exact_mod_cast hl.2.2
  norm_num [groups, massBound, Finset.sum_insert, Finset.sum_singleton] at hb
  simp only [scaledRemainderCapacity, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

#print axioms pool_capacity_bound
#print axioms pool_integer_bound
#print axioms pool_reciprocal_bound
#print axioms weight_eq_reciprocal

end Research.CoveringAssembly
