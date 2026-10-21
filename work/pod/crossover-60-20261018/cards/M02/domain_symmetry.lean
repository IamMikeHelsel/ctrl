import Mathlib.Data.Int.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace M02Symmetry

/-- The two modular-power filters overinclude all admissible prime-minus-one moduli.
Passing them is NOT asserted to prove primality. -/
theorem prime_passes_fermat_filters (m : ℕ) (hm : 4≤m) (hp : (m+1).Prime) :
    2^m % (m+1)=1 ∧ 3^m % (m+1)=1 := by
  have h2 : Nat.Coprime 2 (m+1) :=
    (Nat.coprime_of_lt_prime (by norm_num : (2:ℕ)≠0) (by omega) hp).symm
  have h3 : Nat.Coprime 3 (m+1) :=
    (Nat.coprime_of_lt_prime (by norm_num : (3:ℕ)≠0) (by omega) hp).symm
  have hh2 := Nat.ModEq.pow_card_sub_one_eq_one hp h2
  have hh3 := Nat.ModEq.pow_card_sub_one_eq_one hp h3
  simp only [Nat.add_sub_cancel, Nat.ModEq] at hh2 hh3
  have hp1 : 1<m+1 := by omega
  simpa only [Nat.mod_eq_of_lt hp1] using And.intro hh2 hh3

/-- For any residue, a translation by a multiple of prior stabilizer L moves the
new residue into [0,gcd(L,m)). This is the missing infinite-orbit justification. -/
theorem canonical_residue_exists (L m : ℕ) (hm : 0<m) (a : ℤ) :
    ∃ k b : ℤ, 0≤b ∧ b<(Nat.gcd L m:ℤ) ∧
      Int.ModEq (m:ℤ) (a+(L:ℤ)*k) b := by
  let g : ℤ := Nat.gcd L m
  have hgNat : 0<Nat.gcd L m := Nat.gcd_pos_of_pos_right L hm
  have hg : 0<g := by dsimp [g]; exact_mod_cast hgNat
  refine ⟨-(Nat.gcdA L m)*(a/g), a%g, Int.emod_nonneg _ (ne_of_gt hg),
    Int.emod_lt_of_pos _ hg, ?_⟩
  have hc := (Int.gcd_a_modEq L m).mul_right (a/g)
  have hs := hc.sub_left a
  have he : a-g*(a/g)=a%g := by
    have h := Int.emod_add_ediv_mul a g
    nlinarith
  change Int.ModEq (m:ℤ) (a-(L:ℤ)*Nat.gcdA L m*(a/g)) (a-g*(a/g)) at hs
  rw [he] at hs
  convert hs using 1 <;> ring

/-- Any prior modulus dividing L is unchanged by this translation. -/
theorem previous_class_preserved (n L : ℕ) (hn : n∣L) (x k r : ℤ) :
    Int.ModEq (n:ℤ) (x+(L:ℤ)*k) r ↔ Int.ModEq (n:ℤ) x r := by
  have hcast : (n:ℤ)∣(L:ℤ) := by exact_mod_cast hn
  have hstep : Int.ModEq (n:ℤ) (x+(L:ℤ)*k) x := by
    apply Int.modEq_iff_dvd.mpr
    have hd : (n:ℤ)∣(L:ℤ)*k := dvd_mul_of_dvd_left hcast k
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using dvd_neg.mpr hd
  constructor
  · intro h
    exact hstep.symm.trans h
  · intro h
    exact hstep.trans h

/-- Translating the new class and its tested point preserves membership. -/
theorem translated_new_class (m x a shift b : ℤ)
    (hc : Int.ModEq m (a+shift) b) :
    Int.ModEq m (x+shift) b ↔ Int.ModEq m x a := by
  constructor
  · intro h
    exact (h.trans hc.symm).add_right_cancel' shift
  · intro h
    exact (h.add_right shift).trans hc

#print axioms translated_new_class
#print axioms prime_passes_fermat_filters
#print axioms canonical_residue_exists
#print axioms previous_class_preserved
end M02Symmetry
