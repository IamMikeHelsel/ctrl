import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Counting bridge for conditional covering capacities. AI-assisted research. -/

namespace Research.CoveringCRT

/-- A periodic set occupies exactly the same fraction of every multiple of its
period. This gives the denominator for the conditional-capacity comparison. -/
theorem lift_card (B k : ℕ) (hB : 0 < B) (U : Finset ℕ)
    (hU : ∀ r ∈ U, r < B) :
    ((Finset.range (k * B)).filter fun x => x % B ∈ U).card = U.card * k := by
  classical
  let D := (Finset.range (k * B)).filter fun x => x % B ∈ U
  let T := U ×ˢ Finset.range k
  have hc : D.card = T.card := by
    apply Finset.card_bij (fun x _ => (x % B, x / B))
    · intro x hx
      obtain ⟨hr, hu⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_product.mpr ⟨hu, Finset.mem_range.mpr
        ((Nat.div_lt_iff_lt_mul hB).mpr (Finset.mem_range.mp hr))⟩
    · intro x hx y hy heq
      have hmod := congrArg Prod.fst heq
      have hdiv := congrArg Prod.snd heq
      have hxid := Nat.mod_add_div x B
      have hyid := Nat.mod_add_div y B
      dsimp at hmod hdiv
      rw [hmod, hdiv] at hxid
      omega
    · intro y hy
      obtain ⟨r, t⟩ := y
      obtain ⟨hr, ht⟩ := Finset.mem_product.mp hy
      have hrl := hU r hr
      have htl := Finset.mem_range.mp ht
      refine ⟨r + B * t, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_range.mpr
          nlinarith
        · simpa [Nat.add_mod, Nat.mod_eq_of_lt hrl] using hr
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hrl, Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt hrl]
  simpa [D, T, Finset.card_product] using hc

/-- Intersecting a periodic surviving set with one congruence class. The bound
retains the gcd-compatible fiber; independence is neither assumed nor needed. -/
theorem conditional_class_card_le
    (B m k a : ℕ) (hB : 0 < B) (hm : 0 < m) (U : Finset ℕ) :
    ((Finset.range (k * B.lcm m)).filter fun x => x % B ∈ U ∧ x % m = a).card ≤
      (U.filter fun r => r % B.gcd m = a % B.gcd m).card * k := by
  classical
  let l := B.lcm m
  let g := B.gcd m
  have hl : 0 < l := Nat.lcm_pos hB hm
  let D := (Finset.range (k * l)).filter fun x => x % B ∈ U ∧ x % m = a
  let T := (U.filter fun r => r % g = a % g) ×ˢ Finset.range k
  have mapped : Set.MapsTo (fun x => (x % B, x / l)) D T := by
    intro x hx
    obtain ⟨hr, hu, ha⟩ := Finset.mem_filter.mp hx
    have hxlt : x < k * l := Finset.mem_range.mp hr
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨hu, ?_⟩
      calc
        (x % B) % g = x % g := Nat.mod_mod_of_dvd x (Nat.gcd_dvd_left B m)
        _ = (x % m) % g := (Nat.mod_mod_of_dvd x (Nat.gcd_dvd_right B m)).symm
        _ = a % g := by rw [ha]
    · exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hl).mpr hxlt)
  have inj : Set.InjOn (fun x => (x % B, x / l)) D := by
    intro x hx y hy heq
    have hxb := congrArg Prod.fst heq
    have hdiv := congrArg Prod.snd heq
    have hxm := (Finset.mem_filter.mp hx).2.2
    have hym := (Finset.mem_filter.mp hy).2.2
    have hmod : x % l = y % l := Nat.mod_lcm hxb (hxm.trans hym.symm)
    have hxid := Nat.mod_add_div x l
    have hyid := Nat.mod_add_div y l
    dsimp at hdiv
    rw [hdiv, hmod] at hxid
    omega
  have hc := Finset.card_le_card_of_injOn (fun x => (x % B, x / l)) mapped inj
  simpa [D, T, Finset.card_product] using hc

#print axioms conditional_class_card_le
#print axioms lift_card

end Research.CoveringCRT
