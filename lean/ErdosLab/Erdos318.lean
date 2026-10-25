import Challenge.Erdos318

open Erdos318 Set Real Finset

namespace Challenge.Erdos318

theorem solution : statement := by
  intro A hA hA' hP1
  obtain ⟨e, he_set⟩ := Set.ncard_eq_one.mp hA'
  have he_mem : e ∈ {n | n ∈ A \ {0} ∧ Even n} := by
    rw [he_set]
    exact Set.mem_singleton e
  have heA : e ∈ A \ {0} := he_mem.1
  have he_even : Even e := he_mem.2
  have he_ne_zero : e ≠ 0 := by
    intro h0
    exact heA.2 (Set.mem_singleton_iff.mpr h0)
  have h_odd_of_ne : ∀ n ∈ A \ {0}, n ≠ e → Odd n := by
    intro n hnA hne
    rw [← Nat.not_even_iff_odd]
    intro hn_even
    have hn_mem : n ∈ {x | x ∈ A \ {0} ∧ Even x} := ⟨hnA, hn_even⟩
    rw [he_set, Set.mem_singleton_iff] at hn_mem
    exact hne hn_mem
  have hA_diff_inf : ((A \ {0}) \ {e}).Infinite :=
    (hA.diff (Set.finite_singleton 0)).diff (Set.finite_singleton e)
  obtain ⟨m, hm_mem⟩ := hA_diff_inf.nonempty
  have hmA : m ∈ A \ {0} := hm_mem.1
  have hme : m ≠ e := fun h => hm_mem.2 (Set.mem_singleton_iff.mpr h)
  let f : ℕ → ℝ := fun n => if n = e then 1 else -1
  have hf1 : f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) := by
    intro h
    have hm_eq : f m = 1 := congr_fun h ⟨m, hmA⟩
    dsimp [f] at hm_eq
    rw [if_neg hme] at hm_eq
    linarith
  have hf2 : f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => -1) := by
    intro h
    have he_eq : f e = -1 := congr_fun h ⟨e, heA⟩
    dsimp [f] at he_eq
    rw [if_pos rfl] at he_eq
    linarith
  have hf_range : Set.range f ⊆ {1, -1} := by
    rintro x ⟨n, rfl⟩
    dsimp [f]
    by_cases hn : n = e <;> simp [hn]
  obtain ⟨S, hS_ne, hS_sub, hS_sum⟩ := hP1 f hf1 hf2 hf_range
  have hS_ne_zero : ∀ n ∈ S, n ≠ 0 := by
    intro n hnS h0
    exact (hS_sub hnS).2 (Set.mem_singleton_iff.mpr h0)
  by_cases heS : e ∈ S
  · let T := S.erase e
    have h_split := Finset.add_sum_erase S (fun n => f n / (n : ℝ)) heS
    rw [hS_sum] at h_split
    have hfe : f e / (e : ℝ) = 1 / (e : ℝ) := by
      dsimp [f]
      rw [if_pos rfl]
    have hT_congr : ∑ n ∈ T, f n / (n : ℝ) = - ∑ n ∈ T, (1 : ℝ) / (n : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun n hnT => ?_)
      have hne : n ≠ e := Finset.ne_of_mem_erase hnT
      dsimp [f]
      rw [if_neg hne]
      ring
    have h_eq_inv : (1 : ℝ) / (e : ℝ) = ∑ n ∈ T, (1 : ℝ) / (n : ℝ) := by
      linarith [h_split, hfe, hT_congr]
    let P : ℕ := ∏ n ∈ T, n
    have hP_odd : Odd P := by
      refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun n hnT => ?_)
      exact h_odd_of_ne n (hS_sub (Finset.mem_of_mem_erase hnT)) (Finset.ne_of_mem_erase hnT)
    have h_term : ∀ n ∈ T, (P : ℝ) * ((1 : ℝ) / (n : ℝ)) = ((P / n : ℕ) : ℝ) := by
      intro n hnT
      have hn_dvd : n ∣ P := Finset.dvd_prod_of_mem _ hnT
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS_ne_zero n (Finset.mem_of_mem_erase hnT))
      rw [Nat.cast_div hn_dvd hn0]
      ring
    have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he_ne_zero
    have h_mul : (P : ℝ) = (e : ℝ) * ∑ n ∈ T, ((P / n : ℕ) : ℝ) := by
      calc
        (P : ℝ) = (e : ℝ) * (P : ℝ) * ((1 : ℝ) / (e : ℝ)) := by
          field_simp [he0]
        _ = (e : ℝ) * ((P : ℝ) * ∑ n ∈ T, (1 : ℝ) / (n : ℝ)) := by
          rw [h_eq_inv]
          ring
        _ = (e : ℝ) * ∑ n ∈ T, (P : ℝ) * ((1 : ℝ) / (n : ℝ)) := by
          rw [Finset.mul_sum]
        _ = (e : ℝ) * ∑ n ∈ T, ((P / n : ℕ) : ℝ) := by
          rw [Finset.sum_congr rfl h_term]
    have h_nat_eq : P = e * ∑ n ∈ T, (P / n) := by
      exact_mod_cast h_mul
    have hP_even : Even P := by
      rw [h_nat_eq]
      exact he_even.mul_right _
    exact (Nat.not_even_iff_odd.mpr hP_odd) hP_even
  · have h_neg : ∑ n ∈ S, f n / (n : ℝ) < 0 := by
      refine Finset.sum_neg (fun n hnS => ?_) hS_ne
      have hne : n ≠ e := fun h => heS (h ▸ hnS)
      have hn_pos : (0 : ℝ) < (n : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hS_ne_zero n hnS))
      dsimp [f]
      rw [if_neg hne, neg_div]
      linarith [ one_div_pos.mpr hn_pos ]
    linarith [h_neg, hS_sum]

end Challenge.Erdos318
