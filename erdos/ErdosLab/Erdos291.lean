import Challenge.Erdos291

/-!
# Erdős Problem 291 (Part ii: Infinitely Many $n$ with $\gcd(a_n, L_n) > 1$)

We prove `Erdos291.erdos_291.parts.ii` by formalizing Steinerberger's base-3 construction:
for every $m \ge 1$ and $n = 2 \cdot 3^m$, both $L_n = \operatorname{lcm}_{1 \le k \le n} k$ and
$a_n = \sum_{k=1}^n L_n / k$ are divisible by $3$, so $3 \mid \gcd(a_n, L_n)$ and hence
$\gcd(a_n, L_n) \ge 3 > 1$ for infinitely many $n$.
-/

open Erdos291 Finset

namespace Challenge.Erdos291

private theorem not_dvd_of_ne (m k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ 2 * 3 ^ m)
    (hk_ne1 : k ≠ 3 ^ m) (hk_ne2 : k ≠ 2 * 3 ^ m) : ¬ (3 ^ m ∣ k) := by
  rintro ⟨c, rfl⟩
  have h3m_pos : 0 < 3 ^ m := Nat.pow_pos (by decide)
  have hc_pos : 1 ≤ c := by
    by_contra h
    have hc0 : c = 0 := by omega
    subst hc0
    omega
  have hc_le : c ≤ 2 := by
    by_contra h
    have hc3 : 3 ≤ c := by omega
    have : 3 * 3 ^ m ≤ 3 ^ m * c := by
      rw [Nat.mul_comm (3 ^ m) c]
      exact Nat.mul_le_mul_right (3 ^ m) hc3
    omega
  interval_cases c
  · exact hk_ne1 (Nat.mul_one (3 ^ m))
  · exact hk_ne2 (Nat.mul_comm (3 ^ m) 2)

private theorem three_dvd_term (m k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ 2 * 3 ^ m)
    (hk_ne1 : k ≠ 3 ^ m) (hk_ne2 : k ≠ 2 * 3 ^ m) :
    3 ∣ L (2 * 3 ^ m) / k := by
  set n := 2 * 3 ^ m
  have hk_mem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
  have hk_dvd : k ∣ L n := Finset.dvd_lcm hk_mem
  have hn_mem : n ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]
    have : 0 < 3 ^ m := Nat.pow_pos (by decide)
    omega
  have hn_dvd : n ∣ L n := Finset.dvd_lcm hn_mem
  have h3m_dvd_L : 3 ^ m ∣ L n := dvd_trans ⟨2, by ring⟩ hn_dvd
  by_contra h3_not_dvd
  have hcop3 : Nat.Coprime 3 (L n / k) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3_not_dvd
  have hcop3m : Nat.Coprime (3 ^ m) (L n / k) := hcop3.pow_left m
  have h3m_dvd_prod : 3 ^ m ∣ (L n / k) * k := by
    rw [Nat.div_mul_cancel hk_dvd]
    exact h3m_dvd_L
  have h3m_dvd_k : 3 ^ m ∣ k := hcop3m.dvd_of_dvd_mul_left h3m_dvd_prod
  exact not_dvd_of_ne m k hk1 hkn hk_ne1 hk_ne2 h3m_dvd_k

theorem three_dvd_gcd_two_mul_three_pow (m : ℕ) (hm : 1 ≤ m) :
    3 ∣ Nat.gcd (a (2 * 3 ^ m)) (L (2 * 3 ^ m)) := by
  set n := 2 * 3 ^ m
  have h3m_pos : 0 < 3 ^ m := Nat.pow_pos (by decide)
  have h3_dvd_3m : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
  have hn_mem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hn_dvd_L : n ∣ L n := Finset.dvd_lcm hn_mem
  have h3_dvd_L : 3 ∣ L n :=
    dvd_trans h3_dvd_3m (dvd_trans ⟨2, by ring⟩ hn_dvd_L)
  refine Nat.dvd_gcd ?_ h3_dvd_L
  have h3m_mem : 3 ^ m ∈ (Finset.Icc 1 n).erase n := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨?_, by omega, by omega⟩
    dsimp [n]
    omega
  unfold a
  rw [← Finset.add_sum_erase _ _ hn_mem, ← Finset.add_sum_erase _ _ h3m_mem, ← add_assoc]
  refine dvd_add ?_ ?_
  · obtain ⟨q, hq⟩ := hn_dvd_L
    have hq1 : L n / n = q := by
      rw [hq, Nat.mul_div_right q (by omega)]
    have hq2 : L n / 3 ^ m = 2 * q := by
      have hrew : L n = 3 ^ m * (2 * q) := by
        calc L n = (2 * 3 ^ m) * q := hq
          _ = 3 ^ m * (2 * q) := by ring
      rw [hrew, Nat.mul_div_right (2 * q) h3m_pos]
    rw [hq1, hq2]
    exact ⟨q, by ring⟩
  · refine Finset.dvd_sum fun k hk => ?_
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hk
    rcases hk with ⟨hk_ne1, hk_ne2, hk1, hkn⟩
    exact three_dvd_term m k hk1 hkn hk_ne1 hk_ne2

theorem solution : statement := by
  let f : ℕ → ℕ := fun k => 2 * 3 ^ (k + 1)
  have hf_mono : StrictMono f := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    dsimp [f]
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self (k + 1))) (by decide)
  refine Set.infinite_of_injective_forall_mem hf_mono.injective fun k => ?_
  dsimp [f]
  have h3_dvd := three_dvd_gcd_two_mul_three_pow (k + 1) (by omega)
  have hL_pos : 0 < L (2 * 3 ^ (k + 1)) := by
    have h_ne : L (2 * 3 ^ (k + 1)) ≠ 0 := by
      unfold L
      rw [Finset.lcm_ne_zero_iff]
      intro x hx
      rw [Finset.mem_Icc] at hx
      omega
    omega
  have hgcd_pos : 0 < Nat.gcd (a (2 * 3 ^ (k + 1))) (L (2 * 3 ^ (k + 1))) :=
    Nat.gcd_pos_of_pos_right _ hL_pos
  have h3_le : 3 ≤ Nat.gcd (a (2 * 3 ^ (k + 1))) (L (2 * 3 ^ (k + 1))) :=
    Nat.le_of_dvd hgcd_pos h3_dvd
  omega

end Challenge.Erdos291
