import Challenge.Erdos382
import Mathlib.NumberTheory.Bertrand

/-!
# Erdős Problem 382 (`lt_two_mul_of_largestPrimeRepeated`)

We prove `Erdos382.lt_two_mul_of_largestPrimeRepeated`: if $1 \le u \le v$, $2 \le v$, and
$(\mathrm{maxPrimeFac}(\prod_{m \in [u, v]} m))^2 \mid \prod_{m \in [u, v]} m$, then $v < 2 u$.
-/

open Erdos382 Finset

namespace Challenge.Erdos382

theorem lt_two_mul_of_largestPrimeRepeated {u v : ℕ} (h : LargestPrimeRepeated u v) :
    v < 2 * u := by
  rcases h with ⟨hu, huv, hv, hp_sq⟩
  set P := ∏ m ∈ Finset.Icc u v, m
  set p := Nat.maxPrimeFac P
  by_contra h_not_lt
  have h_ge : 2 * u ≤ v := by omega
  obtain ⟨q, hq_prime, hq_gt, hq_le_two⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (v / 2) (by omega)
  have hq_le_v : q ≤ v := le_trans hq_le_two (Nat.mul_div_le v 2)
  have hq_ge_u : u ≤ q := by omega
  have hq_mem : q ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hq_ge_u, hq_le_v⟩
  have hq_dvd_P : q ∣ P := Finset.dvd_prod_of_mem _ hq_mem
  have hP_pos : 0 < P := by
    refine Finset.prod_pos fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    omega
  have hqp : q ≤ p := Nat.le_maxPrimeFac (Nat.ne_of_gt hP_pos) hq_prime hq_dvd_P
  have hv_lt_2p : v < 2 * p := by omega
  have hP_gt_1 : 1 < P := by
    have hq_ge_2 : 2 ≤ q := hq_prime.two_le
    have hq_le_P : q ≤ P := Nat.le_of_dvd hP_pos hq_dvd_P
    omega
  have hp_prime : p.Prime := Nat.prime_maxPrimeFac_of_one_lt P hP_gt_1
  have hp_dvd_P : p ∣ P := dvd_trans ⟨p, by ring⟩ hp_sq
  rw [Prime.dvd_finsetProd_iff hp_prime.prime] at hp_dvd_P
  obtain ⟨m₀, hm₀_mem, hpm₀⟩ := hp_dvd_P
  have hm₀_eq_p : m₀ = p := by
    rcases hpm₀ with ⟨c, rfl⟩
    rw [Finset.mem_Icc] at hm₀_mem
    have hc_pos : 1 ≤ c := by
      by_contra hc0
      have : c = 0 := by omega
      subst this
      omega
    have hc_le_1 : c ≤ 1 := by
      by_contra hc2
      have : 2 * p ≤ p * c := by
        rw [Nat.mul_comm p c]
        exact Nat.mul_le_mul_right p (by omega)
      omega
    have hc1 : c = 1 := by omega
    rw [hc1, Nat.mul_one]
  rw [hm₀_eq_p] at hm₀_mem
  dsimp [P] at hp_sq
  rw [← Finset.mul_prod_erase _ _ hm₀_mem, sq,
      mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp_prime),
      Prime.dvd_finsetProd_iff hp_prime.prime] at hp_sq
  obtain ⟨m₁, hm₁_mem, hpm₁⟩ := hp_sq
  rw [Finset.mem_erase, Finset.mem_Icc] at hm₁_mem
  rcases hm₁_mem with ⟨hm₁_ne_p, hm₁_ge_u, hm₁_le_v⟩
  rcases hpm₁ with ⟨c, rfl⟩
  have hc_pos : 1 ≤ c := by
    by_contra hc0
    have : c = 0 := by omega
    subst this
    omega
  have hc_ge_2 : 2 ≤ c := by
    by_contra hc1
    have : c = 1 := by omega
    subst this
    exact hm₁_ne_p (Nat.mul_one p)
  have : 2 * p ≤ p * c := by
    rw [Nat.mul_comm p c]
    exact Nat.mul_le_mul_right p hc_ge_2
  omega

theorem solution : statement := fun h => lt_two_mul_of_largestPrimeRepeated h

end Challenge.Erdos382
