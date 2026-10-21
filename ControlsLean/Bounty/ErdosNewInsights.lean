/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-!
# New Erdős Problem Solutions, Extremal Certificates & Structural Insights

This module extends `ControlsLean.Bounty.ErdosBounties` with complete, machine-checked,
standard-axiom-only Lean 4 formalizations across five additional Erdős problems
from Google DeepMind's *Formal Conjectures* repository:

1. **Erdős Problem #370** (`Erdos370`):
   - Complete formalization of `maxPrimeFac` and its multiplicative/power laws.
   - `erdos_370_dyadic_family`: Explicit infinite dyadic family $n_k = 2^{4k+6} - 1$ for which
     $\operatorname{maxPrimeFac}(n_k + 1) = 2 < \sqrt{n_k + 1}$ is constant and
     $\operatorname{maxPrimeFac}(n_k) \le 2^{2k+3} - 1 < \sqrt{n_k}$.
   - `erdos_370`: Exact solution of `Erdos370.erdos_370` (`{ n | (maxPrimeFac n : ℝ) < √n ∧
     (maxPrimeFac (n + 1) : ℝ) < √(n + 1) }.Infinite`).

2. **Erdős Problem #645** (`Erdos645`):
   - `erdos_645_bounded_47`: Quantitative finite-horizon theorem proving that every 2-coloring
     $c : \mathbb{N} \to \mathrm{Bool}$ admits a monochromatic 3-term arithmetic progression
     $x, x + d, x + 2d$ with $0 < x < d$ and $x + 2d \le 47$ (via an explicit 28-split decision
     tree inspecting only 20 integers).
   - `erdos_645`: Exact solution of `Erdos645.erdos_645`.

3. **Erdős Problem #493** (`Erdos493`):
   - `erdos_493`: Exact solution of `Erdos493.erdos_493` ($\exists k N, \forall n \ge N,
     \exists a : \operatorname{Fin} k \to \mathbb{Z}, (\forall i, 2 \le a_i) \wedge
     \prod a_i - \sum a_i = n$).
   - `erdos_493_strictMono_k_two`: Strengthened representation with strictly increasing factors
     $2 \le a_0 < a_1$ for every $n \ge 1$.
   - `erdos_493_two_factors_ge_three_iff`: Exact algebraic obstruction when $a_0, a_1 \ge 3$:
     $n = a_0 a_1 - (a_0 + a_1)$ with $a_0, a_1 \ge 3$ iff $n + 1$ is composite ($b_0 b_1$ with
     $b_0, b_1 \ge 2$).

4. **Erdős Problem #275** (`Erdos275`):
   - `erdos_275_dyadic_covers_Icc`: For every $r \ge 1$, the dyadic congruence system
     $x \equiv 2^i \pmod{2^{i+1}}$ ($i \in \operatorname{Fin} r$) covers all $2^r - 1$
     consecutive integers in $[1, 2^r - 1]$.
   - `erdos_275_dyadic_misses_zero` & `erdos_275_dyadic_misses_two_pow`: Neither $0$ nor $2^r$
     is covered, certifying the sharpness of the Crittenden–Vanden Eynden threshold $2^r$.

5. **Erdős Problems #873 & #1125** (`Erdos873`, `Erdos1125`):
   - `erdos_873_lcm_ge_add`: For any strictly monotone positive sequence $a : \mathbb{N} \to \mathbb{N}$
     and $k \ge 1$, $\operatorname{lcm}_{m < k} a(i + m) \ge a(i + k - 1) \ge i + k$.
   - `erdos_1125_kemperman_exists_monotone_chain`: Under Kemperman's inequality
     $2 f(x) \le f(x + h) + f(x + 2h)$, every $x \in \mathbb{R}$ and $h > 0$ generates an
     unbounded step sequence $x_m \ge x + m h$ along which $f(x_m)$ is non-decreasing.
-/

namespace ControlsLean.Bounty

open Finset

/-! ## 1. Erdős Problem #370: Greatest Prime Factor of $n$ and $n + 1$ Below $\sqrt{n}$ -/

/-- The greatest prime divisor of $n > 1$, taking the value $0$ at $n = 0$ and $1$ at $n = 1$
(matching `Nat.maxPrimeFac` in Google DeepMind's `formal-conjectures`). -/
def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

@[simp]
theorem maxPrimeFac_zero : maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac, List.getLastI]

@[simp]
theorem maxPrimeFac_one : maxPrimeFac 1 = 1 := rfl

theorem prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Nat.Prime (maxPrimeFac n) := by
  have hn : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Nat.Prime (n.primeFactorsList.getLast hn) :=
    Nat.prime_of_mem_primeFactorsList hmem
  simpa [maxPrimeFac, h.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hn] using hprime

theorem maxPrimeFac_dvd : ∀ {n : ℕ}, maxPrimeFac n ∣ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have hn : 1 < n + 2 := by omega
    have hlist : (n + 2).primeFactorsList ≠ [] :=
      (Nat.primeFactorsList_ne_nil (n + 2)).2 hn
    have hmem : (n + 2).primeFactorsList.getLast hlist ∈ (n + 2).primeFactorsList :=
      List.getLast_mem hlist
    have hdvd : (n + 2).primeFactorsList.getLast hlist ∣ n + 2 :=
      Nat.dvd_of_mem_primeFactorsList hmem
    simpa [maxPrimeFac, hn.ne', List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd

theorem le_maxPrimeFac {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hn_one : n ≠ 1 := ((Nat.primeFactorsList_ne_nil n).1 hlist).ne'
  have hp_last : p ≤ n.primeFactorsList.getLast hlist :=
    (Nat.primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxPrimeFac, hn_one, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using hp_last

theorem maxPrimeFac_le : ∀ {n : ℕ}, maxPrimeFac n ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => Nat.le_of_dvd (by omega) maxPrimeFac_dvd

theorem maxPrimeFac_eq_self_of_prime {p : ℕ} (hp : p.Prime) :
    maxPrimeFac p = p :=
  le_antisymm maxPrimeFac_le (le_maxPrimeFac hp.pos.ne' hp (dvd_refl p))

theorem maxPrimeFac_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · have hle : 1 ≤ maxPrimeFac n := by
      obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
      · simp
      · exact (prime_maxPrimeFac_of_one_lt n hn_lt).one_lt.le
    simp [hle]
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · have hle : 1 ≤ maxPrimeFac m := (prime_maxPrimeFac_of_one_lt m hm_lt).one_lt.le
    simp [hle]
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨Nat.zero_lt_of_lt hm_lt, Nat.zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Nat.Prime (maxPrimeFac (m * n)) := prime_maxPrimeFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp maxPrimeFac_dvd with hpm | hpn
    · exact (le_maxPrimeFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxPrimeFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Nat.Prime (maxPrimeFac m) := prime_maxPrimeFac_of_one_lt m hm_lt
      exact le_maxPrimeFac (mul_ne_zero hm hn) hp (dvd_mul_of_dvd_left maxPrimeFac_dvd n)
    · have hp : Nat.Prime (maxPrimeFac n) := prime_maxPrimeFac_of_one_lt n hn_lt
      exact le_maxPrimeFac (mul_ne_zero hm hn) hp (dvd_mul_of_dvd_right maxPrimeFac_dvd m)

@[simp]
theorem maxPrimeFac_pow {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    maxPrimeFac (n ^ k) = maxPrimeFac n :=
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n; simp
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
      simp

/-- For every $k \in \mathbb{N}$, $3 \mid (2^{2k+3} + 1)$. -/
theorem erdos_370_three_dvd_two_pow_odd_add_one (k : ℕ) :
    3 ∣ 2 ^ (2 * k + 3) + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rcases ih with ⟨m, hm⟩
    refine ⟨4 * m - 1, ?_⟩
    have hpow : 2 ^ (2 * (k + 1) + 3) = 4 * 2 ^ (2 * k + 3) := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, pow_add]
      ring
    omega

/-- The explicit dyadic sequence $n_k = 2^{4k+6} - 1$ for Erdős Problem #370. -/
def erdos370DyadicSeq (k : ℕ) : ℕ := 2 ^ (4 * k + 6) - 1

theorem erdos370DyadicSeq_strictMono : StrictMono erdos370DyadicSeq := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold erdos370DyadicSeq
  have h1 : 1 ≤ 2 ^ (4 * k + 6) := Nat.one_le_pow _ _ (by decide)
  have h2 : 2 ^ (4 * k + 6) < 2 ^ (4 * (k + 1) + 6) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

/-- **Erdős #370 Quantitative Dyadic Bound**:
For every $k \in \mathbb{N}$ and $n = 2^{4k+6} - 1$:
1. $\operatorname{maxPrimeFac}(n + 1) = 2$, and
2. $\operatorname{maxPrimeFac}(n) \le 2^{2k+3} - 1$. -/
theorem erdos_370_dyadic_bounds (k : ℕ) :
    maxPrimeFac (erdos370DyadicSeq k + 1) = 2 ∧
      maxPrimeFac (erdos370DyadicSeq k) ≤ 2 ^ (2 * k + 3) - 1 := by
  set e := 2 * k + 3
  set X := 2 ^ e
  have hX_ge : 8 ≤ X := by
    dsimp [X]
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
  have h2e : 2 ^ (4 * k + 6) = X * X := by
    dsimp [X]
    rw [← pow_add]
    congr 1
    omega
  have hXX_ge : 64 ≤ X * X := by nlinarith
  have h_succ : erdos370DyadicSeq k + 1 = 2 ^ (4 * k + 6) := by
    unfold erdos370DyadicSeq
    omega
  refine ⟨?_, ?_⟩
  · rw [h_succ, maxPrimeFac_pow (by omega) 2]
    exact maxPrimeFac_eq_self_of_prime Nat.prime_two
  · -- Factor X * X - 1 = (X - 1) * (X + 1)
    have h_fac : erdos370DyadicSeq k = (X - 1) * (X + 1) := by
      unfold erdos370DyadicSeq
      rw [h2e]
      obtain ⟨Y, hY⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
      rw [hY]
      have h_id : (Y + 1) * (Y + 1) = (Y + 1 - 1) * (Y + 1 + 1) + 1 := by
        simp only [Nat.add_sub_cancel]
        ring
      omega
    rw [h_fac, maxPrimeFac_mul (by omega) (by omega)]
    refine max_le maxPrimeFac_le ?_
    obtain ⟨m, hm⟩ := erdos_370_three_dvd_two_pow_odd_add_one k
    have hm' : X + 1 = 3 * m := hm
    have hm_ne : m ≠ 0 := by omega
    have hm_le : m ≤ X - 1 := by omega
    rw [hm', maxPrimeFac_mul (by decide) hm_ne]
    have h3 : maxPrimeFac 3 = 3 := maxPrimeFac_eq_self_of_prime Nat.prime_three
    rw [h3]
    refine max_le (by omega) ?_
    exact maxPrimeFac_le.trans hm_le

/-- **Erdős Problem #370 (`erdos_370`)**:
There are infinitely many $n \in \mathbb{N}$ such that $\operatorname{maxPrimeFac}(n) < \sqrt{n}$
and $\operatorname{maxPrimeFac}(n + 1) < \sqrt{n + 1}$. -/
theorem erdos_370 :
    { n : ℕ | (maxPrimeFac n : ℝ) < Real.sqrt n ∧
      (maxPrimeFac (n + 1) : ℝ) < Real.sqrt (n + 1) }.Infinite := by
  refine Set.infinite_of_injective_forall_mem erdos370DyadicSeq_strictMono.injective fun k => ?_
  obtain ⟨h_succ, h_n⟩ := erdos_370_dyadic_bounds k
  set e := 2 * k + 3
  set X := 2 ^ e
  have hX_ge : 8 ≤ X := by
    dsimp [X]
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
  have h2e : 2 ^ (4 * k + 6) = X * X := by
    dsimp [X]
    rw [← pow_add]
    congr 1
    omega
  have h_sq_lt : (X - 1) ^ 2 < erdos370DyadicSeq k := by
    unfold erdos370DyadicSeq
    rw [h2e]
    obtain ⟨Y, hY⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
    have hY_ge : 7 ≤ Y := by omega
    rw [hY]
    simp only [Nat.add_sub_cancel]
    have h_id : (Y + 1) * (Y + 1) - 1 = Y ^ 2 + 2 * Y := by
      have : (Y + 1) * (Y + 1) = Y ^ 2 + 2 * Y + 1 := by ring
      omega
    rw [h_id]
    omega
  have h_succ_gt : 4 < erdos370DyadicSeq k + 1 := by
    unfold erdos370DyadicSeq
    have hXX : 64 ≤ 2 ^ (4 * k + 6) := by
      rw [h2e]
      nlinarith
    omega
  refine ⟨?_, ?_⟩
  · have hle : (maxPrimeFac (erdos370DyadicSeq k) : ℝ) ≤ ((X - 1 : ℕ) : ℝ) := by
      exact_mod_cast h_n
    refine lt_of_le_of_lt hle ?_
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast h_sq_lt
  · rw [h_succ]
    rw [Real.lt_sqrt (by positivity)]
    have h4 : ((2 : ℕ) : ℝ) ^ 2 < (erdos370DyadicSeq k : ℝ) + 1 := by
      push_cast
      have : (4 : ℝ) < (erdos370DyadicSeq k : ℝ) + 1 := by exact_mod_cast h_succ_gt
      linarith
    exact h4

/-! ## 2. Erdős Problem #645: Monochromatic 3-APs $x, x + d, x + 2d$ with $d > x$ -/

private lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- **Erdős Problem #645 Quantitative Horizon Certificate (`erdos_645_bounded_47`)**:
For every 2-coloring $c : \mathbb{N} \to \mathrm{Bool}$, there exist positive integers $x, d$
with $0 < x < d$ and $x + 2d \le 47$ such that $x, x + d, x + 2d$ are monochromatic. -/
theorem erdos_645_bounded_47 (c : ℕ → Bool) :
    ∃ x d : ℕ, 0 < x ∧ x < d ∧ x + 2 * d ≤ 47 ∧
      ∃ C : Bool, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C := by
  rcases eq_or_ne (c 15) (c 1) with h15 | h15
  · rcases eq_or_ne (c 29) (c 1) with h29 | h29
    · exact ⟨1, 14, by decide, by decide, by decide, c 1, rfl, h15, h29⟩
    · rcases eq_or_ne (c 11) (c 1) with h11 | h11
      · rcases eq_or_ne (c 7) (c 1) with h7 | h7
        · rcases eq_or_ne (c 3) (c 1) with h3 | h3
          · exact ⟨3, 4, by decide, by decide, by decide, c 1, h3, h7, h11⟩
          · rcases eq_or_ne (c 8) (c 1) with h8 | h8
            · exact ⟨1, 7, by decide, by decide, by decide, c 1, rfl, h8, h15⟩
            · rcases eq_or_ne (c 13) (c 1) with h13 | h13
              · exact ⟨1, 6, by decide, by decide, by decide, c 1, rfl, h7, h13⟩
              · exact ⟨3, 5, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h3, bool_eq_not_of_ne h8, bool_eq_not_of_ne h13⟩
        · rcases eq_or_ne (c 21) (c 1) with h21 | h21
          · exact ⟨1, 10, by decide, by decide, by decide, c 1, rfl, h11, h21⟩
          · rcases eq_or_ne (c 18) (c 1) with h18 | h18
            · rcases eq_or_ne (c 35) (c 1) with h35 | h35
              · exact ⟨1, 17, by decide, by decide, by decide, c 1, rfl, h18, h35⟩
              · exact ⟨7, 14, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h7, bool_eq_not_of_ne h21, bool_eq_not_of_ne h35⟩
            · exact ⟨7, 11, by decide, by decide, by decide, !c 1,
                bool_eq_not_of_ne h7, bool_eq_not_of_ne h18, bool_eq_not_of_ne h29⟩
      · rcases eq_or_ne (c 47) (c 1) with h47 | h47
        · rcases eq_or_ne (c 19) (c 1) with h19 | h19
          · rcases eq_or_ne (c 24) (c 1) with h24 | h24
            · exact ⟨1, 23, by decide, by decide, by decide, c 1, rfl, h24, h47⟩
            · rcases eq_or_ne (c 37) (c 1) with h37 | h37
              · exact ⟨1, 18, by decide, by decide, by decide, c 1, rfl, h19, h37⟩
              · exact ⟨11, 13, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h11, bool_eq_not_of_ne h24, bool_eq_not_of_ne h37⟩
          · rcases eq_or_ne (c 3) (c 1) with h3 | h3
            · rcases eq_or_ne (c 9) (c 1) with h9 | h9
              · exact ⟨3, 6, by decide, by decide, by decide, c 1, h3, h9, h15⟩
              · exact ⟨9, 10, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h9, bool_eq_not_of_ne h19, bool_eq_not_of_ne h29⟩
            · exact ⟨3, 8, by decide, by decide, by decide, !c 1,
                bool_eq_not_of_ne h3, bool_eq_not_of_ne h11, bool_eq_not_of_ne h19⟩
        · exact ⟨11, 18, by decide, by decide, by decide, !c 1,
            bool_eq_not_of_ne h11, bool_eq_not_of_ne h29, bool_eq_not_of_ne h47⟩
  · rcases eq_or_ne (c 5) (c 1) with h5 | h5
    · rcases eq_or_ne (c 3) (c 1) with h3 | h3
      · exact ⟨1, 2, by decide, by decide, by decide, c 1, rfl, h3, h5⟩
      · rcases eq_or_ne (c 9) (c 1) with h9 | h9
        · exact ⟨1, 4, by decide, by decide, by decide, c 1, rfl, h5, h9⟩
        · exact ⟨3, 6, by decide, by decide, by decide, !c 1,
            bool_eq_not_of_ne h3, bool_eq_not_of_ne h9, bool_eq_not_of_ne h15⟩
    · rcases eq_or_ne (c 25) (c 1) with h25 | h25
      · rcases eq_or_ne (c 17) (c 1) with h17 | h17
        · rcases eq_or_ne (c 3) (c 1) with h3 | h3
          · rcases eq_or_ne (c 31) (c 1) with h31 | h31
            · exact ⟨3, 14, by decide, by decide, by decide, c 1, h3, h17, h31⟩
            · rcases eq_or_ne (c 47) (c 1) with h47 | h47
              · exact ⟨3, 22, by decide, by decide, by decide, c 1, h3, h25, h47⟩
              · exact ⟨15, 16, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h15, bool_eq_not_of_ne h31, bool_eq_not_of_ne h47⟩
          · rcases eq_or_ne (c 9) (c 1) with h9 | h9
            · exact ⟨1, 8, by decide, by decide, by decide, c 1, rfl, h9, h17⟩
            · exact ⟨3, 6, by decide, by decide, by decide, !c 1,
                bool_eq_not_of_ne h3, bool_eq_not_of_ne h9, bool_eq_not_of_ne h15⟩
        · rcases eq_or_ne (c 13) (c 1) with h13 | h13
          · exact ⟨1, 12, by decide, by decide, by decide, c 1, rfl, h13, h25⟩
          · rcases eq_or_ne (c 11) (c 1) with h11 | h11
            · rcases eq_or_ne (c 21) (c 1) with h21 | h21
              · exact ⟨1, 10, by decide, by decide, by decide, c 1, rfl, h11, h21⟩
              · exact ⟨5, 8, by decide, by decide, by decide, !c 1,
                  bool_eq_not_of_ne h5, bool_eq_not_of_ne h13, bool_eq_not_of_ne h21⟩
            · exact ⟨5, 6, by decide, by decide, by decide, !c 1,
                bool_eq_not_of_ne h5, bool_eq_not_of_ne h11, bool_eq_not_of_ne h17⟩
      · exact ⟨5, 10, by decide, by decide, by decide, !c 1,
          bool_eq_not_of_ne h5, bool_eq_not_of_ne h15, bool_eq_not_of_ne h25⟩

/-- **Erdős Problem #645 (`erdos_645`)**:
In any 2-coloring of $\mathbb{N}$, there exists a monochromatic 3-term arithmetic progression
$x, x + d, x + 2d$ with $0 < x < d$. -/
theorem erdos_645 (c : ℕ → Bool) :
    ∃ x d, 0 < x ∧ x < d ∧ (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) := by
  obtain ⟨x, d, hx, hd, -, hC⟩ := erdos_645_bounded_47 c
  exact ⟨x, d, hx, hd, hC⟩

/-! ## 3. Erdős Problem #493: Representations $n = \prod_{i=1}^k a_i - \sum_{i=1}^k a_i$ -/

/-- **Erdős Problem #493 (`erdos_493`)**:
There exist $k \in \mathbb{N}$ and $N \in \mathbb{Z}$ such that every integer $n \ge N$ can be
written as $\prod_{i=1}^k a_i - \sum_{i=1}^k a_i$ for some integers $a_i \ge 2$. -/
theorem erdos_493 :
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  refine ⟨2, 0, fun n hn => ⟨![2, n + 2], ?_, ?_⟩⟩
  · intro i
    fin_cases i
    · simp
    · simp [hn]
  · simp [Fin.prod_univ_two, Fin.sum_univ_two]
    ring

/-- **Erdős #493 Strengthened Distinct-Factor Theorem**:
Every integer $n \ge 1$ admits a strictly increasing pair $2 \le a_0 < a_1$ such that
$a_0 a_1 - (a_0 + a_1) = n$. -/
theorem erdos_493_strictMono_k_two (n : ℤ) (hn : 1 ≤ n) :
    ∃ a : Fin 2 → ℤ,
      StrictMono a ∧ (∀ i : Fin 2, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin 2, a i) - (∑ i : Fin 2, a i) = n := by
  refine ⟨![2, n + 2], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (lt_irrefl _ hij).elim
    · simp; omega
    · exact ( Nat.not_lt_zero _ hij ).elim
    · exact (lt_irrefl _ hij).elim
  · intro i
    fin_cases i
    · simp
    · simp; omega
  · simp [Fin.prod_univ_two, Fin.sum_univ_two]
    ring

/-- **Erdős #493 Obstruction for Factors $\ge 3$**:
An integer $n$ can be written as $a_0 a_1 - (a_0 + a_1)$ with $a_0, a_1 \ge 3$ if and only if
$n + 1 = b_0 b_1$ is composite ($b_0, b_1 \ge 2$). -/
theorem erdos_493_two_factors_ge_three_iff (n : ℤ) :
    (∃ a₀ a₁ : ℤ, 3 ≤ a₀ ∧ 3 ≤ a₁ ∧ a₀ * a₁ - (a₀ + a₁) = n) ↔
      ∃ b₀ b₁ : ℤ, 2 ≤ b₀ ∧ 2 ≤ b₁ ∧ b₀ * b₁ = n + 1 := by
  constructor
  · rintro ⟨a₀, a₁, ha₀, ha₁, h_eq⟩
    refine ⟨a₀ - 1, a₁ - 1, by omega, by omega, ?_⟩
    linarith
  · rintro ⟨b₀, b₁, hb₀, hb₁, h_eq⟩
    refine ⟨b₀ + 1, b₁ + 1, by omega, by omega, ?_⟩
    linarith

/-! ## 4. Erdős Problem #275: Extremal Sharpness of the Dyadic Covering System -/

/-- **Erdős #275 Dyadic Coverage of $[1, 2^r - 1]$**:
For every $r \ge 1$ and every integer $x \in [1, 2^r - 1]$, there exists $i \in \operatorname{Fin} r$
such that $x \equiv 2^i \pmod{2^{i+1}}$. -/
theorem erdos_275_dyadic_covers_Icc :
    ∀ (r : ℕ) (x : ℕ), 1 ≤ x → x ≤ 2 ^ r - 1 →
      ∃ i : Fin r, x ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)]
  | 0, x, hx1, hx2 => by simp at hx2; omega
  | r + 1, x, hx1, hx2 => by
    rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
    · -- x = 2 * k is even, so 1 ≤ k ≤ 2^r - 1
      have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ 2 ^ r - 1 := by
        rw [pow_succ'] at hx2
        omega
      obtain ⟨j, hj⟩ := erdos_275_dyadic_covers_Icc r k hk1 hk2
      refine ⟨j.succ, ?_⟩
      change (2 * k) % 2 ^ (j.val + 1 + 1) = 2 ^ (j.val + 1) % 2 ^ (j.val + 1 + 1)
      have h1 : (2 * k) % 2 ^ (j.val + 1 + 1) = 2 * (k % 2 ^ (j.val + 1)) := by
        rw [pow_succ' 2 (j.val + 1), Nat.mul_mod_mul_left]
      have h2 := Nat.mul_mod_mul_left 2 (2 ^ j.val) (2 ^ (j.val + 1))
      rw [← pow_succ' 2 (j.val + 1), ← pow_succ' 2 j.val] at h2
      rw [h1, h2]
      exact congr_arg (2 * ·) hj
    · -- x = 2 * k + 1 is odd, covered by i = 0 (1 mod 2)
      refine ⟨⟨0, Nat.succ_pos r⟩, ?_⟩
      change (2 * k + 1) % 2 = 1 % 2
      omega

/-- **Erdős #275 Dyadic Uncovered Multiples of $2^r$**:
No multiple of $2^r$ (in particular $0$ or $2^r$) satisfies $x \equiv 2^i \pmod{2^{i+1}}$
for any $i \in \operatorname{Fin} r$. -/
theorem erdos_275_dyadic_misses_mul (r m : ℕ) (i : Fin r) :
    ¬ (m * 2 ^ r ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)]) := by
  intro hmod
  have hi_le : i.val + 1 ≤ r := i.isLt
  have hdvd : 2 ^ (i.val + 1) ∣ m * 2 ^ r :=
    dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hi_le) m
  have hmod_zero : (m * 2 ^ r) % 2 ^ (i.val + 1) = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hpow_lt : 2 ^ i.val < 2 ^ (i.val + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self i.val)
  have hpow_mod : (2 ^ i.val) % 2 ^ (i.val + 1) = 2 ^ i.val :=
    Nat.mod_eq_of_lt hpow_lt
  change (m * 2 ^ r) % 2 ^ (i.val + 1) = (2 ^ i.val) % 2 ^ (i.val + 1) at hmod
  rw [hmod_zero, hpow_mod] at hmod
  have hpos : 0 < 2 ^ i.val := Nat.pow_pos (by decide)
  omega

/-- **Erdős Problem #275 Extremal Sharpness Certificate**:
For every $r \ge 1$, the system of $r$ congruences $a_i = 2^i \pmod{2^{i+1}}$ ($i \in \operatorname{Fin} r$)
covers all $2^r - 1$ consecutive integers in $[1, 2^r - 1]$, yet fails to cover $0$ and $2^r$,
proving that the Crittenden–Vanden Eynden threshold $2^r$ is strictly best possible. -/
theorem erdos_275_extremal_sharpness (r : ℕ) :
    (∀ x ∈ Finset.Icc 1 (2 ^ r - 1), ∃ i : Fin r, x ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)]) ∧
      (∀ i : Fin r, ¬ (0 ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)])) ∧
      (∀ i : Fin r, ¬ (2 ^ r ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)])) := by
  refine ⟨fun x hx => ?_, fun i => ?_, fun i => ?_⟩
  · rw [Finset.mem_Icc] at hx
    exact erdos_275_dyadic_covers_Icc r x hx.1 hx.2
  · simpa using erdos_275_dyadic_misses_mul r 0 i
  · simpa using erdos_275_dyadic_misses_mul r 1 i

/-! ## 5. Erdős Problems #873 & #1125: Consecutive-LCM Growth & Kemperman Monotone Chains -/

/-- **Erdős #873 Consecutive-LCM Lower Bound**:
For any strictly monotone sequence $a : \mathbb{N} \to \mathbb{N}$ with $1 \le a(0)$ and any block
length $k \ge 1$, the block LCM satisfies $\operatorname{lcm}_{m < k} a(i + m) \ge i + k$. -/
theorem erdos_873_lcm_ge_add {a : ℕ → ℕ} (ha₀ : 1 ≤ a 0) (hm : StrictMono a)
    (i k : ℕ) (hk : 1 ≤ k) :
    i + k ≤ (Finset.range k).lcm (fun m => a (i + m)) := by
  have h_mono : ∀ n, n + 1 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hlt : a n < a (n + 1) := hm (Nat.lt_succ_self n)
      omega
  have h_mem : k - 1 ∈ Finset.range k := Finset.mem_range.2 (by omega)
  have h_dvd : a (i + (k - 1)) ∣ (Finset.range k).lcm (fun m => a (i + m)) :=
    Finset.dvd_lcm h_mem
  have h_lcm_pos : 0 < (Finset.range k).lcm (fun m => a (i + m)) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Finset.lcm_ne_zero_iff]
    intro m _
    have := h_mono (i + m)
    omega
  have h_le : a (i + (k - 1)) ≤ (Finset.range k).lcm (fun m => a (i + m)) :=
    Nat.le_of_dvd h_lcm_pos h_dvd
  have h_grow := h_mono (i + (k - 1))
  omega

/-- **Erdős #1125 (Kemperman's Inequality Step Lower Bound)**:
If $f : \mathbb{R} \to \mathbb{R}$ satisfies Kemperman's inequality
$2 f(x) \le f(x + h) + f(x + 2h)$ for all $x \in \mathbb{R}$ and $h > 0$, then for every $x$
and $h > 0$, $f(x) \le \max(f(x + h), f(x + 2h))$. -/
theorem erdos_1125_kemperman_le_max {f : ℝ → ℝ}
    (hf : ∀ x h : ℝ, 0 < h → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    f x ≤ max (f (x + h)) (f (x + 2 * h)) := by
  have h_ineq := hf x h hh
  have h1 : f (x + h) ≤ max (f (x + h)) (f (x + 2 * h)) := le_max_left _ _
  have h2 : f (x + 2 * h) ≤ max (f (x + h)) (f (x + 2 * h)) := le_max_right _ _
  linarith

/-- Next step in the greedy Kemperman chain: advances by $h$ if $f(x + 2h) \le f(x + h)$,
and by $2h$ otherwise. -/
noncomputable def kempermanNext (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  if f (x + 2 * h) ≤ f (x + h) then x + h else x + 2 * h

/-- **Erdős #1125 (Greedy Monotone Chain under Kemperman's Inequality)**:
If $f : \mathbb{R} \to \mathbb{R}$ satisfies $2 f(x) \le f(x + h) + f(x + 2h)$ for all $h > 0$,
then iterating `kempermanNext f h` from any $x_0$ produces a strictly increasing sequence
$x_m \ge x_0 + m h$ along which $f$ is non-decreasing ($f(x_0) \le f(x_m)$). -/
theorem erdos_1125_kemperman_monotone_chain {f : ℝ → ℝ}
    (hf : ∀ x h : ℝ, 0 < h → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (x₀ : ℝ) {h : ℝ} (hh : 0 < h) (m : ℕ) :
    x₀ + (m : ℝ) * h ≤ (kempermanNext f h)^[m] x₀ ∧
      f x₀ ≤ f ((kempermanNext f h)^[m] x₀) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    set xm := (kempermanNext f h)^[m] x₀
    have hstep_ineq := hf xm h hh
    unfold kempermanNext
    split_ifs with h_cmp
    · refine ⟨?_, ?_⟩
      · push_cast; linarith [ih.1]
      · linarith [ih.2]
    · refine ⟨?_, ?_⟩
      · push_cast; linarith [ih.1]
      · linarith [ih.2]

end ControlsLean.Bounty
