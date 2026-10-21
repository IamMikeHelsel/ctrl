/-
Copyright (c) 2026 ControlsLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Erdős Problem Solutions and Quantitative Bounds — Wave 2

This module provides self-contained, verified solutions and quantitative theorems for six
additional problems from the Erdős collection (`formal-conjectures`), completely disjoint
from `ControlsLean/Bounty/ErdosBounties.lean` and `ControlsLean/Bounty/ErdosNewInsights.lean`:

1. **Erdős Problem #1148 (`Erdos1148`)**:
   - Complete proof of `erdos_1148.variants.weaker`: every natural number $n \in \mathbb{N}$ can
     be written as $n = x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2) \le n + 2\sqrt{n}$.
   - Exact sufficient conditions for the strong bound `Erdos1148Prop n` ($\max(x^2, y^2, z^2) \le n$):
     every square $n = m^2$ and every integer $n$ whose remainder $n - \lfloor\sqrt{n}\rfloor^2$
     is odd satisfies `Erdos1148Prop n` unconditionally.

2. **Erdős Problem #1179 (`Erdos1179`)**:
   - Complete proof of `erdos_1179.variants.lower_bound`: for any finite additive commutative
     group $G$, any $\varepsilon \in (0, 1)$, and any $\varepsilon$-balanced subset $A \subseteq G$,
     we have $|G| \le 2^{|A|}$.
   - Exact representation conservation law $\sum_{g \in G} F_A(g) = 2^{|A|}$ and strict
     positivity $F_A(g) \ge 1$ for every $g \in G$ whenever $\varepsilon < 1$.

3. **Erdős Problem #1187 (`Erdos1187`)**:
   - Complete proof of `erdos_1187.parts.ii`: disproving the existence of monochromatic
     arithmetic progressions of length $k \ge 3$ with prime common difference under finite
     colourings of $\mathbb{Z}$, via the canonical modulo-$4$ colouring $c(n) = (n : \mathrm{ZMod}\ 4)$.

4. **Erdős Problem #311 (`Erdos311`)**:
   - Complete proof of `erdos_311.delta_ge_inv_lcm`: for every $N \in \mathbb{N}$, the minimal
     non-zero Egyptian-fraction discrepancy $\delta(N) = \min_{A \subseteq \{1,\dots,N\}} |1 - \sum_{n \in A} 1/n|$
     satisfies $\frac{1}{\operatorname{lcm}(1, \dots, N)} \le \delta(N)$, together with $\delta(1) = 1$.

5. **Erdős Problem #367 (`Erdos367`)**:
   - Complete proof of `erdos_367.variants.k_le_two`: for every $k \le 2$, the product of the
     $2$-full parts over a window of length $k$ satisfies
     $\prod_{n \le m < n+k} B_2(m) = O(n^2)$ as $n \to \infty$.
   - Universal divisibility $B_r(n) \mid n$ and bound $B_r(n) \le n$ for all $r$ and $n \ge 1$.

6. **Erdős Problem #455 (`Erdos455`)**:
   - Discrete second-order convexity and double-integrator growth bounds for sequences with
     non-decreasing first differences $q_{n+2} - q_{n+1} \ge q_{n+1} - q_n$, establishing
     exact linear and quadratic lower bounds on $q_n$.
-/

namespace ControlsLean.Bounty.ErdosWave2

open Finset Filter Asymptotics
open scoped Topology

/-! ## 1. Erdős Problem #1148: Representations by $x^2 + y^2 - z^2$ -/

namespace Erdos1148

/-- Strong representation property from Erdős Problem #1148:
$n = x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2) \le n$. -/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

/-- Weaker representation property from Erdős Problem #1148 (`erdos_1148.variants.weaker`):
$n = x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2) \le n + 2\sqrt{n}$. -/
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

/-- Every perfect square $n = m^2$ satisfies the strong representation property `Erdos1148Prop n`
via $(x, y, z) = (m, 0, 0)$. -/
theorem erdos_1148_prop_of_sq_eq {n m : ℕ} (h : n = m ^ 2) : Erdos1148Prop n := by
  refine ⟨m, 0, 0, by omega, by omega, by omega, by omega⟩

/-- Every natural number $n$ whose remainder $n - \lfloor\sqrt{n}\rfloor^2 = 2k + 1$ is odd
satisfies the strong representation property `Erdos1148Prop n` via
$(x, y, z) = (\lfloor\sqrt{n}\rfloor, k + 1, k)$. -/
theorem erdos_1148_prop_of_odd_rem (n k : ℕ)
    (hrem : n = (Nat.sqrt n) ^ 2 + (2 * k + 1)) : Erdos1148Prop n := by
  set m := Nat.sqrt n
  have hlt : n < (m + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hkm : k + 1 ≤ m := by nlinarith
  have hk_sq : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm 2
  have hk0_sq : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ k) 2
  refine ⟨m, k + 1, k, ?_, by omega, by omega, by omega⟩
  have hdiff : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  omega

/-- Strong `Erdos1148Prop n` implies the weaker property `erdos_1148_weaker_prop n`. -/
theorem erdos_1148_weaker_of_strong {n : ℕ} (h : Erdos1148Prop n) :
    erdos_1148_weaker_prop n := by
  rcases h with ⟨x, y, z, heq, hx, hy, hz⟩
  have hpos : 0 ≤ 2 * Real.sqrt n := by positivity
  have hxR : (x ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hyR : (y ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hy
  have hzR : (z ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hz
  exact ⟨x, y, z, heq, by linarith, by linarith, by linarith⟩

/-- Complete solution to `Erdos1148.erdos_1148.variants.weaker`:
Every natural number $n$ can be written as $n = x^2 + y^2 - z^2$ with
$\max(x^2, y^2, z^2) \le n + 2\sqrt{n}$. -/
theorem erdos_1148.variants.weaker : ∀ n : ℕ, erdos_1148_weaker_prop n := by
  intro n
  set m := Nat.sqrt n
  have hm_le : m ^ 2 ≤ n := Nat.sqrt_le' n
  have hm_lt : n < (m + 1) ^ 2 := Nat.lt_succ_sqrt' n
  set r := n - m ^ 2
  have hr_eq : n = m ^ 2 + r := (Nat.add_sub_of_le hm_le).symm
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- Case 1: r = k + k is even
    by_cases hk0 : k = 0
    · apply erdos_1148_weaker_of_strong
      apply erdos_1148_prop_of_sq_eq (m := m)
      omega
    · -- Subcase 1b: r = 2k with 1 ≤ k ≤ m
      have hkm : k ≤ m := by nlinarith
      set j := m - k
      have hj_eq : j + k = m := Nat.sub_add_cancel hkm
      have hj_lt : j + 1 ≤ m := by omega
      have h_id : n = (m + 1) ^ 2 + j ^ 2 - (j + 1) ^ 2 := by
        have h1 : (m + 1) ^ 2 + j ^ 2 = m ^ 2 + 2 * m + 1 + j ^ 2 := by ring
        have h2 : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
        omega
      have hm_sqrt : (m : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg m)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hm_le)
      have hn_ge : m ^ 2 + 2 ≤ n := by omega
      have hn_ge_R : (m : ℝ) ^ 2 + 2 ≤ (n : ℝ) := by exact_mod_cast hn_ge
      have hx_le : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ n + 2 * Real.sqrt n := by
        calc ((m + 1 : ℕ) : ℝ) ^ 2 = (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 := by
              push_cast; ring
          _ ≤ ((n : ℝ) - 2) + 2 * Real.sqrt n + 1 := by linarith
          _ ≤ (n : ℝ) + 2 * Real.sqrt n := by linarith
      have hj1_sq : (j + 1) ^ 2 ≤ n := by
        calc (j + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hj_lt 2
          _ ≤ n := hm_le
      have hj_sq : j ^ 2 ≤ n := by
        calc j ^ 2 ≤ (j + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ j) 2
          _ ≤ n := hj1_sq
      have hj1_R : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by
        have h : (((j + 1) ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj1_sq
        simpa only [Nat.cast_pow] using h
      have hj_R : (j : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hj_sq
      have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt n := by positivity
      exact ⟨m + 1, j, j + 1, h_id, hx_le, by linarith, by linarith⟩
  · -- Case 2: r = 2k + 1 is odd
    apply erdos_1148_weaker_of_strong
    apply erdos_1148_prop_of_odd_rem n k
    change n = m ^ 2 + (2 * k + 1)
    omega

end Erdos1148

/-! ## 2. Erdős Problem #1179: Uniform Subset Sums in Finite Abelian Groups -/

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
/-- $F_A(g) = \#\{S \subseteq A : \sum_{x \in S} x = g\}$. -/
noncomputable def repCount (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter fun S ↦ ∑ x ∈ S, x = g).card

/-- `A` is `ε`-balanced if $|F_A(g) - 2^{|A|}/|G|| \le \varepsilon \cdot 2^{|A|}/|G|$ for all $g \in G$. -/
def IsBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G, |(repCount A g : ℝ) - 2 ^ A.card / Fintype.card G| ≤
    ε * (2 ^ A.card / Fintype.card G)

/-- Conservation of subset-sum representations: the sum of $F_A(g)$ over all $g \in G$
equals $2^{|A|}$. -/
theorem sum_repCount_eq_two_pow (A : Finset G) :
    ∑ g : G, repCount A g = 2 ^ A.card := by
  classical
  simp only [repCount]
  rw [← Finset.card_biUnion]
  · have h_eq : (univ : Finset G).biUnion
        (fun g ↦ A.powerset.filter fun S ↦ ∑ x ∈ S, x = g) = A.powerset := by
      ext S
      simp only [mem_biUnion, mem_univ, mem_filter, true_and, exists_eq_right']
    rw [h_eq, Finset.card_powerset]
  · intro g₁ _ g₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro S hS₁ hS₂
    rw [mem_filter] at hS₁ hS₂
    exact hne (hS₁.2.symm.trans hS₂.2)

/-- If $A$ is $\varepsilon$-balanced with $\varepsilon < 1$, then every element $g \in G$
has at least one subset representation ($1 \le F_A(g)$). -/
theorem repCount_pos_of_isBalanced {ε : ℝ} (hε1 : ε < 1) {A : Finset G}
    (hbal : IsBalanced ε A) (g : G) :
    1 ≤ repCount A g := by
  have hg := hbal g
  have h_abs : -(ε * (2 ^ A.card / (Fintype.card G : ℝ))) ≤
      (repCount A g : ℝ) - 2 ^ A.card / (Fintype.card G : ℝ) :=
    (abs_le.mp hg).1
  have hcard_pos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hpow_pos : (0 : ℝ) < 2 ^ A.card := by positivity
  have hquot_pos : (0 : ℝ) < 2 ^ A.card / (Fintype.card G : ℝ) := div_pos hpow_pos hcard_pos
  have hrep_pos : (0 : ℝ) < (repCount A g : ℝ) := by nlinarith
  have hrep_nat : 0 < repCount A g := by exact_mod_cast hrep_pos
  omega

/-- Complete solution to `Erdos1179.erdos_1179.variants.lower_bound`:
For any $\varepsilon \in (0, 1)$ and any $\varepsilon$-balanced subset $A \subseteq G$,
$|G| \le 2^{|A|}$. -/
theorem erdos_1179.variants.lower_bound :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ A : Finset G, IsBalanced ε A → Fintype.card G ≤ 2 ^ A.card := by
  intro ε _ hε1 A hbal
  calc Fintype.card G = ∑ _g : G, 1 := by simp
    _ ≤ ∑ g : G, repCount A g :=
        Finset.sum_le_sum (fun g _ ↦ repCount_pos_of_isBalanced hε1 hbal g)
    _ = 2 ^ A.card := sum_repCount_eq_two_pow A

end Erdos1179

/-! ## 3. Erdős Problem #1187: Monochromatic Arithmetic Progressions with Prime Difference -/

namespace Erdos1187

/-- A set $S$ is an arithmetic progression of length $l$ with first term $a$ and common
difference $d$ (`Set.IsAPOfLengthWith` from `formal-conjectures`). -/
def IsAPOfLengthWith {α : Type*} [AddCommMonoid α] (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : (n : ℕ∞) < l)}

/-- No prime number is divisible by $4$. -/
theorem not_four_dvd_prime {p : ℕ} (hp : p.Prime) : ¬ (4 ∣ p) := by
  intro hdvd
  have h2 : 2 ∣ 4 := by decide
  have h2p : 2 ∣ p := dvd_trans h2 hdvd
  rcases (Nat.dvd_prime hp).mp h2p with h | rfl
  · omega
  · omega

/-- Under the modulo-$4$ colouring $c : \mathbb{Z} \to \mathrm{ZMod}\ 4$, $c(n) = (n : \mathrm{ZMod}\ 4)$,
no two integers at prime distance $p$ share the same colour. -/
theorem no_monochromatic_prime_diff_pair_mod_four (a : ℤ) {p : ℕ} (hp : p.Prime) :
    ((a : ℤ) : ZMod 4) ≠ (((a + (p : ℤ)) : ℤ) : ZMod 4) := by
  intro heq
  have hsub : (((a + (p : ℤ)) : ℤ) : ZMod 4) - ((a : ℤ) : ZMod 4) = 0 :=
    sub_eq_zero.mpr heq.symm
  push_cast at hsub
  rw [add_sub_cancel_left] at hsub
  have hdvd : 4 ∣ p := (ZMod.natCast_eq_zero_iff p 4).mp hsub
  exact not_four_dvd_prime hp hdvd

/-- Complete solution to `Erdos1187.erdos_1187.parts.ii`:
It is false that for every $k \ge 3$ and every finite colouring of $\mathbb{Z}$, there exists a
monochromatic arithmetic progression of length $k$ whose common difference is a prime. -/
theorem erdos_1187.parts.ii : ¬ ∀ k : ℕ, 3 ≤ k →
    ∀ (κ : Type) [Finite κ] (c : ℤ → κ), ∃ (a : ℤ) (p : ℕ) (S : Set ℤ), p.Prime ∧
      IsAPOfLengthWith S k a (p : ℤ) ∧ ∃ γ : κ, ∀ n ∈ S, c n = γ := by
  intro H
  obtain ⟨a, p, S, hp, hS, γ, hmono⟩ :=
    H 3 (le_refl 3) (ZMod 4) (fun n : ℤ ↦ (n : ZMod 4))
  have ha_mem : a ∈ S := by
    rw [hS.2]
    refine ⟨0, ?_, by simp⟩
    exact_mod_cast (by decide : 0 < 3)
  have hap_mem : a + (p : ℤ) ∈ S := by
    rw [hS.2]
    refine ⟨1, ?_, by simp⟩
    exact_mod_cast (by decide : 1 < 3)
  have hc0 : (a : ZMod 4) = γ := hmono a ha_mem
  have hc1 : ((a + (p : ℤ) : ℤ) : ZMod 4) = γ := hmono (a + (p : ℤ)) hap_mem
  exact no_monochromatic_prime_diff_pair_mod_four a hp (hc0.trans hc1.symm)

end Erdos1187

/-! ## 4. Erdős Problem #311: Egyptian-Fraction Discrepancy Lower Bound -/

namespace Erdos311

/-- `delta N` is the minimal non-zero value of $|1 - \sum_{n \in A} 1/n|$ as $A$ ranges over
all subsets of $\{1, \dots, N\}$. -/
noncomputable def delta (N : ℕ) : ℝ :=
  sInf {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

/-- For $N = 1$, $\delta(1) = 1$. -/
theorem delta_one : delta 1 = 1 := by
  have hset : {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc (1 : ℕ) 1, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|} = {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, A, hA, rfl⟩
      rw [Icc_self, subset_singleton_iff] at hA
      rcases hA with rfl | rfl
      · simp
      · simp at hx
    · rintro rfl
      exact ⟨one_ne_zero, ∅, empty_subset _, by simp⟩
  unfold delta
  rw [hset, csInf_singleton]

/-- The least common multiple $L_N = \operatorname{lcm}_{n \in [1, N]} n$ is strictly positive
for every $N \in \mathbb{N}$. -/
theorem lcm_Icc_pos (N : ℕ) : 0 < (Icc 1 N).lcm id := by
  by_contra h
  have h0 : (Icc 1 N).lcm id = 0 := by omega
  rw [Finset.lcm_eq_zero_iff] at h0
  rcases h0 with ⟨n, hn, hn0⟩
  rw [Finset.mem_Icc] at hn
  simp only [id_eq] at hn0
  omega

/-- For any $A \subseteq \{1, \dots, N\}$ and $L = \operatorname{lcm}(1, \dots, N)$,
the scaled discrepancy $L \cdot (1 - \sum_{n \in A} 1/n)$ is the real cast of an integer. -/
theorem lcm_mul_discrepancy_eq_intCast (N : ℕ) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) :
    let L : ℕ := (Icc 1 N).lcm id
    ∃ M : ℤ, (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = (M : ℝ) := by
  intro L
  refine ⟨(L : ℤ) - ∑ n ∈ A, ((L / n : ℕ) : ℤ), ?_⟩
  push_cast
  rw [mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun n hn ↦ ?_)
  have hn_Icc : n ∈ Icc 1 N := hA hn
  have hn_pos : 0 < n := by
    rw [Finset.mem_Icc] at hn_Icc
    omega
  have hn_dvd : n ∣ L := Finset.dvd_lcm hn_Icc
  have hL_eq : (n : ℝ) * ((L / n : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hn_dvd
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn_pos)
  calc (L : ℝ) * (1 / (n : ℝ)) = ((n : ℝ) * ((L / n : ℕ) : ℝ)) / (n : ℝ) := by
        rw [hL_eq, mul_one_div]
    _ = ((L / n : ℕ) : ℝ) := mul_div_cancel_left₀ _ hn_ne

/-- Complete solution to `Erdos311.delta_ge_inv_lcm`:
For every $N \in \mathbb{N}$, $\frac{1}{\operatorname{lcm}(1, \dots, N)} \le \delta(N)$. -/
theorem delta_ge_inv_lcm (N : ℕ) : 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N := by
  unfold delta
  set S := {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}
  have hne : S.Nonempty := ⟨1, one_ne_zero, ∅, empty_subset _, by simp⟩
  apply le_csInf hne
  rintro x ⟨hx_ne, A, hA, rfl⟩
  set L : ℕ := (Icc 1 N).lcm id
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast lcm_Icc_pos N
  obtain ⟨M, hM⟩ := lcm_mul_discrepancy_eq_intCast N hA
  have h_abs : (L : ℝ) * |1 - ∑ n ∈ A, (1 : ℝ) / n| = |(M : ℝ)| := by
    rw [← abs_of_pos hL_pos, ← abs_mul, hM]
  have hM_ne : M ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, abs_zero] at h_abs
    rcases mul_eq_zero.mp h_abs with hL0 | hx0
    · linarith
    · exact hx_ne hx0
  have hM_ge_one : (1 : ℝ) ≤ |(M : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |M| := Int.one_le_abs hM_ne
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|M| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using h2
  rw [div_le_iff₀' hL_pos]
  linarith

end Erdos311

/-! ## 5. Erdős Problem #367: Products of $r$-Full Parts -/

namespace Erdos367

/-- `B r n` is the $r$-full part of $n$: the product of prime powers $p^a \parallel n$
with $a \ge r$. -/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

/-- For every $n \ne 0$, the $r$-full part $B_r(n)$ divides $n$. -/
theorem B_dvd (r : ℕ) {n : ℕ} (hn : n ≠ 0) : B r n ∣ n := by
  have hprod : ∏ i ∈ n.factorization.support, i ^ n.factorization i = n :=
    Nat.prod_factorization_pow_eq_self hn
  have hdvd : B r n ∣ ∏ i ∈ n.factorization.support, i ^ n.factorization i :=
    Finset.prod_dvd_prod_of_subset
      (n.factorization.support.filter fun i ↦ r ≤ n.factorization i)
      n.factorization.support
      (fun i : ℕ ↦ i ^ n.factorization i)
      (Finset.filter_subset (fun i ↦ r ≤ n.factorization i) n.factorization.support)
  rwa [hprod] at hdvd

/-- For every $n \ge 1$, $B_r(n) \le n$. -/
theorem B_le_self (r : ℕ) {n : ℕ} (hn : 1 ≤ n) : B r n ≤ n :=
  Nat.le_of_dvd (by omega) (B_dvd r (by omega))

/-- Over any window $[n, n+k)$ with $n \ge 1$, the product of $B_r(m)$ is at most
the product of $m$. -/
theorem prod_B_le_prod_Ico (r k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∏ m ∈ Finset.Ico n (n + k), B r m ≤ ∏ m ∈ Finset.Ico n (n + k), m := by
  refine Finset.prod_le_prod (fun m hm ↦ ?_)
  rw [Finset.mem_Ico] at hm
  exact B_le_self r (by omega)

/-- For $k \le 2$ and $n \ge 1$, $\prod_{m \in [n, n+k)} B_2(m) \le 2 n^2$. -/
theorem prod_B_two_le_two_mul_sq {k : ℕ} (hk : k ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    ∏ m ∈ Finset.Ico n (n + k), B 2 m ≤ 2 * n ^ 2 := by
  have hle := prod_B_le_prod_Ico 2 k hn
  interval_cases k
  · simp at hle ⊢
    nlinarith
  · simp at hle ⊢
    nlinarith
  · have hIco : Finset.Ico n (n + 2) = {n, n + 1} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hIco, Finset.prod_pair (by omega), Finset.prod_pair (by omega)] at hle
    rw [hIco, Finset.prod_pair (by omega)]
    nlinarith

/-- Complete solution to `Erdos367.erdos_367.variants.k_le_two`:
For every $k \le 2$, $\prod_{n \le m < n+k} B_2(m) = O(n^2)$ as $n \to \infty$. -/
theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
  intro k hk
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  have hbound := prod_B_two_le_two_mul_sq hk hn
  have hboundR : ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    exact_mod_cast hbound
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.rpow_two,
      Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
  exact hboundR

end Erdos367

/-! ## 6. Erdős Problem #455: Discrete Convexity and Prime Gap Integrators -/

namespace Erdos455

/-- Discrete second-order convexity from Erdős Problem #455:
first differences are non-decreasing, $q(n+1) - q(n) \le q(n+2) - q(n+1)$. -/
def IsDiscreteConvex (q : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, q (n + 1) - q n ≤ q (n + 2) - q (n + 1)

/-- Monotonicity of first differences for a discrete-convex sequence. -/
theorem discreteConvex_diff_mono {q : ℕ → ℕ} (hconv : IsDiscreteConvex q) :
    Monotone (fun n ↦ q (n + 1) - q n) :=
  monotone_nat_of_le_succ hconv

/-- Telescoping sum of first differences for any monotone sequence $q : \mathbb{N} \to \mathbb{N}$. -/
theorem monotone_telescoping_sum {q : ℕ → ℕ} (hmono : Monotone q) (n : ℕ) :
    q 0 + ∑ k ∈ Finset.range n, (q (k + 1) - q k) = q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have hle : q n ≤ q (n + 1) := hmono (Nat.le_succ n)
    omega

/-- Discrete first-order Taylor lower bound for a discrete-convex monotone sequence:
$q(n) \ge q(0) + n \cdot (q(1) - q(0))$. -/
theorem discreteConvex_linear_lower_bound {q : ℕ → ℕ}
    (hmono : Monotone q) (hconv : IsDiscreteConvex q) (n : ℕ) :
    q 0 + n * (q 1 - q 0) ≤ q n := by
  rw [← monotone_telescoping_sum hmono n]
  gcongr
  calc n * (q 1 - q 0) = ∑ _k ∈ Finset.range n, (q 1 - q 0) := by simp
    _ ≤ ∑ k ∈ Finset.range n, (q (k + 1) - q k) := by
        refine Finset.sum_le_sum (fun k _ ↦ ?_)
        exact discreteConvex_diff_mono hconv (Nat.zero_le k)

/-- If a sequence has strictly increasing first differences with step acceleration at least $c$
($q(k+2) - q(k+1) \ge q(k+1) - q(k) + c$), then the $n$-th first difference satisfies
$q(n+1) - q(n) \ge (q(1) - q(0)) + n \cdot c$. -/
theorem discreteConvex_diff_accel_bound {q : ℕ → ℕ} {c : ℕ}
    (haccel : ∀ k : ℕ, q (k + 1) - q k + c ≤ q (k + 2) - q (k + 1)) (n : ℕ) :
    (q 1 - q 0) + n * c ≤ q (n + 1) - q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := haccel n
    calc (q 1 - q 0) + (n + 1) * c = ((q 1 - q 0) + n * c) + c := by ring
      _ ≤ (q (n + 1) - q n) + c := Nat.add_le_add_right ih c
      _ ≤ q (n + 2) - q (n + 1) := hstep

/-- Discrete double-integrator quadratic lower bound for Erdős Problem #455:
Under uniform step acceleration $q(k+2) - q(k+1) \ge q(k+1) - q(k) + c$,
$2 q(n) \ge 2 q(0) + 2 n (q(1) - q(0)) + n (n - 1) c$. -/
theorem discreteConvex_quadratic_lower_bound {q : ℕ → ℕ} {c : ℕ}
    (hmono : Monotone q)
    (haccel : ∀ k : ℕ, q (k + 1) - q k + c ≤ q (k + 2) - q (k + 1)) (n : ℕ) :
    2 * q 0 + 2 * n * (q 1 - q 0) + n * (n - 1) * c ≤ 2 * q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : q n ≤ q (n + 1) := hmono (Nat.le_succ n)
    have hdiff := discreteConvex_diff_accel_bound haccel n
    have h_tri : (n + 1) * n = n * (n - 1) + 2 * n := by
      cases n with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    calc 2 * q 0 + 2 * (n + 1) * (q 1 - q 0) + (n + 1) * n * c
        = (2 * q 0 + 2 * n * (q 1 - q 0) + n * (n - 1) * c) +
          2 * ((q 1 - q 0) + n * c) := by
          rw [h_tri]
          ring
      _ ≤ 2 * q n + 2 * (q (n + 1) - q n) :=
          Nat.add_le_add ih (Nat.mul_le_mul_left 2 hdiff)
      _ = 2 * q (n + 1) := by omega

end Erdos455

end ControlsLean.Bounty.ErdosWave2
