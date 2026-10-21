/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# Uncontested Erdős Problem Solutions, Variants & Counterexample Certificates

This module provides standalone, complete, machine-checked, standard-axiom-only Lean 4 formalizations
of theorems, variants, structural bounds, and counterexample certificates across five
Erdős problems from Google DeepMind's *Formal Conjectures* repository:

1. **Erdős Problem #261** (`Erdos261`):
   - Telescoping identity for $\sum_{k \in (n, n+m]} k / 2^k$.
   - `erdos_261_borwein_loring`: Borwein–Loring identity [BoLo90] for $n = 2^{m+1} - m - 2$.
   - `erdos_261_borwein_loring_property`: `Erdos261Prop (2 ^ (m + 1) - m - 2)` for $m \ge 2$.
   - `erdos_261_parts_i`: Infinitely many positive integers $n$ satisfy `Erdos261Prop n`.
   - `erdos_261_rafik_split`: Z. Rafik's dyadic split $4/2^4 = 5/2^5 + 6/2^6$.

2. **Erdős Problem #931** (`Erdos931`):
   - `erdos_931_counterexample_symmetric_2_7`: Positive-integer symmetric $k_1 = k_2 = 3$
     counterexample $(n_1, n_2) = (2, 7)$ to $n_2 > 2(n_1 + k_1)$, improving on AlphaProof's
     degenerate $n_1 = 0$ example $(k_1, k_2, n_1, n_2) = (10, 3, 0, 13)$.
   - `erdos_931_counterexample_no_strict_between_prime`: Symmetric $k_1 = k_2 = 3$ counterexample
     $(n_1, n_2) = (3, 7)$ where the open interval $(n_1 + k_1, n_2) = (6, 7)$ between the two
     blocks contains no prime (and no integer).
   - `erdos_931_additional_condition_nonempty`: Exact statement of
     `Erdos931.erdos_931.variants.additional_condition_nonempty`.
   - `erdos_931_exists_prime_of_two_mul_le`: Via Bertrand's postulate, whenever $1 \le n_1$ and
     $2 n_1 \le n_2$, there always exists a prime $p$ with $n_1 \le p \le n_2$.

3. **Erdős Problem #951** (`Erdos951`):
   - `erdos_951_step_gap`: Any strictly increasing sequence $a : \mathbb{N} \to \mathbb{R}$ with
     1-separated Beurling integers (`Erdos951Prop a`) satisfies $a(n + 1) - a(n) \ge 1$.
   - `erdos_951_linear_lower_bound`: Constructive linear growth bound $a(n) \ge a(0) + n$.
   - `erdos_951_isBeurlingPrimes`: Direct proof of `Erdos951.erdos_951.variants.isBeurlingPrimes`
     from the linear lower bound without non-constructive LUB/compactness arguments.

4. **Erdős Problem #143** (`Erdos143`):
   - `erdos_143_one_separated`: Any `WellSeparatedSet A` is $1$-separated ($|x - y| \ge 1$ for
     distinct $x, y \in A$).
   - `erdos_143_floor_injOn`: The floor map $x \mapsto \lfloor x \rfloor_+$ is injective on any
     `WellSeparatedSet A`.
   - `erdos_143_ncard_le_floor`: For every $x \ge 1$, $A \cap [1, x]$ is finite and satisfies
     $(A \cap [1, x]).\mathrm{ncard} \le \lfloor x \rfloor_+$, certifying non-vacuity of the
     counting function in `Erdos143.erdos_143.parts.i`.

5. **Erdős Problem #834** (`Erdos834`):
   - `erdos_834_parts_ii`: R. Li's 9-vertex, 22-edge 3-uniform hypergraph [arXiv:2512.24850]
     certified via kernel `decide +kernel` to have chromatic number 3, minimum degree $\ge 7$,
     and to become 2-colorable upon deleting any edge or any vertex.
-/

namespace ControlsLean.Bounty

open Finset Filter
open scoped Topology

/-! ## 1. Erdős Problem #261: Dyadic Representations $n / 2^n = \sum a_k / 2^{a_k}$ -/

/-- A natural number $n$ satisfies `Erdos261Prop` if there exist $t \ge 2$ pairwise distinct
positive integers $a_1, \ldots, a_t$ such that $n / 2^n = \sum_{k} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop :=
  ∃ (t : ℕ) (_ht : 2 ≤ t) (a : Fin t → ℕ),
    Function.Injective a ∧ (1 ≤ a) ∧ (n : ℚ) / (2 ^ n : ℚ) = ∑ k, (a k : ℚ) / (2 ^ (a k) : ℚ)

/-- Telescoping sum over `Finset.range m`:
$\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} =
\frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}$. -/
theorem sum_range_shifted_div_two_pow (n m : ℕ) :
    ∑ i ∈ Finset.range m, ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ) =
      ((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ) - ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : n + 1 + m = n + m + 1 := by omega
    have h2 : n + (m + 1) = n + m + 1 := by omega
    rw [h1, h2]
    push_cast
    rw [pow_succ (2 : ℚ) (n + m)]
    ring

/-- Telescoping sum over `Finset.Ioc n (n + m)`:
$\sum_{k \in (n, n + m]} \frac{k}{2^k} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}$. -/
theorem sum_Ioc_div_two_pow (n m : ℕ) :
    ∑ k ∈ Finset.Ioc n (n + m), (k : ℚ) / (2 ^ k : ℚ) =
      ((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ) - ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hle : n ≤ n + m := Nat.le_add_right n m
    have h_eq : n + (m + 1) = n + m + 1 := by omega
    rw [h_eq, Finset.sum_Ioc_succ_top hle, ih]
    push_cast
    rw [pow_succ (2 : ℚ) (n + m)]
    ring

/-- **Erdős #261 (Borwein–Loring Identity)**: For every positive integer $m$ and
$n = 2^{m+1} - m - 2$, $n / 2^n = \sum_{n < k \le n + m} k / 2^k$. -/
theorem erdos_261_borwein_loring (m : ℕ) (_hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    (n : ℚ) / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), (k : ℚ) / (2 ^ k : ℚ) := by
  intro n
  rw [sum_Ioc_div_two_pow]
  have hpow : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  have hnm : n + m + 2 = 2 ^ (m + 1) := by omega
  rw [hnm]
  have h_cast : ((2 ^ (m + 1) : ℕ) : ℚ) = (2 : ℚ) ^ m * 2 := by
    push_cast
    rw [pow_succ]
  have h_denom : (2 : ℚ) ^ (n + m) = (2 : ℚ) ^ n * (2 : ℚ) ^ m := pow_add (2 : ℚ) n m
  have h2m : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  rw [h_cast, h_denom, mul_comm ((2 : ℚ) ^ m) 2,
    mul_div_mul_right (2 : ℚ) ((2 : ℚ) ^ n) h2m]
  push_cast
  ring

/-- **Erdős #261 (Borwein–Loring Property)**: For every $m \ge 2$,
$n = 2^{m+1} - m - 2$ satisfies `Erdos261Prop`. -/
theorem erdos_261_borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  set n := 2 ^ (m + 1) - m - 2
  refine ⟨m, hm, fun i : Fin m => n + 1 + i.val, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp at hij
    exact Fin.ext (by omega)
  · intro i
    dsimp [Pi.one_apply]
    omega
  · rw [Fin.sum_univ_eq_sum_range (fun i => ((n + 1 + i : ℕ) : ℚ) / (2 ^ (n + 1 + i) : ℚ)),
      sum_range_shifted_div_two_pow]
    have hpow : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    have hnm : n + m + 2 = 2 ^ (m + 1) := by omega
    rw [hnm]
    have h_cast : ((2 ^ (m + 1) : ℕ) : ℚ) = (2 : ℚ) ^ m * 2 := by
      push_cast
      rw [pow_succ]
    have h_denom : (2 : ℚ) ^ (n + m) = (2 : ℚ) ^ n * (2 : ℚ) ^ m := pow_add (2 : ℚ) n m
    have h2m : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    rw [h_cast, h_denom, mul_comm ((2 : ℚ) ^ m) 2,
      mul_div_mul_right (2 : ℚ) ((2 : ℚ) ^ n) h2m]
    push_cast
    ring

/-- The Borwein–Loring sequence $k \mapsto 2^{k+3} - (k + 2) - 2$. -/
def borweinLoringSeq (k : ℕ) : ℕ := 2 ^ (k + 3) - (k + 2) - 2

theorem borweinLoringSeq_strictMono : StrictMono borweinLoringSeq := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  dsimp [borweinLoringSeq]
  have h1 : k + 3 < 2 ^ (k + 3) := Nat.lt_two_pow_self
  have h2 : 2 ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by
    have : k + 1 + 3 = (k + 3) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  omega

theorem borweinLoringSeq_pos (k : ℕ) : 0 < borweinLoringSeq k := by
  have h0 : 0 < borweinLoringSeq 0 := by decide
  exact lt_of_lt_of_le h0 (borweinLoringSeq_strictMono.monotone (Nat.zero_le k))

/-- **Erdős #261 (Part i)**: Infinitely many positive integers $n$ satisfy `Erdos261Prop n`. -/
theorem erdos_261_parts_i : {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem borweinLoringSeq_strictMono.injective fun k => ?_
  exact ⟨borweinLoringSeq_pos k, erdos_261_borwein_loring_property (k + 2) (by omega)⟩

/-- Z. Rafik's dyadic split $4/2^4 = 5/2^5 + 6/2^6$ (the $m = 2$ case of Borwein–Loring,
used to construct multiple infinite representations of $7/4$). -/
theorem erdos_261_rafik_split : (4 : ℚ) / 2 ^ 4 = 5 / 2 ^ 5 + 6 / 2 ^ 6 := by
  norm_num

/-! ## 2. Erdős Problem #931: Equal Prime Factors of Consecutive Products -/

/-- Symmetric $k_1 = k_2 = 3$ positive-integer counterexample $(n_1, n_2) = (2, 7)$ to
$n_2 > 2(n_1 + k_1)$: $3 \cdot 4 \cdot 5 = 60$ and $8 \cdot 9 \cdot 10 = 720$ share prime
factors $\{2, 3, 5\}$. -/
theorem erdos_931_counterexample_symmetric_2_7 :
    (2, 7) ∈ {(n₁, n₂) : ℕ × ℕ | n₁ + 3 ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + 3) ∧
      (∏ i ∈ Finset.Icc 1 3, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 3, (n₂ + j)).primeFactors} := by
  refine ⟨by decide, by decide, ?_⟩
  decide +kernel

/-- Symmetric $k_1 = k_2 = 3$ counterexample $(n_1, n_2) = (3, 7)$ where the open interval
$(n_1 + k_1, n_2) = (6, 7)$ strictly between the two consecutive-integer blocks contains no
prime (and no integer). -/
theorem erdos_931_counterexample_no_strict_between_prime :
    ((3, 7) ∈ {(n₁, n₂) : ℕ × ℕ | n₁ + 3 ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + 3) ∧
      (∏ i ∈ Finset.Icc 1 3, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 3, (n₂ + j)).primeFactors}) ∧
    ¬ ∃ p : ℕ, p.Prime ∧ 3 + 3 < p ∧ p < 7 := by
  refine ⟨⟨by decide, by decide, ?_⟩, ?_⟩
  · decide +kernel
  · rintro ⟨p, _, hp1, hp2⟩
    omega

/-- **Erdős #931 (`additional_condition_nonempty`)**: Witnessed by the symmetric positive-integer
counterexample $k_1 = k_2 = 3, (n_1, n_2) = (2, 7)$. -/
theorem erdos_931_additional_condition_nonempty :
    ∃ (k₁ k₂ : ℕ), ∃ (_h₁ : k₂ ≤ k₁), ∃ (_h₂ : 3 ≤ k₂),
      {(n₁, n₂) : ℕ × ℕ | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
          (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
          (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty :=
  ⟨3, 3, le_rfl, le_rfl, ⟨(2, 7), erdos_931_counterexample_symmetric_2_7⟩⟩

/-- **Erdős #931 (`exists_prime` in the Bertrand regime $2 n_1 \le n_2$)**: Whenever $1 \le n_1$
and $2 n_1 \le n_2$, Bertrand's postulate guarantees a prime $p$ with $n_1 \le p \le n_2$. -/
theorem erdos_931_exists_prime_of_two_mul_le {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 2 * n₁ ≤ n₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ ≤ p ∧ p ≤ n₂ := by
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul n₁ (by omega)
  exact ⟨p, hp_prime, le_of_lt hp_gt, le_trans hp_le hn₂⟩

/-! ## 3. Erdős Problem #951: 1-Separated Beurling Primes -/

/-- A sequence of real numbers $1 < a_0 < a_1 < \cdots$ is a sequence of Beurling primes if it
is strictly monotone and tends to $+\infty$. -/
noncomputable def IsBeurlingPrimes (a : ℕ → ℝ) : Prop :=
  1 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop

/-- A Beurling integer is a finite product $\prod_i a_i^{k_i}$ for a finitely supported exponent
vector $k : \mathbb{N} \to_0 \mathbb{N}$. -/
noncomputable def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ :=
  k.prod fun x y => (a x) ^ y

/-- Property `Erdos951Prop`: distinct finitely supported exponent vectors yield Beurling integers
at distance at least $1$. -/
def Erdos951Prop (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ : ℕ →₀ ℕ), k ≠ ℓ → |beurlingInteger a k - beurlingInteger a ℓ| ≥ 1

/-- Any strictly monotone sequence satisfying `Erdos951Prop` has consecutive gaps
$a(n + 1) - a(n) \ge 1$. -/
theorem erdos_951_step_gap {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) (n : ℕ) :
    1 ≤ a (n + 1) - a n := by
  have hlt : a n < a (n + 1) := hm (Nat.lt_succ_self n)
  have hne : (Finsupp.single (n + 1) 1 : ℕ →₀ ℕ) ≠ Finsupp.single n 1 := by
    intro h
    have := Finsupp.ext_iff.mp h n
    simp at this
  have hdist := he (Finsupp.single (n + 1) 1) (Finsupp.single n 1) hne
  simp only [beurlingInteger, Finsupp.prod_single_index, pow_zero, pow_one] at hdist
  rwa [abs_of_pos (sub_pos.mpr hlt)] at hdist

/-- Constructive linear lower bound: $a(0) + n \le a(n)$ for all $n \in \mathbb{N}$. -/
theorem erdos_951_linear_lower_bound {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a)
    (n : ℕ) : a 0 + (n : ℝ) ≤ a n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hgap := erdos_951_step_gap hm he n
    push_cast
    linarith

/-- **Erdős #951 (`isBeurlingPrimes`)**: Direct constructive proof via
`erdos_951_linear_lower_bound` that any strictly monotone sequence $a$ with $1 < a(0)$ and
`Erdos951Prop a` is a sequence of Beurling primes. -/
theorem erdos_951_isBeurlingPrimes {a : ℕ → ℝ} (ha : 1 < a 0)
    (hm : StrictMono a) (he : Erdos951Prop a) :
    IsBeurlingPrimes a := by
  refine ⟨ha, hm, ?_⟩
  refine tendsto_atTop_mono (erdos_951_linear_lower_bound hm he) ?_
  exact tendsto_atTop_add_const_left atTop (a 0) tendsto_natCast_atTop_atTop

/-! ## 4. Erdős Problem #143: Well-Separated Sets and Counting Non-Vacuity -/

/-- A countably infinite set $A \subseteq (1, \infty)$ is well-separated if $|k x - y| \ge 1$
for all distinct $x, y \in A$ and all integers $k \ge 1$. -/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ Set.Ioi (1 : ℝ)) ∧ Set.Infinite A ∧ Set.Countable A ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|))

/-- Specializing $k = 1$ shows every `WellSeparatedSet A` is $1$-separated. -/
theorem erdos_143_one_separated {A : Set ℝ} (hA : WellSeparatedSet A)
    {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    1 ≤ |x - y| := by
  have h1 := hA.2.2.2 x hx y hy hxy 1 le_rfl
  simpa using h1

/-- The natural floor map $x \mapsto \lfloor x \rfloor_+$ is injective on any `WellSeparatedSet`. -/
theorem erdos_143_floor_injOn {A : Set ℝ} (hA : WellSeparatedSet A) :
    Set.InjOn Nat.floor A := by
  intro x hx y hy hfloor
  by_contra hxy
  have hsep := erdos_143_one_separated hA hx hy hxy
  have hx_pos : 0 ≤ x := by
    have := hA.1 hx
    simp only [Set.mem_Ioi] at this
    linarith
  have hy_pos : 0 ≤ y := by
    have := hA.1 hy
    simp only [Set.mem_Ioi] at this
    linarith
  have hx_lo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_pos
  have hx_hi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hy_lo : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy_pos
  have hy_hi : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  rw [hfloor] at hx_lo hx_hi
  have habs : |x - y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- For every $x \in \mathbb{R}$, $A \cap [1, x]$ injects into $[1, \lfloor x \rfloor_+]$ via
`Nat.floor`, proving finiteness and $(A \cap [1, x]).\mathrm{ncard} \le \lfloor x \rfloor_+$. -/
theorem erdos_143_ncard_le_floor {A : Set ℝ} (hA : WellSeparatedSet A) (x : ℝ) :
    (A ∩ Set.Icc 1 x).Finite ∧ (A ∩ Set.Icc 1 x).ncard ≤ ⌊x⌋₊ := by
  have hinj : Set.InjOn Nat.floor (A ∩ Set.Icc 1 x) :=
    erdos_143_floor_injOn hA |>.mono Set.inter_subset_left
  have hmaps : Set.MapsTo Nat.floor (A ∩ Set.Icc 1 x) (Finset.Icc 1 ⌊x⌋₊ : Set ℕ) := by
    rintro y ⟨-, hy1, hyx⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Nat.le_floor (by simpa using hy1), Nat.floor_mono hyx⟩
  have hfin : (A ∩ Set.Icc 1 x).Finite :=
    Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet (Finset.Icc 1 ⌊x⌋₊))
  refine ⟨hfin, ?_⟩
  have hcard : (A ∩ Set.Icc 1 x).ncard ≤ (Finset.Icc 1 ⌊x⌋₊ : Set ℕ).ncard :=
    Set.ncard_le_ncard_of_injOn Nat.floor hmaps hinj (Finset.finite_toSet (Finset.Icc 1 ⌊x⌋₊))
  rw [Set.ncard_coe_finset, Nat.card_Icc] at hcard
  omega

/-! ## 5. Erdős Problem #834 (Part ii): 3-Chromatic-Critical 3-Uniform Hypergraph -/

/-- A hypergraph $H$ is $r$-uniform if every edge has cardinality $r$. -/
def IsUniform {V : Type*} (H : Finset (Finset V)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A weak $k$-coloring is proper if no edge is monochromatic. -/
def IsProperHypergraphColoring {V : Type*} (H : Finset (Finset V)) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- $H$ is $k$-colorable if it admits a proper weak $k$-coloring. -/
def HypergraphColorable {V : Type*} (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperHypergraphColoring H c

/-- $H$ has chromatic number $k$ if it is $k$-colorable and not $j$-colorable for any $j < k$. -/
def HasHypergraphChromaticNumber {V : Type*} (H : Finset (Finset V)) (k : ℕ) : Prop :=
  HypergraphColorable H k ∧ ∀ j < k, ¬ HypergraphColorable H j

/-- Vertex degree in a finite hypergraph. -/
def hypergraphDegree {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- Li's 9-vertex, 22-edge 3-uniform hypergraph [arXiv:2512.24850, Section 4.1]. -/
private def liH : Finset (Finset (Fin 9)) :=
  {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7},
   {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7},
   {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}}

private theorem liH_uniform : IsUniform liH 3 := by
  unfold IsUniform liH; decide +kernel

private theorem liH_degree : ∀ v : Fin 9, 7 ≤ hypergraphDegree liH v := by
  unfold hypergraphDegree liH; decide +kernel

private theorem liH_colorable_three : HypergraphColorable liH 3 :=
  ⟨![0, 0, 1, 0, 0, 1, 2, 1, 1], by unfold IsProperHypergraphColoring liH; decide +kernel⟩

private theorem liH_not_colorable_zero : ¬ HypergraphColorable liH 0 := by
  rintro ⟨c, -⟩
  exact (c 0).elim0

private theorem liH_not_colorable_one : ¬ HypergraphColorable liH 1 := by
  rintro ⟨c, hc⟩
  obtain ⟨x, -, y, -, hxy⟩ := hc {0, 1, 2} (by unfold liH; decide +kernel)
  exact hxy (Subsingleton.elim _ _)

private theorem liH_not_colorable_two : ¬ HypergraphColorable liH 2 := by
  rintro ⟨c, hc⟩
  revert c
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  unfold IsProperHypergraphColoring liH
  decide +kernel

private def edgeWit : Fin 22 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 1], ![0, 1, 0, 0, 1, 1, 0, 1, 1], ![0, 1, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 1, 1, 1, 0, 0, 1], ![0, 1, 0, 1, 1, 0, 1, 1, 0],
    ![0, 0, 1, 1, 1, 0, 1, 0, 1]]

private def vertWit : Fin 9 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 0, 1], ![0, 0, 1, 1, 1, 0, 1, 0, 0]]

private theorem liH_edge_critical : ∀ e ∈ liH, HypergraphColorable (liH.erase e) 2 := by
  suffices h : ∀ e ∈ liH, ∃ i : Fin 22, IsProperHypergraphColoring (liH.erase e) (edgeWit i) by
    intro e he
    obtain ⟨i, hi⟩ := h e he
    exact ⟨_, hi⟩
  unfold IsProperHypergraphColoring liH edgeWit
  decide +kernel

private theorem liH_vertex_critical :
    ∀ v : Fin 9, HypergraphColorable (liH.filter (fun e => v ∉ e)) 2 := by
  suffices h : ∀ v : Fin 9, IsProperHypergraphColoring (liH.filter (fun e => v ∉ e)) (vertWit v) by
    exact fun v => ⟨_, h v⟩
  unfold IsProperHypergraphColoring liH vertWit
  decide +kernel

/-- **Erdős #834 (Part ii)**: There exists a 3-uniform hypergraph with chromatic number 3 and
minimum degree $\ge 7$ that becomes 2-colorable upon deleting any edge or any vertex. -/
theorem erdos_834_parts_ii :
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform H 3 ∧ HasHypergraphChromaticNumber H 3 ∧
        (∀ e ∈ H, HypergraphColorable (H.erase e) 2) ∧
        (∀ v : Fin n, HypergraphColorable (H.filter (fun e => v ∉ e)) 2) ∧
        ∀ v : Fin n, 7 ≤ hypergraphDegree H v :=
  ⟨9, liH, liH_uniform,
    ⟨liH_colorable_three, fun j hj => by
      interval_cases j
      · exact liH_not_colorable_zero
      · exact liH_not_colorable_one
      · exact liH_not_colorable_two⟩,
    liH_edge_critical, liH_vertex_critical, liH_degree⟩

end ControlsLean.Bounty
