# Uncontested Erdős Problem Solutions, Variants, and Counterexample Certificates in Lean 4

**Author**: Mike Helsel  
**Date**: October 17, 2026  
**Status**: Machine-Checked & Verified (`ControlsLean.Bounty.ErdosBounties` & `ctrl-erdos-lab`)  
**Target Repositories**:
- `ctrl` (`ControlsLean/Bounty/ErdosBounties.lean`)
- `ctrl-erdos-lab` (`erdos/ErdosLab/Erdos261.lean`, `erdos/ErdosLab/Erdos931.lean`, `erdos/ErdosLab/Erdos834.lean`)  
**Axiom Footprint**: Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, zero custom axioms)

---

## 1. Abstract & Triage Summary

Using a two-tier triage pipeline across Google DeepMind's *Formal Conjectures* repository (`d9ce556af8ed`, 1,137 Erdős problems) and the Justin Sun Prize (JSP) / Palomar Registry problem catalogs, we identified high-leverage **uncontested** or partially formalized Erdős problems where complete `sorry`-free Lean 4 proofs, constructive bounds, or improved counterexample certificates can be machine-checked using standard axioms only.

We formalize five Erdős problem families in both the standalone `ctrl` bounty module (`ControlsLean/Bounty/ErdosBounties.lean`) and the `ctrl-erdos-lab` challenge/verifier pipeline (`erdos/Challenge/` + `erdos/ErdosLab/`):

1. **Erdős Problem #261** (*Dyadic Representations $n / 2^n = \sum a_k / 2^{a_k}$*):
   - Uncontested in the JSP catalog (`jsp_id = none`).
   - We formalize the Borwein–Loring telescoping identity [BoLo90] over $\mathbb{Q}$, prove `Erdos261.erdos_261.variants.borwein_loring` and `Erdos261.erdos_261.variants.borwein_loring_property`, and prove the main solved theorem `Erdos261.erdos_261.parts.i` ($\{n : \mathbb{N} \mid 0 < n \wedge \mathrm{Erdos261Prop}\, n\}.\mathrm{Infinite}$), together with Z. Rafik's dyadic split $4/2^4 = 5/2^5 + 6/2^6$.
2. **Erdős Problem #931** (*Prime Factors of Products of Consecutive Integer Blocks*):
   - While *Formal Conjectures* recorded AlphaProof's degenerate $n_1 = 0, k_1 = 10, k_2 = 3, n_2 = 13$ witness for `erdos_931.variants.additional_condition_nonempty`, a Python search uncovered positive-integer symmetric $k_1 = k_2 = 3$ counterexamples $(n_1, n_2) = (2, 7)$ and $(3, 7)$.
   - Moreover, $(k_1, k_2, n_1, n_2) = (3, 3, 3, 7)$ has $n_1 + k_1 = 6$ and $n_2 = 7$, proving that the strict open interval $(n_1 + k_1, n_2)$ between the two blocks can be empty and contain **no prime**, while in the regime $2 n_1 \le n_2$ ($n_1 \ge 1$), Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) guarantees a prime $p \in [n_1, n_2]$.
3. **Erdős Problem #951** (*1-Separated Beurling Prime Systems*):
   - Uncontested in the JSP catalog (`jsp_id = none`).
   - We prove the explicit uniform gap bound $a(n+1) - a(n) \ge 1$ (`erdos_951_step_gap`) and constructive linear growth bound $a(n) \ge a(0) + n$ (`erdos_951_linear_lower_bound`), giving a direct, non-contradiction proof of `Erdos951.erdos_951.variants.isBeurlingPrimes`.
4. **Erdős Problem #143** (*Well-Separated Real Sets Avoiding Near-Multiples*):
   - We prove that any `WellSeparatedSet A` is $1$-separated ($|x - y| \ge 1$ for $x \neq y \in A$), that `Nat.floor` is injective on $A$, and that $A \cap [1, x]$ is always finite with $(A \cap [1, x]).\mathrm{ncard} \le \lfloor x \rfloor_+$, establishing non-vacuity of the `Set.ncard` counting function in `Erdos143.erdos_143.parts.i`.
5. **Erdős Problem #834 (Part ii)** (*3-Chromatic-Critical 3-Uniform Hypergraph with Minimum Degree $\ge 7$*):
   - Using R. Li's 9-vertex, 22-edge 3-uniform hypergraph [arXiv:2512.24850], we certify via kernel `decide +kernel` that $\chi(H) = 3$, $\delta(H) \ge 7$, and deleting any edge or vertex renders $H$ 2-colorable.

---

## 2. Mathematical Formulations & Proofs

### 2.1 Erdős Problem #261: Borwein–Loring Telescoping Identity & Infinitude

A natural number $n$ satisfies `Erdos261Prop n` if there exist $t \ge 2$ and an injective sequence $a : \mathrm{Fin}\, t \to \mathbb{N}$ with $a_k \ge 1$ such that:
$$\frac{n}{2^n} = \sum_{k=0}^{t-1} \frac{a_k}{2^{a_k}}.$$

#### Telescoping Sum Lemma
Define the rational potential $F(k) = \frac{k + 2}{2^k}$. For every $k \ge 0$:
$$F(k) - F(k + 1) = \frac{k + 2}{2^k} - \frac{k + 3}{2^{k+1}} = \frac{2(k + 2) - (k + 3)}{2^{k+1}} = \frac{k + 1}{2^{k+1}}.$$
Summing over $i \in \{0, \ldots, m - 1\}$ (or equivalently $k = n + 1 + i \in (n, n + m]$) yields the exact telescoping identity (`sum_range_shifted_div_two_pow` and `sum_Ioc_div_two_pow`):
$$\sum_{k \in (n, n+m]} \frac{k}{2^k} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}.$$

#### The Borwein–Loring Sequence
For any integer $m \ge 1$, set $n_m = 2^{m+1} - m - 2$. Since $m + 1 < 2^{m+1}$ (`Nat.lt_two_pow_self`), we have $m + 2 \le 2^{m+1}$ in $\mathbb{N}$, so:
$$n_m + m + 2 = 2^{m+1}.$$
Substituting this into the telescoping identity gives:
$$\sum_{k \in (n_m, n_m + m]} \frac{k}{2^k} = \frac{n_m + 2}{2^{n_m}} - \frac{2^{m+1}}{2^{n_m + m}} = \frac{n_m + 2}{2^{n_m}} - \frac{2}{2^{n_m}} = \frac{n_m}{2^{n_m}}.$$
For $m \ge 2$, taking $t = m \ge 2$ and $a_i = n_m + 1 + i$ gives $m$ pairwise distinct positive integers satisfying `Erdos261Prop n_m` (`erdos_261_borwein_loring_property`). Since $k \mapsto n_{k+2} = 2^{k+3} - (k + 2) - 2$ is strictly increasing and positive (`borweinLoringSeq_strictMono`, `borweinLoringSeq_pos`), infinitely many positive integers satisfy `Erdos261Prop` (`erdos_261_parts_i`).

---

### 2.2 Erdős Problem #931: Equal Prime Factors of Consecutive Integer Blocks

For $k_1 \ge k_2 \ge 3$ and $n_2 \ge n_1 + k_1$, Erdős asked when the products of consecutive integers
$$P_1 = \prod_{i=1}^{k_1} (n_1 + i) \quad \text{and} \quad P_2 = \prod_{j=1}^{k_2} (n_2 + j)$$
have the same set of prime factors, and suggested that perhaps equality forces $n_2 > 2(n_1 + k_1)$ or at least the existence of a prime between the intervals.

1. **Symmetric Positive-Integer Counterexamples ($k_1 = k_2 = 3$)**:
   - $(n_1, n_2) = (2, 7)$: $P_1 = 3 \cdot 4 \cdot 5 = 60 = 2^2 \cdot 3 \cdot 5$ and $P_2 = 8 \cdot 9 \cdot 10 = 720 = 2^4 \cdot 3^2 \cdot 5$ both have prime factors $\{2, 3, 5\}$, while $n_1 + k_1 = 5 \le 7 = n_2 \le 10 = 2(n_1 + k_1)$ (`erdos_931_counterexample_symmetric_2_7`).
   - $(n_1, n_2) = (3, 7)$: $P_1 = 4 \cdot 5 \cdot 6 = 120 = 2^3 \cdot 3 \cdot 5$ and $P_2 = 8 \cdot 9 \cdot 10 = 720$ both have prime factors $\{2, 3, 5\}$, with $n_1 + k_1 = 6$ and $n_2 = 7$. The open interval $(n_1 + k_1, n_2) = (6, 7)$ strictly between the two blocks contains **no integer and hence no prime** (`erdos_931_counterexample_no_strict_between_prime`).
2. **Prime Existence in the Bertrand Regime ($2 n_1 \le n_2$)**:
   - In *Formal Conjectures*, `erdos_931.variants.exists_prime` asks for a prime $p$ satisfying $n_1 \le p \le n_2$. Using Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), we prove that whenever $1 \le n_1$ and $2 n_1 \le n_2$, there always exists a prime $p \in (n_1, 2 n_1] \subseteq [n_1, n_2]$ (`erdos_931_exists_prime_of_two_mul_le`).

---

### 2.3 Erdős Problem #951: Constructive Linear Growth of 1-Separated Beurling Primes

A strictly increasing sequence $a : \mathbb{N} \to \mathbb{R}$ with $1 < a(0)$ satisfies `Erdos951Prop a` if for all distinct finitely supported exponent vectors $k \neq \ell : \mathbb{N} \to_0 \mathbb{N}$,
$$\left|\prod_{i} a(i)^{k(i)} - \prod_{i} a(i)^{\ell(i)}\right| \ge 1.$$

Evaluating `Erdos951Prop a` at the singleton exponent vectors $k = \mathrm{single}(n+1, 1)$ and $\ell = \mathrm{single}(n, 1)$ yields:
$$a(n + 1) - a(n) = |a(n + 1) - a(n)| \ge 1 \quad \forall n \in \mathbb{N}.$$
By induction on $n$, we obtain the explicit linear lower bound (`erdos_951_linear_lower_bound`):
$$a(n) \ge a(0) + n \quad \forall n \in \mathbb{N},$$
from which $\lim_{n \to \infty} a(n) = +\infty$ (`IsBeurlingPrimes a`, theorem `erdos_951_isBeurlingPrimes`) follows immediately by `tendsto_atTop_mono`.

---

### 2.4 Erdős Problem #143: Floor Injectivity and Non-Vacuity for Well-Separated Sets

A countably infinite set $A \subseteq (1, \infty)$ satisfies `WellSeparatedSet A` if $|k x - y| \ge 1$ for all distinct $x, y \in A$ and all integers $k \ge 1$.
1. Specializing $k = 1$ gives $1 \le |x - y|$ for all distinct $x, y \in A$ (`erdos_143_one_separated`).
2. Since any two real numbers $x, y \ge 0$ with $\lfloor x \rfloor_+ = \lfloor y \rfloor_+$ satisfy $|x - y| < 1$, the map `Nat.floor : ℝ → ℕ` is injective on $A$ (`erdos_143_floor_injOn`).
3. Consequently, for every $x \in \mathbb{R}$, $A \cap [1, x]$ maps injectively into $\mathrm{Finset.Icc}\, 1\, \lfloor x \rfloor_+$, proving both `(A ∩ Set.Icc 1 x).Finite` and the explicit counting bound:
   $$(A \cap [1, x]).\mathrm{ncard} \le \lfloor x \rfloor_+$$
   (`erdos_143_ncard_le_floor`). This guarantees that `Set.ncard` in `Erdos143.erdos_143.parts.i` never takes the junk value $0$ due to an infinite intersection.

---

### 2.5 Erdős Problem #834 (Part ii): Li's 3-Chromatic-Critical 3-Uniform Hypergraph

We include R. Li's 9-vertex, 22-edge 3-uniform hypergraph `liH` (`erdos_834_parts_ii`), where every finite property—3-uniformity, minimum degree $\ge 7$ (degrees $10, 7^8$), 3-colorability, non-2-colorability across all $2^9 = 512$ 2-colorings, and 2-colorability after deleting each of the 22 edges or 9 vertices—is verified by Lean's kernel via `decide +kernel`.

---

## 3. Verification & Axiom Audit

### 3.1 `ctrl-erdos-lab` Verification (Local Mac + Remote `sparky.local`)

In `/Users/mike/Dev/ctrl-erdos-lab`, challenges `261`, `931`, and `834` are registered, approved, and verified via `uv run ctrl check --all` and `uv run ctrl spark check`:

| Problem | FC Target | File | Build | Tokens | Axioms | Binding | Hash |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **#261** | `Erdos261.erdos_261.parts.i` | `erdos/ErdosLab/Erdos261.lean` | Pass | Pass | Pass | Pass | Pass |
| **#931** | `Erdos931.erdos_931.variants.additional_condition_nonempty` | `erdos/ErdosLab/Erdos931.lean` | Pass | Pass | Pass | Pass | Pass |
| **#834** | `Erdos834.erdos_834.parts.ii` | `erdos/ErdosLab/Erdos834.lean` | Pass | Pass | Pass | Pass | Pass |

### 3.2 `ControlsLean/Bounty/ErdosBounties.lean` Axiom Footprint

All headline theorems in `ControlsLean/Bounty/ErdosBounties.lean` compile cleanly under `lake env lean ControlsLean/Bounty/ErdosBounties.lean` and depend only on standard Lean 4 axioms:

```lean
#print axioms ControlsLean.Bounty.sum_range_shifted_div_two_pow
-- 'ControlsLean.Bounty.sum_range_shifted_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.sum_Ioc_div_two_pow
-- 'ControlsLean.Bounty.sum_Ioc_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_261_borwein_loring
-- 'ControlsLean.Bounty.erdos_261_borwein_loring' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_261_borwein_loring_property
-- 'ControlsLean.Bounty.erdos_261_borwein_loring_property' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_261_parts_i
-- 'ControlsLean.Bounty.erdos_261_parts_i' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_261_rafik_split
-- 'ControlsLean.Bounty.erdos_261_rafik_split' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_931_counterexample_symmetric_2_7
-- 'ControlsLean.Bounty.erdos_931_counterexample_symmetric_2_7' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_931_counterexample_no_strict_between_prime
-- 'ControlsLean.Bounty.erdos_931_counterexample_no_strict_between_prime' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_931_additional_condition_nonempty
-- 'ControlsLean.Bounty.erdos_931_additional_condition_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_931_exists_prime_of_two_mul_le
-- 'ControlsLean.Bounty.erdos_931_exists_prime_of_two_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_951_step_gap
-- 'ControlsLean.Bounty.erdos_951_step_gap' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_951_linear_lower_bound
-- 'ControlsLean.Bounty.erdos_951_linear_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_951_isBeurlingPrimes
-- 'ControlsLean.Bounty.erdos_951_isBeurlingPrimes' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_143_one_separated
-- 'ControlsLean.Bounty.erdos_143_one_separated' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_143_floor_injOn
-- 'ControlsLean.Bounty.erdos_143_floor_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_143_ncard_le_floor
-- 'ControlsLean.Bounty.erdos_143_ncard_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms ControlsLean.Bounty.erdos_834_parts_ii
-- 'ControlsLean.Bounty.erdos_834_parts_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
```
