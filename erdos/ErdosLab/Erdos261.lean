import Challenge.Erdos261

/-!
# Erdős Problem 261 (Part i & Borwein–Loring Construction)

We formalize the Borwein–Loring telescoping construction [BoLo90]: for every integer $m \ge 1$
and $n = 2^{m+1} - m - 2$,
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$
For $m \ge 2$, this representation has $m \ge 2$ distinct positive integer terms $a_i = n + 1 + i$,
establishing `Erdos261Prop (2 ^ (m + 1) - m - 2)` and hence `Erdos261.erdos_261.parts.i`:
infinitely many positive integers $n$ satisfy `Erdos261Prop n`.
-/

open Erdos261

namespace Challenge.Erdos261

/-- Telescoping sum over `Finset.range m`:
$\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}$. -/
private theorem sum_range_shifted_div_two_pow (n m : ℕ) :
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
private theorem sum_Ioc_div_two_pow (n m : ℕ) :
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

/-- Proof of `Erdos261.erdos_261.variants.borwein_loring`: for every $m > 0$ and
$n = 2^{m+1} - m - 2$, $n / 2^n = \sum_{k \in (n, n+m]} k / 2^k$. -/
theorem borwein_loring (m : ℕ) (_hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
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

/-- Proof of `Erdos261.erdos_261.variants.borwein_loring_property`: for $m \ge 2$,
$2^{m+1} - m - 2$ satisfies `Erdos261Prop`. -/
theorem borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
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

private def blSeq (k : ℕ) : ℕ := 2 ^ (k + 3) - (k + 2) - 2

private theorem blSeq_strictMono : StrictMono blSeq := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  dsimp [blSeq]
  have h1 : k + 3 < 2 ^ (k + 3) := Nat.lt_two_pow_self
  have h2 : 2 ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by
    have : k + 1 + 3 = (k + 3) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  omega

private theorem blSeq_pos (k : ℕ) : 0 < blSeq k := by
  have h0 : 0 < blSeq 0 := by decide
  exact lt_of_lt_of_le h0 (blSeq_strictMono.monotone (Nat.zero_le k))

theorem solution : statement := by
  refine Set.infinite_of_injective_forall_mem blSeq_strictMono.injective fun k => ?_
  exact ⟨blSeq_pos k, borwein_loring_property (k + 2) (by omega)⟩

end Challenge.Erdos261
