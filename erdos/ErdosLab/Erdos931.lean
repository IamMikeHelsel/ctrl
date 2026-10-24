import Challenge.Erdos931

/-!
# Erdős Problem 931 (Counterexamples & Prime-Existence Regime)

Erdős asked whether for $k_1 \ge k_2 \ge 3$ and $n_2 \ge n_1 + k_1$, equal prime factors of
$$\prod_{i=1}^{k_1} (n_1 + i) \quad \text{and} \quad \prod_{j=1}^{k_2} (n_2 + j)$$
force $n_2 > 2(n_1 + k_1)$.

While Formal Conjectures recorded AlphaProof's degenerate $n_1 = 0$ counterexample
$(k_1, k_2, n_1, n_2) = (10, 3, 0, 13)$, our search found positive-integer symmetric
$k_1 = k_2 = 3$ counterexamples including:
- $(k_1, k_2, n_1, n_2) = (3, 3, 2, 7)$: $3 \cdot 4 \cdot 5 = 60$ and $8 \cdot 9 \cdot 10 = 720$
  both have prime factors $\{2, 3, 5\}$, with $2 + 3 \le 7 \le 2(2 + 3) = 10$.
- $(k_1, k_2, n_1, n_2) = (3, 3, 3, 7)$: $4 \cdot 5 \cdot 6 = 120$ and $8 \cdot 9 \cdot 10 = 720$
  both have prime factors $\{2, 3, 5\}$, with $3 + 3 = 6 < 7 = n_2 \le 12$, so there is no integer
  (and hence no prime) strictly between $n_1 + k_1 = 6$ and $n_2 = 7$.
-/

namespace Challenge.Erdos931

/-- Symmetric $k_1 = k_2 = 3$ positive-integer counterexample $(n_1, n_2) = (2, 7)$. -/
private theorem counterexample_3_3_2_7 :
    (2, 7) ∈ {(n₁, n₂) : ℕ × ℕ | n₁ + 3 ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + 3) ∧
      (∏ i ∈ Finset.Icc 1 3, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 3, (n₂ + j)).primeFactors} := by
  simp only [Set.mem_setOf_eq]
  refine ⟨by decide, by decide, ?_⟩
  decide +kernel

/-- Adjacent-gap $k_1 = k_2 = 3$ counterexample $(n_1, n_2) = (3, 7)$ where $(n_1 + k_1, n_2) = (6, 7)$
contains no integer (and hence no prime) strictly between the two blocks. -/
private theorem counterexample_3_3_3_7_no_strict_between_prime :
    ((3, 7) ∈ {(n₁, n₂) : ℕ × ℕ | n₁ + 3 ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + 3) ∧
      (∏ i ∈ Finset.Icc 1 3, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 3, (n₂ + j)).primeFactors}) ∧
    ¬ ∃ p : ℕ, p.Prime ∧ 3 + 3 < p ∧ p < 7 := by
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    refine ⟨by decide, by decide, ?_⟩
    decide +kernel
  · rintro ⟨p, _, hp1, hp2⟩
    omega

theorem solution : statement := by
  refine ⟨3, 3, le_rfl, le_rfl, ⟨(2, 7), counterexample_3_3_2_7⟩⟩

end Challenge.Erdos931
