# Erdős Problem 931 (`additional_condition_nonempty`): Counterexamples with Equal Prime Factors

Source: <https://www.erdosproblems.com/931> · FC: `Erdos931.erdos_931.variants.additional_condition_nonempty`
(`FormalConjectures/ErdosProblems/931.lean` @ `d9ce556`).

## Why
- Tagged `category research solved` in Formal Conjectures.
- Formal Conjectures used AlphaProof's degenerate $n_1 = 0, k_1 = 10, k_2 = 3, n_2 = 13$ witness.
- A targeted Python search found non-degenerate positive-integer symmetric $k_1 = k_2 = 3$
  counterexamples $(n_1, n_2) = (2, 7)$ and $(3, 7)$, where $(3, 7)$ also has an empty open interval
  $(n_1 + k_1, n_2) = (6, 7)$ containing no prime.

## Statement review
FC statement (copied verbatim into `erdos/Challenge/Erdos931.lean`):
```lean
∃ (k₁ k₂ : ℕ), ∃ (_h₁ : k₂ ≤ k₁), ∃ (_h₂ : 3 ≤ k₂),
  {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty
```
- Faithfully captures counterexamples to Erdős's suggestion that equal prime factors of
  $\prod_{i=1}^{k_1}(n_1 + i)$ and $\prod_{j=1}^{k_2}(n_2 + j)$ should force $n_2 > 2(n_1 + k_1)$.
- Approved by `mike`.

## Blueprint (lemma DAG)
- `counterexample_3_3_2_7` (*search*): kernel `decide +kernel` check for $k_1 = k_2 = 3, (n_1, n_2) = (2, 7)$.
- `counterexample_3_3_3_7_no_strict_between_prime` (*search*): kernel `decide +kernel` check for
  $k_1 = k_2 = 3, (n_1, n_2) = (3, 7)$ plus `omega` refutation of any prime in $(6, 7)$.
- `solution` (*elementary*): packages `⟨3, 3, le_rfl, le_rfl, ⟨(2, 7), counterexample_3_3_2_7⟩⟩`.
