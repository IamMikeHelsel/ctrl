import FormalConjectures.ErdosProblems.«931»

/-!
# Challenge: Erdős Problem 931 (variant additional_condition_nonempty)

Statement copied verbatim from `Erdos931.erdos_931.variants.additional_condition_nonempty` in
FormalConjectures.ErdosProblems.«931» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/931
-/

open Erdos931

namespace Challenge.Erdos931

/-- statement copied from FormalConjectures.ErdosProblems.«931» `erdos_931.variants.additional_condition_nonempty`
(Apache-2.0) -/
def statement : Prop :=
    ∃ (k₁ k₂ : ℕ), ∃ (_h₁ : k₂ ≤ k₁), ∃ (_h₂ : 3 ≤ k₂),
      {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
          (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
          (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty

-- approved-by: mike 2026-10-17

end Challenge.Erdos931
