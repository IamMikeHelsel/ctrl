import FormalConjectures.ErdosProblems.«318»

/-!
# Challenge: Erdős Problem 318 (variant contain_single_even)

Statement copied verbatim from `Erdos318.erdos_318.variants.contain_single_even` in
FormalConjectures.ErdosProblems.«318» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/318
-/

open Erdos318
open Set Real

namespace Challenge.Erdos318

/-- statement copied from FormalConjectures.ErdosProblems.«318» `erdos_318.variants.contain_single_even`
(Apache-2.0) -/
def statement : Prop :=
    ∀ {A : Set ℕ} (hA : A.Infinite)
      (hA' : {n | n ∈ A \ {0} ∧ Even n}.ncard = 1),
      ¬ P₁ A

-- approved-by: (pending)

end Challenge.Erdos318
