import FormalConjectures.ErdosProblems.«885»

/-!
# Challenge: Erdős Problem 885 (variant k_eq_3)

Statement copied verbatim from `Erdos885.erdos_885.variants.k_eq_3` in
FormalConjectures.ErdosProblems.«885» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/885
-/

open Erdos885
open Nat Set Finset

namespace Challenge.Erdos885

/-- statement copied from FormalConjectures.ErdosProblems.«885» `erdos_885.variants.k_eq_3`
(Apache-2.0) -/
def statement : Prop :=
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3

-- approved-by: (pending)

end Challenge.Erdos885
