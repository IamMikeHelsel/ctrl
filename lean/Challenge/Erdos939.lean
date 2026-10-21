import FormalConjectures.ErdosProblems.«939»

/-!
# Challenge: Erdős Problem 939 (variant finite)

Statement copied verbatim from `Erdos939.erdos_939.variants.finite` in
FormalConjectures.ErdosProblems.«939» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/939
-/

open Erdos939
open Nat

namespace Challenge.Erdos939

/-- statement copied from FormalConjectures.ErdosProblems.«939» `erdos_939.variants.finite`
(Apache-2.0) -/
def statement : Prop :=
    ¬ ∀ r ≥ 4, (Erdos939Sums r).Finite

-- approved-by: (pending)

end Challenge.Erdos939
