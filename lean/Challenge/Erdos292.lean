import FormalConjectures.ErdosProblems.«292»

/-!
# Challenge: Erdős Problem 292 (variant two_mul)

Statement copied verbatim from `Erdos292.erdos_292.variants.two_mul` in
FormalConjectures.ErdosProblems.«292» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/292
-/

open Erdos292
open Filter Asymptotics

namespace Challenge.Erdos292

/-- statement copied from FormalConjectures.ErdosProblems.«292» `erdos_292.variants.two_mul`
(Apache-2.0) -/
def statement : Prop :=
    ∀ n ∈ A, 1 < n → 2 * n ∈ A

-- approved-by: (pending)

end Challenge.Erdos292
