import FormalConjectures.ErdosProblems.«382»

/-!
# Challenge: Erdős Problem 382 (`lt_two_mul_of_largestPrimeRepeated`)

Statement copied verbatim from `Erdos382.lt_two_mul_of_largestPrimeRepeated` in
FormalConjectures.ErdosProblems.«382» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/382
-/

open Erdos382

namespace Challenge.Erdos382

/-- statement copied from FormalConjectures.ErdosProblems.«382»
`lt_two_mul_of_largestPrimeRepeated` (Apache-2.0) -/
def statement : Prop :=
    ∀ {u v : ℕ}, LargestPrimeRepeated u v → v < 2 * u

-- approved-by: mike 2026-10-18

end Challenge.Erdos382
