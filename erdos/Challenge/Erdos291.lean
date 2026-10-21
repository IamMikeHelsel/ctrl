import FormalConjectures.ErdosProblems.«291»

/-!
# Challenge: Erdős Problem 291 (part ii)

Statement copied verbatim from `Erdos291.erdos_291.parts.ii` in
FormalConjectures.ErdosProblems.«291» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/291
-/

open Erdos291

namespace Challenge.Erdos291

/-- statement copied from FormalConjectures.ErdosProblems.«291» `erdos_291.parts.ii`
(Apache-2.0) -/
def statement : Prop :=
    { n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite

-- approved-by: mike 2026-10-18

end Challenge.Erdos291
