import FormalConjectures.ErdosProblems.«261»

/-!
# Challenge: Erdős Problem 261 (part i)

Statement copied verbatim from `Erdos261.erdos_261.parts.i` in
FormalConjectures.ErdosProblems.«261» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/261
-/

open Erdos261
open scoped Cardinal

namespace Challenge.Erdos261

/-- statement copied from FormalConjectures.ErdosProblems.«261» `erdos_261.parts.i`
(Apache-2.0) -/
def statement : Prop :=
    {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite

-- approved-by: mike 2026-10-17

end Challenge.Erdos261
