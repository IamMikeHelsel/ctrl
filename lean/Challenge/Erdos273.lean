import FormalConjectures.ErdosProblems.«273»

/-!
# Challenge: Erdős Problem 273 (variant three)

Statement copied verbatim from `Erdos273.erdos_273.variants.three` in
FormalConjectures.ErdosProblems.«273» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/273
-/

open Erdos273

namespace Challenge.Erdos273

/-- statement copied from FormalConjectures.ErdosProblems.«273» `erdos_273.variants.three`
(Apache-2.0) -/
def statement : Prop :=
    ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
      c.moduli i = Ideal.span {↑(p - 1)}

-- approved-by: (pending)

end Challenge.Erdos273
