import FormalConjectures.ErdosProblems.«834»

/-!
# Challenge: Erdős Problem 834 (part ii)

Statement copied verbatim from `Erdos834.erdos_834.parts.ii` in
FormalConjectures.ErdosProblems.«834» (google-deepmind/formal-conjectures @ d9ce556, Apache-2.0).
Source: https://www.erdosproblems.com/834
-/

open Erdos834
open Filter Asymptotics

namespace Challenge.Erdos834

/-- statement copied from FormalConjectures.ErdosProblems.«834» `erdos_834.parts.ii`
(Apache-2.0) -/
def statement : Prop :=
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform 3 ∧ H.HasHypergraphChromaticNumber 3 ∧
      (∀ e ∈ H, (H.erase e).HypergraphColorable 2) ∧
      (∀ v : Fin n, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable 2) ∧
      ∀ v : Fin n, 7 ≤ H.hypergraphDegree v

-- approved-by: mike 2026-10-17

end Challenge.Erdos834
