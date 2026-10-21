import Mathlib.Tactic

namespace M08
/-- Basis convention: orientation theta0 wedge ... wedge theta13,
seven positive then seven negative metric entries. This is a declared basis
Hodge normalization, not a proof that the draft selects these conventions. -/
def inversions (I J : Finset (Fin 14)) : ℕ :=
  ((I ×ˢ J).filter (fun p => p.2 < p.1)).card

def hodgeSign (I : Finset (Fin 14)) : ℤ :=
  (-1)^(inversions I Iᶜ + (I.filter (fun i => 7 ≤ i.val)).card)

def wedgeSign (I J : Finset (Fin 14)) : ℤ :=
  if Disjoint I J then (-1)^(inversions I J) else 0

theorem mixed_two_form_star : hodgeSign {0,7} = -1 := by decide

theorem mixed_vector_left_contraction :
    hodgeSign {0,7} * wedgeSign {0} ({0,7}ᶜ) *
      hodgeSign ({0} ∪ ({0,7}ᶜ)) = -1 := by decide

theorem mixed_vector_right_contraction :
    hodgeSign {0,7} * wedgeSign {7} ({0,7}ᶜ) *
      hodgeSign ({7} ∪ ({0,7}ᶜ)) = -1 := by decide

theorem mixed_double_contraction :
    hodgeSign {0,7} * wedgeSign {0,7} ({0,7}ᶜ) *
      hodgeSign Finset.univ = 1 := by decide

theorem hodge_square_relevant_degrees :
    ((-1:ℤ)^(0*(14-0)+7) = -1) ∧
    ((-1:ℤ)^(1*(14-1)+7) = 1) ∧
    ((-1:ℤ)^(2*(14-2)+7) = -1) ∧
    ((-1:ℤ)^(13*(14-13)+7) = 1) ∧
    ((-1:ℤ)^(14*(14-14)+7) = -1) := by norm_num

/-- Coefficient-level assembly after the separately checked Hodge legs. -/
theorem assembled_sign (C D : ℝ) : -C-(1/2)*(-D)=-(C-(1/2)*D) := by ring

#print axioms mixed_two_form_star
#print axioms mixed_vector_left_contraction
#print axioms mixed_vector_right_contraction
#print axioms mixed_double_contraction
#print axioms hodge_square_relevant_degrees
#print axioms assembled_sign
end M08
