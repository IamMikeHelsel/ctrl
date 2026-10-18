import Chirality
noncomputable section
namespace ChiralityReview
open HyperbolicSpinor GUClifford

theorem chirality_nonzero : chirality ≠ (0 : Cl) := by
  intro h
  have hs := chirality_square
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem chirality_not_selfadjoint : star chirality ≠ chirality := by
  rw [chirality_star]
  intro h
  have hz : (2 : ℝ) • chirality = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h.symm
  exact chirality_nonzero ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem twisted_positive_square_negative :
    (chirality * gamma 0) * (chirality * gamma 0) = -(1 : Cl) := by
  calc
    (chirality * gamma 0) * (chirality * gamma 0) =
        (-(gamma 0 * chirality)) * (chirality * gamma 0) :=
          congrArg (fun x : Cl => x * (chirality * gamma 0)) (chirality_anticommutes_gamma 0)
    _ = -(gamma 0 * (chirality * chirality) * gamma 0) := by
          simp only [neg_mul, mul_assoc]
    _ = -(1 : Cl) := by rw [chirality_square, mul_one, gamma_sq]; norm_num [eps]

theorem twisted_positive_not_positive_square :
    (chirality * gamma 0) * (chirality * gamma 0) ≠ (1 : Cl) := by
  rw [twisted_positive_square_negative]
  intro h
  have hm := congrArg splitMatrixEquiv h
  have he := congrArg (fun A : SpinMatrix => A ∅ ∅) hm
  norm_num at he

end ChiralityReview
