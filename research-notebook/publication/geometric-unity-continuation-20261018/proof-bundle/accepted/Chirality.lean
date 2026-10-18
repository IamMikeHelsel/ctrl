import SkewLie
noncomputable section
namespace HyperbolicSpinor
open GUClifford

def chirality : Cl := gamma 0 * gamma 1 * gamma 2 * gamma 3 * gamma 4 * gamma 5 * gamma 6 * gamma 7 * gamma 8 * gamma 9 * gamma 10 * gamma 11 * gamma 12 * gamma 13

theorem gamma_square_right (i : Ix) (X : Cl) :
    gamma i * (gamma i * X) = eps i • X := by
  rw [← mul_assoc, gamma_sq, smul_mul_assoc, one_mul]

theorem gamma_swap_right (i j : Ix) (h : i ≠ j) (X : Cl) :
    gamma i * (gamma j * X) = -(gamma j * (gamma i * X)) := by
  rw [← mul_assoc, gamma_swap i j h, neg_mul, mul_assoc]

local macro "clifford_nf" : tactic => `(tactic| norm_num [chirality,
    mul_assoc,
    neg_mul,
    mul_neg,
    neg_neg,
    one_mul,
    mul_one,
    gamma_sq,
    gamma_square_right,
    eps,
    smul_neg,
    neg_smul,
    one_smul,
    gamma_swap_right 1 0 (by decide),
    gamma_swap_right 2 0 (by decide),
    gamma_swap_right 2 1 (by decide),
    gamma_swap_right 3 0 (by decide),
    gamma_swap_right 3 1 (by decide),
    gamma_swap_right 3 2 (by decide),
    gamma_swap_right 4 0 (by decide),
    gamma_swap_right 4 1 (by decide),
    gamma_swap_right 4 2 (by decide),
    gamma_swap_right 4 3 (by decide),
    gamma_swap_right 5 0 (by decide),
    gamma_swap_right 5 1 (by decide),
    gamma_swap_right 5 2 (by decide),
    gamma_swap_right 5 3 (by decide),
    gamma_swap_right 5 4 (by decide),
    gamma_swap_right 6 0 (by decide),
    gamma_swap_right 6 1 (by decide),
    gamma_swap_right 6 2 (by decide),
    gamma_swap_right 6 3 (by decide),
    gamma_swap_right 6 4 (by decide),
    gamma_swap_right 6 5 (by decide),
    gamma_swap_right 7 0 (by decide),
    gamma_swap_right 7 1 (by decide),
    gamma_swap_right 7 2 (by decide),
    gamma_swap_right 7 3 (by decide),
    gamma_swap_right 7 4 (by decide),
    gamma_swap_right 7 5 (by decide),
    gamma_swap_right 7 6 (by decide),
    gamma_swap_right 8 0 (by decide),
    gamma_swap_right 8 1 (by decide),
    gamma_swap_right 8 2 (by decide),
    gamma_swap_right 8 3 (by decide),
    gamma_swap_right 8 4 (by decide),
    gamma_swap_right 8 5 (by decide),
    gamma_swap_right 8 6 (by decide),
    gamma_swap_right 8 7 (by decide),
    gamma_swap_right 9 0 (by decide),
    gamma_swap_right 9 1 (by decide),
    gamma_swap_right 9 2 (by decide),
    gamma_swap_right 9 3 (by decide),
    gamma_swap_right 9 4 (by decide),
    gamma_swap_right 9 5 (by decide),
    gamma_swap_right 9 6 (by decide),
    gamma_swap_right 9 7 (by decide),
    gamma_swap_right 9 8 (by decide),
    gamma_swap_right 10 0 (by decide),
    gamma_swap_right 10 1 (by decide),
    gamma_swap_right 10 2 (by decide),
    gamma_swap_right 10 3 (by decide),
    gamma_swap_right 10 4 (by decide),
    gamma_swap_right 10 5 (by decide),
    gamma_swap_right 10 6 (by decide),
    gamma_swap_right 10 7 (by decide),
    gamma_swap_right 10 8 (by decide),
    gamma_swap_right 10 9 (by decide),
    gamma_swap_right 11 0 (by decide),
    gamma_swap_right 11 1 (by decide),
    gamma_swap_right 11 2 (by decide),
    gamma_swap_right 11 3 (by decide),
    gamma_swap_right 11 4 (by decide),
    gamma_swap_right 11 5 (by decide),
    gamma_swap_right 11 6 (by decide),
    gamma_swap_right 11 7 (by decide),
    gamma_swap_right 11 8 (by decide),
    gamma_swap_right 11 9 (by decide),
    gamma_swap_right 11 10 (by decide),
    gamma_swap_right 12 0 (by decide),
    gamma_swap_right 12 1 (by decide),
    gamma_swap_right 12 2 (by decide),
    gamma_swap_right 12 3 (by decide),
    gamma_swap_right 12 4 (by decide),
    gamma_swap_right 12 5 (by decide),
    gamma_swap_right 12 6 (by decide),
    gamma_swap_right 12 7 (by decide),
    gamma_swap_right 12 8 (by decide),
    gamma_swap_right 12 9 (by decide),
    gamma_swap_right 12 10 (by decide),
    gamma_swap_right 12 11 (by decide),
    gamma_swap_right 13 0 (by decide),
    gamma_swap_right 13 1 (by decide),
    gamma_swap_right 13 2 (by decide),
    gamma_swap_right 13 3 (by decide),
    gamma_swap_right 13 4 (by decide),
    gamma_swap_right 13 5 (by decide),
    gamma_swap_right 13 6 (by decide),
    gamma_swap_right 13 7 (by decide),
    gamma_swap_right 13 8 (by decide),
    gamma_swap_right 13 9 (by decide),
    gamma_swap_right 13 10 (by decide),
    gamma_swap_right 13 11 (by decide),
    gamma_swap_right 13 12 (by decide),
    gamma_swap 1 0 (by decide),
    gamma_swap 2 0 (by decide),
    gamma_swap 2 1 (by decide),
    gamma_swap 3 0 (by decide),
    gamma_swap 3 1 (by decide),
    gamma_swap 3 2 (by decide),
    gamma_swap 4 0 (by decide),
    gamma_swap 4 1 (by decide),
    gamma_swap 4 2 (by decide),
    gamma_swap 4 3 (by decide),
    gamma_swap 5 0 (by decide),
    gamma_swap 5 1 (by decide),
    gamma_swap 5 2 (by decide),
    gamma_swap 5 3 (by decide),
    gamma_swap 5 4 (by decide),
    gamma_swap 6 0 (by decide),
    gamma_swap 6 1 (by decide),
    gamma_swap 6 2 (by decide),
    gamma_swap 6 3 (by decide),
    gamma_swap 6 4 (by decide),
    gamma_swap 6 5 (by decide),
    gamma_swap 7 0 (by decide),
    gamma_swap 7 1 (by decide),
    gamma_swap 7 2 (by decide),
    gamma_swap 7 3 (by decide),
    gamma_swap 7 4 (by decide),
    gamma_swap 7 5 (by decide),
    gamma_swap 7 6 (by decide),
    gamma_swap 8 0 (by decide),
    gamma_swap 8 1 (by decide),
    gamma_swap 8 2 (by decide),
    gamma_swap 8 3 (by decide),
    gamma_swap 8 4 (by decide),
    gamma_swap 8 5 (by decide),
    gamma_swap 8 6 (by decide),
    gamma_swap 8 7 (by decide),
    gamma_swap 9 0 (by decide),
    gamma_swap 9 1 (by decide),
    gamma_swap 9 2 (by decide),
    gamma_swap 9 3 (by decide),
    gamma_swap 9 4 (by decide),
    gamma_swap 9 5 (by decide),
    gamma_swap 9 6 (by decide),
    gamma_swap 9 7 (by decide),
    gamma_swap 9 8 (by decide),
    gamma_swap 10 0 (by decide),
    gamma_swap 10 1 (by decide),
    gamma_swap 10 2 (by decide),
    gamma_swap 10 3 (by decide),
    gamma_swap 10 4 (by decide),
    gamma_swap 10 5 (by decide),
    gamma_swap 10 6 (by decide),
    gamma_swap 10 7 (by decide),
    gamma_swap 10 8 (by decide),
    gamma_swap 10 9 (by decide),
    gamma_swap 11 0 (by decide),
    gamma_swap 11 1 (by decide),
    gamma_swap 11 2 (by decide),
    gamma_swap 11 3 (by decide),
    gamma_swap 11 4 (by decide),
    gamma_swap 11 5 (by decide),
    gamma_swap 11 6 (by decide),
    gamma_swap 11 7 (by decide),
    gamma_swap 11 8 (by decide),
    gamma_swap 11 9 (by decide),
    gamma_swap 11 10 (by decide),
    gamma_swap 12 0 (by decide),
    gamma_swap 12 1 (by decide),
    gamma_swap 12 2 (by decide),
    gamma_swap 12 3 (by decide),
    gamma_swap 12 4 (by decide),
    gamma_swap 12 5 (by decide),
    gamma_swap 12 6 (by decide),
    gamma_swap 12 7 (by decide),
    gamma_swap 12 8 (by decide),
    gamma_swap 12 9 (by decide),
    gamma_swap 12 10 (by decide),
    gamma_swap 12 11 (by decide),
    gamma_swap 13 0 (by decide),
    gamma_swap 13 1 (by decide),
    gamma_swap 13 2 (by decide),
    gamma_swap 13 3 (by decide),
    gamma_swap 13 4 (by decide),
    gamma_swap 13 5 (by decide),
    gamma_swap 13 6 (by decide),
    gamma_swap 13 7 (by decide),
    gamma_swap 13 8 (by decide),
    gamma_swap 13 9 (by decide),
    gamma_swap 13 10 (by decide),
    gamma_swap 13 11 (by decide),
    gamma_swap 13 12 (by decide)])

set_option maxHeartbeats 0 in
theorem chirality_square : chirality * chirality = 1 := by
  clifford_nf

set_option maxHeartbeats 0 in
theorem chirality_star : star chirality = -chirality := by
  have hg (i : Ix) : star (gamma i) = -gamma i := CliffordAlgebra.star_ι (e i)
  simp only [chirality, star_mul, hg]
  clifford_nf

set_option maxHeartbeats 0 in
theorem chirality_anticommutes_gamma (i : Ix) : chirality * gamma i = -(gamma i * chirality) := by
  fin_cases i
  · change chirality * gamma 0 = -(gamma 0 * chirality)
    clifford_nf
  · change chirality * gamma 1 = -(gamma 1 * chirality)
    clifford_nf
  · change chirality * gamma 2 = -(gamma 2 * chirality)
    clifford_nf
  · change chirality * gamma 3 = -(gamma 3 * chirality)
    clifford_nf
  · change chirality * gamma 4 = -(gamma 4 * chirality)
    clifford_nf
  · change chirality * gamma 5 = -(gamma 5 * chirality)
    clifford_nf
  · change chirality * gamma 6 = -(gamma 6 * chirality)
    clifford_nf
  · change chirality * gamma 7 = -(gamma 7 * chirality)
    clifford_nf
  · change chirality * gamma 8 = -(gamma 8 * chirality)
    clifford_nf
  · change chirality * gamma 9 = -(gamma 9 * chirality)
    clifford_nf
  · change chirality * gamma 10 = -(gamma 10 * chirality)
    clifford_nf
  · change chirality * gamma 11 = -(gamma 11 * chirality)
    clifford_nf
  · change chirality * gamma 12 = -(gamma 12 * chirality)
    clifford_nf
  · change chirality * gamma 13 = -(gamma 13 * chirality)
    clifford_nf

theorem chirality_anticommutes_vector (v : V) :
    chirality * CliffordAlgebra.ι Q v = -(CliffordAlgebra.ι Q v * chirality) := by
  rw [vector_expansion]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    chirality_anticommutes_gamma, smul_neg, Finset.sum_neg_distrib]

theorem chirality_commutes_bivector (v w : V) :
    chirality * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) =
      (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * chirality := by
  rw [← mul_assoc, chirality_anticommutes_vector, neg_mul, mul_assoc,
    chirality_anticommutes_vector, mul_neg, neg_neg, mul_assoc]

theorem chirality_twisted_vector_skew (v : V) :
    CliffordSkew (chirality * CliffordAlgebra.ι Q v) := by
  dsimp [CliffordSkew]
  rw [star_mul, chirality_star, CliffordAlgebra.star_ι, neg_mul_neg]
  have h := chirality_anticommutes_vector v
  simpa only [neg_neg] using (congrArg (fun x : Cl => -x) h).symm

theorem chirality_not_scalar (c : ℝ) : chirality ≠ c • (1 : Cl) := by
  intro h
  have ha := chirality_anticommutes_gamma 0
  rw [h] at ha
  have hb := congrArg (fun x : Cl => x * gamma 0) ha
  simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, neg_mul,
    gamma_sq] at hb
  norm_num [eps] at hb
  have hc : c = -c := (smul_left_injective ℝ (one_ne_zero : (1 : Cl) ≠ 0)) (by simpa only [neg_smul] using hb)
  have hz : c = 0 := by linarith
  have hs := chirality_square
  rw [h, hz, zero_smul, zero_mul] at hs
  exact zero_ne_one hs

theorem twisted_gamma_not_scalar_multiple (c : ℝ) :
    chirality * gamma 0 ≠ c • gamma 0 := by
  intro h
  have hh := congrArg (fun x : Cl => x * gamma 0) h
  rw [mul_assoc, gamma_sq, smul_mul_assoc, gamma_sq] at hh
  norm_num [eps] at hh
  exact chirality_not_scalar c hh

/-- Actual representation of the full volume; no abstract parity matrix is assumed. -/
def chiralityMatrix : SpinMatrix := splitMatrixEquiv chirality

theorem chiralityMatrix_square : chiralityMatrix * chiralityMatrix = 1 := by
  rw [chiralityMatrix, ← map_mul, chirality_square, map_one]

theorem chiralityMatrix_adjoint : realAdjoint chiralityMatrix = -chiralityMatrix := by
  change realAdjoint (splitMatrix chirality) = -splitMatrix chirality
  rw [← splitMatrix_star, chirality_star, map_neg]

theorem actual_twisted_matrix_skew (v : V) :
    FormSkew K (chiralityMatrix * splitMatrixEquiv (CliffordAlgebra.ι Q v)) := by
  rw [chiralityMatrix, ← map_mul, ← cliffordSkew_iff_formSkew]
  exact chirality_twisted_vector_skew v

/-- Infinitesimal conjugation by each actual vector product commutes with the twist. -/
theorem bivector_commutator_twist (v w : V) (x : Cl) :
    (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * (chirality * x) -
      (chirality * x) * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) =
      chirality * ((CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * x -
        x * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w)) := by
  rw [mul_sub, ← mul_assoc (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w),
    ← chirality_commutes_bivector, mul_assoc, mul_assoc]
  simp only [mul_assoc]

end HyperbolicSpinor
