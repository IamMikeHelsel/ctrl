import SpinEquivariance

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- A rational inner change of Clifford realization; not asserted to be a Spin element. -/
def boostElement : Cl := (2 : ℝ) • (1 : Cl) + chirality
def boostInverse : Cl := (1/3 : ℝ) • ((2 : ℝ) • (1 : Cl) - chirality)

theorem boost_right_inverse : boostElement * boostInverse = 1 := by
  simp only [boostElement, boostInverse, mul_smul_comm, mul_sub, add_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, chirality_square]
  module

theorem boost_left_inverse : boostInverse * boostElement = 1 := by
  simp only [boostElement, boostInverse, smul_mul_assoc, sub_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, chirality_square]
  module

def rationalBoost : Clˣ where
  val := boostElement
  inv := boostInverse
  val_inv := boost_right_inverse
  inv_val := boost_left_inverse

/-- A nontrivial quadratic-form-preserving twist is an actual inner conjugation. -/
theorem rationalBoost_vector (v : V) :
    boostElement * CliffordAlgebra.ι Q v * boostInverse =
      (5/3 : ℝ) • CliffordAlgebra.ι Q v +
        (4/3 : ℝ) • (chirality * CliffordAlgebra.ι Q v) := by
  have ha : CliffordAlgebra.ι Q v * chirality = -(chirality * CliffordAlgebra.ι Q v) := by
    have h := chirality_anticommutes_vector v
    simpa only [neg_neg] using (congrArg (fun x : Cl => -x) h).symm
  have ht : chirality * CliffordAlgebra.ι Q v * chirality = -CliffordAlgebra.ι Q v := by
    rw [mul_assoc, ha, mul_neg, ← mul_assoc, chirality_square, one_mul]
  simp only [boostElement, boostInverse, mul_smul_comm, mul_sub, add_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ht, ha]
  module

theorem boost_commutes_spin (s : Cl) (hs : s ∈ spinGroup Q) :
    boostElement * s = s * boostElement := by
  simp only [boostElement, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, chirality_commutes_spin s hs]

/-- The unnormalized conjugating unit has adjoint norm three, not one. -/
theorem boost_star_mul : star boostElement * boostElement = (3 : ℝ) • (1 : Cl) := by
  simp only [boostElement, star_add, star_smul, star_trivial, star_one, chirality_star,
    add_mul, mul_add, neg_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    chirality_square]
  module

/-- Its actual real matrix preserves K up to the positive factor three. -/
theorem boost_matrix_conformal :
    (splitMatrixEquiv boostElement).transpose * K * splitMatrixEquiv boostElement =
      (3 : ℝ) • K := by
  have h := congrArg splitMatrixEquiv boost_star_mul
  rw [map_mul, splitMatrixEquiv_star, map_smul, map_one] at h
  have hh := congrArg (fun M : SpinMatrix => K*M) h
  simpa only [← mul_assoc, K_square, one_mul, mul_smul_comm, mul_one] using hh

end HyperbolicSpinor
