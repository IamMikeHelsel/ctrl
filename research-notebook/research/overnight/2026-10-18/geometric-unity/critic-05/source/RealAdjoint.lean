import VolumeForm

noncomputable section
open scoped BigOperators
namespace HyperbolicSpinor
open GUClifford

/-- The form adjoint uses the actual negative-generator product, on both sides. -/
def realAdjoint : SpinMatrix →ₗ[ℝ] SpinMatrix where
  toFun A := K * A.transpose * K
  map_add' A B := by simp [Matrix.transpose_add, mul_add, add_mul]
  map_smul' c A := by simp [Matrix.transpose_smul]

@[simp] theorem realAdjoint_apply (A : SpinMatrix) : realAdjoint A = K * A.transpose * K := rfl

theorem realAdjoint_one : realAdjoint 1 = 1 := by
  simp only [realAdjoint_apply, Matrix.transpose_one, mul_one, K_square]

theorem realAdjoint_mul (A B : SpinMatrix) : realAdjoint (A*B) = realAdjoint B * realAdjoint A := by
  simp only [realAdjoint_apply, Matrix.transpose_mul]
  calc
    K * (B.transpose * A.transpose) * K = K * B.transpose * (K*K) * A.transpose * K := by
      rw [K_square]
      simp only [mul_one, mul_assoc]
    _ = (K * B.transpose * K) * (K * A.transpose * K) := by
      simp only [mul_assoc]

theorem realAdjoint_positive (i : J) : realAdjoint (positiveMatrix i) = -positiveMatrix i := by
  rw [realAdjoint_apply, positive_transpose]
  calc
    K * positiveMatrix i * K = K * (positiveMatrix i * K) := mul_assoc _ _ _
    _ = K * (-(K * positiveMatrix i)) := by rw [K_anticommutes_positive]
    _ = -positiveMatrix i := by rw [mul_neg, ← mul_assoc, K_square, one_mul]

theorem realAdjoint_negative (i : J) : realAdjoint (negativeMatrix i) = -negativeMatrix i := by
  rw [realAdjoint_apply, negative_transpose, mul_neg, neg_mul,
    K_commutes_negative, mul_assoc, K_square, mul_one]

theorem realAdjoint_gamma (i : Ix) : realAdjoint (splitMatrix (gamma i)) = -splitMatrix (gamma i) := by
  refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
  · intro j
    exact realAdjoint_positive j
  · intro j
    simpa only [negativeMatrix, Fin.natAdd_eq_addNat] using realAdjoint_negative j

theorem vector_expansion (v : V) : CliffordAlgebra.ι Q v = ∑ i : Ix, (v i) • gamma i := by
  have hv : v = ∑ i : Ix, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, gamma]

theorem realAdjoint_vector (v : V) :
    realAdjoint (splitMatrix (CliffordAlgebra.ι Q v)) = -splitMatrix (CliffordAlgebra.ι Q v) := by
  rw [vector_expansion]
  simp only [map_sum, map_smul, realAdjoint_gamma, smul_neg, Finset.sum_neg_distrib]

/-- Clifford conjugation of every real element is the actual matrix form adjoint. -/
theorem splitMatrix_star (x : Cl) : splitMatrix (star x) = realAdjoint (splitMatrix x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.star_algebraMap, AlgHom.commutes]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, realAdjoint_one]
  | ι v =>
    rw [CliffordAlgebra.star_ι, map_neg, realAdjoint_vector]
  | mul a b ha hb =>
    rw [star_mul, map_mul, map_mul, realAdjoint_mul, ha, hb]
  | add a b ha hb =>
    rw [star_add, map_add, map_add, map_add, ha, hb]

/-- The statement is for the already proved concrete algebra equivalence. -/
theorem splitMatrixEquiv_star (x : Cl) :
    splitMatrixEquiv (star x) = K * (splitMatrixEquiv x).transpose * K := by
  exact splitMatrix_star x

theorem realAdjoint_involutive (A : SpinMatrix) : realAdjoint (realAdjoint A) = A := by
  obtain ⟨x, rfl⟩ := splitMatrix_surjective A
  rw [← splitMatrix_star, ← splitMatrix_star, star_star]

end HyperbolicSpinor
