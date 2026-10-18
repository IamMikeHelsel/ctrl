import ComplementAction

noncomputable section
open scoped BigOperators
open Matrix
namespace HyperbolicSpinor

/-- Presence of coordinate zero splits the 128 actual basis vectors into two halves. -/
def halfSign (T : Finset J) : ℝ := if (0 : J) ∈ T then -1 else 1

def D : SpinMatrix := Matrix.diagonal halfSign

theorem K_entry (I T : Finset J) :
    K I T = if I = Tᶜ then (complementSign T : ℝ) else 0 := by
  have h := congrFun (K_mulVec_basis T) I
  simpa [unitCoord, Matrix.mulVec_single_one, Pi.single_apply, Pi.smul_apply] using h

theorem halfSign_compl (T : Finset J) : halfSign Tᶜ = -halfSign T := by
  by_cases h : (0 : J) ∈ T <;> simp [halfSign, h]

theorem D_transpose : D.transpose = D := Matrix.diagonal_transpose _

theorem D_square : D * D = 1 := by
  rw [D, Matrix.diagonal_mul_diagonal]
  ext I T
  by_cases he : I = T
  · subst T
    by_cases h : (0 : J) ∈ I <;> simp [Matrix.diagonal_apply, Matrix.one_apply, halfSign, h]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, he]

theorem D_K_anticommute : D * K = -(K * D) := by
  ext I T
  simp only [D, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply]
  rw [K_entry]
  by_cases h : I = Tᶜ
  · subst I
    rw [ite_eq_left rfl, halfSign_compl]
    ring
  · rw [ite_eq_right h]
    simp

/-- Explicit paired columns. Each has support in T and its actual complement. -/
def U : SpinMatrix := 1 + K * D

theorem U_column (T : Finset J) :
    U *ᵥ unitCoord T = unitCoord T +
      (halfSign T * (complementSign T : ℝ)) • unitCoord Tᶜ := by
  simp only [U, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec]
  have hd : D *ᵥ unitCoord T = halfSign T • unitCoord T := by
    ext I
    simp [D, unitCoord, Pi.single_apply]
  rw [hd, Matrix.mulVec_smul, K_mulVec_basis, smul_smul]

theorem U_transpose : U.transpose = 1 + D * K := by
  simp only [U, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
    D_transpose, K_transpose]

theorem U_orthogonal_scaled : U.transpose * U = (2 : ℝ) • (1 : SpinMatrix) := by
  rw [U_transpose, U]
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one]
  have h : D * K * (K * D) = (1 : SpinMatrix) := by
    calc
      D * K * (K * D) = D * (K*K) * D := by simp only [mul_assoc]
      _ = 1 := by rw [K_square, mul_one, D_square]
  rw [h, D_K_anticommute]
  simp only [two_smul]
  abel

theorem U_orthogonal_scaled_right : U * U.transpose = (2 : ℝ) • (1 : SpinMatrix) := by
  rw [U_transpose, U]
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one]
  have h : K * D * (D * K) = (1 : SpinMatrix) := by
    calc
      K * D * (D * K) = K * (D*D) * K := by simp only [mul_assoc]
      _ = 1 := by rw [D_square, mul_one, K_square]
  rw [h, D_K_anticommute]
  simp only [two_smul]
  abel

theorem K_U : K * U = U * D := by
  simp only [U, mul_add, add_mul, mul_one, one_mul]
  rw [← mul_assoc, K_square, one_mul, mul_assoc, D_square, mul_one]
  exact add_comm _ _

/-- An explicit congruence for the existing K, not a separately postulated form. -/
theorem U_congruence : U.transpose * K * U = (2 : ℝ) • D := by
  rw [mul_assoc, K_U, ← mul_assoc, U_orthogonal_scaled, smul_mul_assoc, one_mul]

/-- Both inverse equations are proved for the explicit matrix. -/
def Uinverse : SpinMatrix := (1/2 : ℝ) • U.transpose

theorem Uinverse_left : Uinverse * U = 1 := by
  rw [Uinverse, smul_mul_assoc, U_orthogonal_scaled, smul_smul]
  norm_num

theorem Uinverse_right : U * Uinverse = 1 := by
  rw [Uinverse, mul_smul_comm, U_orthogonal_scaled_right, smul_smul]
  norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem positive_half_count : (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card = 64 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem negative_half_count : (Finset.univ.filter (fun T : Finset J => (0 : J) ∈ T)).card = 64 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem complementSign_compl : ∀ T : Finset J,
    complementSign Tᶜ = complementSign T := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem complementSign_square : ∀ T : Finset J,
    complementSign T * complementSign T = 1 := by decide

theorem positive_pair_column (T : Finset J) (h : (0 : J) ∉ T) :
    U *ᵥ unitCoord T = unitCoord T + (complementSign T : ℝ) • unitCoord Tᶜ := by
  rw [U_column]
  simp [halfSign, h]

theorem negative_pair_column (T : Finset J) (h : (0 : J) ∉ T) :
    U *ᵥ unitCoord Tᶜ = unitCoord Tᶜ - (complementSign T : ℝ) • unitCoord T := by
  rw [U_column, complementSign_compl]
  simp [halfSign, h, sub_eq_add_neg]

theorem U_congruence_entry (I T : Finset J) :
    (U.transpose * K * U) I T =
      if I = T then (if (0 : J) ∈ T then (-2 : ℝ) else 2) else 0 := by
  rw [U_congruence]
  by_cases he : I = T
  · subst T
    by_cases h : (0 : J) ∈ I <;> simp [D, halfSign, h]
  · simp [D, Matrix.diagonal_apply, he]

end HyperbolicSpinor
