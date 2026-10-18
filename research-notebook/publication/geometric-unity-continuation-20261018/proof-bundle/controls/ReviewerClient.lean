import SignatureControls
import OrderControls
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
namespace ReviewerSignature

theorem actual_order : K = negativeMatrix 0 * negativeMatrix 1 * negativeMatrix 2 *
    negativeMatrix 3 * negativeMatrix 4 * negativeMatrix 5 * negativeMatrix 6 := rfl

theorem actual_negative_action (i : J) (T : Finset J) :
    (create i - annihilate i) (spinBasis T) =
      (toggleSign i T : ℝ) • spinBasis (toggle i T) := negative_basis i T

theorem actual_K_entry (I T : Finset J) :
    K I T = if I = Tᶜ then (complementSign T : ℝ) else 0 := K_entry I T

theorem singleton_last_sign : K *ᵥ unitCoord {6} = -unitCoord ({6} : Finset J)ᶜ := by
  rw [K_mulVec_basis]
  norm_num [complementSign]

theorem two_ends_sign : K *ᵥ unitCoord {0,6} = unitCoord ({0,6} : Finset J)ᶜ := by
  rw [K_mulVec_basis]
  norm_num [complementSign]

theorem actual_eigen_columns (T : Finset J) :
    K *ᵥ (U *ᵥ unitCoord T) = halfSign T • (U *ᵥ unitCoord T) := by
  rw [Matrix.mulVec_mulVec, K_U, ← Matrix.mulVec_mulVec]
  have hd : D *ᵥ unitCoord T = halfSign T • unitCoord T := by
    ext I
    simp [D, unitCoord, Pi.single_apply]
  rw [hd, Matrix.mulVec_smul]

theorem negative_eigen_column : K *ᵥ (U *ᵥ unitCoord {0}) = -(U *ᵥ unitCoord {0}) := by
  rw [actual_eigen_columns]
  simp [halfSign]

theorem left_norm : U.transpose * U = (2 : ℝ) • (1 : SpinMatrix) := U_orthogonal_scaled

theorem right_norm : U * U.transpose = (2 : ℝ) • (1 : SpinMatrix) := U_orthogonal_scaled_right

theorem explicit_left_inverse : ((1/2 : ℝ) • U.transpose) * U = 1 := Uinverse_left

theorem explicit_right_inverse : U * ((1/2 : ℝ) • U.transpose) = 1 := Uinverse_right

theorem actual_congruence : U.transpose * K * U = (2 : ℝ) • D := U_congruence

theorem real_negative_value : (U.transpose * K * U) {0,6} {0,6} = -2 := by
  rw [U_congruence_entry]
  simp

theorem real_positive_value : (U.transpose * K * U) {1,6} {1,6} = 2 := by
  rw [U_congruence_entry]
  norm_num

theorem zero_cross_value : (U.transpose * K * U) {1} {0} = 0 := by
  rw [U_congruence_entry]
  norm_num

theorem exactly_two_halves :
    (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card = 64 ∧
    (Finset.univ.filter (fun T : Finset J => (0 : J) ∈ T)).card = 64 :=
  ⟨positive_half_count, negative_half_count⟩

theorem complex_form_unchanged : Kc = realToComplexMatrix K := rfl

theorem complex_congruence : Uc.conjTranspose * Kc * Uc = (2 : ℂ) • Dc := Uc_congruence

theorem complex_left_inverse : ((1/2 : ℂ) • Uc.conjTranspose) * Uc = 1 := by
  rw [← Ucinverse_formula, Ucinverse_left]

theorem complex_right_inverse : Uc * ((1/2 : ℂ) • Uc.conjTranspose) = 1 := by
  rw [← Ucinverse_formula, Ucinverse_right]

theorem complex_negative_value : (Uc.conjTranspose * Kc * Uc) {0,6} {0,6} = -2 := by
  rw [Uc_congruence_entry]
  simp

theorem projector_not_basis_change :
    ∃ x : Finset J → ℝ, x ≠ 0 ∧ (1+K) *ᵥ x = 0 :=
  ⟨_, unpaired_killed_vector_nonzero, unpaired_projector_kills⟩

end ReviewerSignature
