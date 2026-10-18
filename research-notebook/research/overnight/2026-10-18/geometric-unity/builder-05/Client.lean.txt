import SignatureControls
import OrderControls
noncomputable section
open Matrix HyperbolicSpinor
namespace GUSignatureClient

theorem actual_column (T : Finset J) :
    K *ᵥ unitCoord T = (complementSign T : ℝ) • unitCoord Tᶜ := K_mulVec_basis T

theorem actual_entry (I T : Finset J) :
    K I T = if I = Tᶜ then (complementSign T : ℝ) else 0 := K_entry I T

theorem paired_positive (T : Finset J) (h : (0 : J) ∉ T) :
    U *ᵥ unitCoord T = unitCoord T + (complementSign T : ℝ) • unitCoord Tᶜ := positive_pair_column T h

theorem paired_negative (T : Finset J) (h : (0 : J) ∉ T) :
    U *ᵥ unitCoord Tᶜ = unitCoord Tᶜ - (complementSign T : ℝ) • unitCoord T := negative_pair_column T h

theorem real_congruence : U.transpose * K * U = (2 : ℝ) • D := U_congruence

theorem real_inverse_left : Uinverse * U = 1 := Uinverse_left

theorem real_inverse_right : U * Uinverse = 1 := Uinverse_right

theorem positive_count : (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card = 64 := positive_half_count

theorem negative_count : (Finset.univ.filter (fun T : Finset J => (0 : J) ∈ T)).card = 64 := negative_half_count

theorem complex_congruence : Uc.conjTranspose * Kc * Uc = (2 : ℂ) • Dc := Uc_congruence

theorem complex_inverse_formula : Ucinverse = (1/2 : ℂ) • Uc.conjTranspose := Ucinverse_formula

theorem complex_inverse_left : Ucinverse * Uc = 1 := Ucinverse_left

theorem complex_inverse_right : Uc * Ucinverse = 1 := Ucinverse_right

theorem positive_witness : (U.transpose * K * U) ∅ ∅ = 2 := real_positive_direction

theorem negative_witness : (Uc.conjTranspose * Kc * Uc) {0} {0} = -2 := complex_negative_direction

theorem omitted_D_is_singular :
    ∃ x : Finset J → ℝ, x ≠ 0 ∧ (1 + K) *ᵥ x = 0 :=
  ⟨unitCoord ∅ - K *ᵥ unitCoord ∅, unpaired_killed_vector_nonzero, unpaired_projector_kills⟩

end GUSignatureClient
