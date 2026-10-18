import ComplexSignature

noncomputable section
open Matrix
namespace HyperbolicSpinor

theorem K_vacuum_column : K *ᵥ unitCoord ∅ = unitCoord Finset.univ := by
  rw [K_mulVec_basis]
  simp [complementSign]

theorem K_zero_diagonal : K ∅ ∅ = 0 := by
  rw [K_entry]
  have h : (∅ : Finset J) ≠ Finset.univ := by
    intro he
    have hh : (0 : J) ∈ (∅ : Finset J) := he.symm ▸ Finset.mem_univ 0
    simp at hh
  simp [h]

theorem K_signed_singleton : K *ᵥ unitCoord {0} = -unitCoord ({0} : Finset J)ᶜ := by
  rw [K_mulVec_basis]
  norm_num [complementSign]

/-- Omitting D loses invertibility: I+K kills a nonzero vector. -/
theorem unpaired_projector_kills :
    (1 + K) *ᵥ (unitCoord ∅ - K *ᵥ unitCoord ∅) = 0 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, K_square, Matrix.one_mulVec]
  abel

theorem unpaired_killed_vector_nonzero : unitCoord ∅ - K *ᵥ unitCoord ∅ ≠ 0 := by
  intro h
  have he := congrFun h ∅
  rw [K_vacuum_column] at he
  have hn : (∅ : Finset J) ≠ Finset.univ := by
    intro hu
    have hh : (0 : J) ∈ (∅ : Finset J) := hu.symm ▸ Finset.mem_univ 0
    simp at hh
  simp [unitCoord, Pi.single_apply, hn] at he

theorem real_positive_direction : (U.transpose * K * U) ∅ ∅ = 2 := by
  rw [U_congruence_entry]
  simp

theorem real_negative_direction : (U.transpose * K * U) {0} {0} = -2 := by
  rw [U_congruence_entry]
  simp

theorem complex_negative_direction : (Uc.conjTranspose * Kc * Uc) {0} {0} = -2 := by
  rw [Uc_congruence_entry]
  simp

end HyperbolicSpinor
