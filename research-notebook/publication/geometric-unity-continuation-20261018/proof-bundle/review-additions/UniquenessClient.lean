import FormUniqueness
import SignatureControls
noncomputable section
namespace UniquenessReview
open HyperbolicSpinor GUClifford Matrix

theorem zero_compatible : VectorCompatible (0 : SpinMatrix) := by
  simpa using scalar_vectorCompatible 0

theorem twice_compatible : VectorCompatible ((2 : ℝ) • K) := scalar_vectorCompatible 2

theorem K_ne_zero : K ≠ (0 : SpinMatrix) := by
  intro h
  have hs := K_square
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem twice_not_normalized : (2 : ℝ) • K ≠ K := by
  intro h
  have hz : (1 : ℝ) • K = (0 : ℝ) • K := by
    have hd := congrArg (fun A : SpinMatrix => A - K) h
    simpa [two_smul] using hd
  exact K_ne_zero (by simpa using hz)

theorem nonzero_coordinate : ∃ i j, K i j ≠ 0 := by
  by_contra h
  push_neg at h
  apply K_ne_zero
  ext i j
  exact h i j

theorem normalization_has_witness : ∃ i j, K i j ≠ 0 ∧
    ∀ H, VectorCompatible H → H i j = K i j → H = K := by
  obtain ⟨i,j,hk⟩ := nonzero_coordinate
  exact ⟨i,j,hk,fun H h hn => normalized_vectorCompatible_unique H h i j hk hn⟩

theorem zero_diagonal_does_not_fix_scale :
    ((2 : ℝ) • K) ∅ ∅ = K ∅ ∅ ∧ (2 : ℝ) • K ≠ K := by
  constructor
  · simp [K_zero_diagonal]
  · exact twice_not_normalized

theorem zero_coordinate_uniqueness_false :
    ¬ (∀ H : SpinMatrix, VectorCompatible H → H ∅ ∅ = K ∅ ∅ → H = K) := by
  intro h
  exact twice_not_normalized (h ((2 : ℝ) • K) twice_compatible
    zero_diagonal_does_not_fix_scale.1)

end UniquenessReview
