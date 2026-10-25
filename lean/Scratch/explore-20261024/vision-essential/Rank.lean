import ControlsLean.Vision.Epipolar
import Mathlib

open Matrix

namespace ControlsLean.Vision.Explore

variable {K : Type*} [Field K]

theorem skew_mulVec_self (t : Fin 3 → K) : skew t *ᵥ t = 0 := by
  rw [skew_mulVec, cross_self]

/-- `rank [t]ₓ ≤ 2` (always). -/
theorem rank_skew_le (t : Fin 3 → K) (ht : t ≠ 0) : (skew t).rank ≤ 2 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (skew t).mulVecLin
  have hker : 1 ≤ Module.finrank K (LinearMap.ker (skew t).mulVecLin) := by
    have hle : K ∙ t ≤ LinearMap.ker (skew t).mulVecLin := by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, mulVecLin_apply,
        skew_mulVec_self]
    have := Submodule.finrank_mono hle
    rwa [finrank_span_singleton ht] at this
  rw [Matrix.rank]
  simp only [Module.finrank_fin_fun] at hrn
  omega

/-- `rank [t]ₓ ≥ 2` when `t ≠ 0`, via a `2 × 2` minor equal to `t i ^ 2`. -/
theorem two_le_rank_skew {t : Fin 3 → K} (ht : t ≠ 0) : 2 ≤ (skew t).rank := by
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra h; push Not at h; exact ht (funext h)
  have key : ∀ r c : Fin 2 → Fin 3, ((skew t).submatrix r c).det ≠ 0 → 2 ≤ (skew t).rank :=
    fun r c h => by
      have := rank_submatrix_le (skew t) r c
      rw [rank_of_det_ne_zero h, Fintype.card_fin] at this
      exact this
  fin_cases i
  · exact key ![1, 2] ![1, 2] (by rw [det_fin_two]; simpa [skew] using hi)
  · exact key ![0, 2] ![0, 2] (by rw [det_fin_two]; simpa [skew] using hi)
  · exact key ![0, 1] ![0, 1] (by rw [det_fin_two]; simpa [skew] using hi)

theorem rank_skew {t : Fin 3 → K} (ht : t ≠ 0) : (skew t).rank = 2 :=
  le_antisymm (rank_skew_le t ht) (two_le_rank_skew ht)

/-- **`rank E = 2`** for `t ≠ 0` and invertible `R`, over any field. -/
theorem rank_essential {R : Matrix (Fin 3) (Fin 3) K} (hR : R.det ≠ 0) {t : Fin 3 → K}
    (ht : t ≠ 0) : (essential R t).rank = 2 := by
  rw [essential, rank_mul_eq_left_of_det_ne_zero R _ hR, rank_skew ht]

theorem rank_essential_zero (R : Matrix (Fin 3) (Fin 3) K) : essential R 0 = 0 := by
  have : skew (0 : Fin 3 → K) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  rw [essential, this, Matrix.zero_mul]

/-! ### Over `ℂ` the cubic does NOT characterise essential matrices -/

/-- An isotropic, nilpotent-ish matrix: `E Eᵀ = 0` because `1 + i² = 0`. -/
def Eiso : Matrix (Fin 3) (Fin 3) ℂ := !![1, Complex.I, 0; 0, 0, 0; 0, 0, 0]

theorem Eiso_mul_transpose : Eiso * Eisoᵀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Eiso, Matrix.mul_apply, Fin.sum_univ_three]

/-- `Eiso` satisfies the Huang–Faugeras cubic in either form (both sides are `0`). -/
theorem Eiso_cubic : Eiso * Eisoᵀ * Eiso = ((1 / 2 : ℂ) * trace (Eiso * Eisoᵀ)) • Eiso := by
  rw [Eiso_mul_transpose]; simp

theorem Eiso_ne_zero : Eiso ≠ 0 := by
  intro h; have := congrFun (congrFun h 0) 0; simp [Eiso] at this

/-- …but `Eiso` is not `[t]ₓ R` for any complex orthogonal `R` (`R Rᵀ = 1`). So the robo-lean
converse `exists_essential_of_cubic` genuinely needs `ℝ` (positivity of `tr(E Eᵀ)`). -/
theorem Eiso_not_essential :
    ¬ ∃ (R : Matrix (Fin 3) (Fin 3) ℂ) (t : Fin 3 → ℂ), R * Rᵀ = 1 ∧ Eiso = essential R t := by
  rintro ⟨R, t, hR, hE⟩
  have hS : skew t * (skew t)ᵀ = 0 := by
    rw [← Eiso_mul_transpose, hE, essential, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc R, hR, Matrix.one_mul]
  rw [skew_transpose] at hS
  have h00 := congrFun (congrFun hS 0) 0
  have h11 := congrFun (congrFun hS 1) 1
  have h22 := congrFun (congrFun hS 2) 2
  have h01 := congrFun (congrFun hS 0) 1
  have h02 := congrFun (congrFun hS 0) 2
  have h12 := congrFun (congrFun hS 1) 2
  simp [skew, Matrix.mul_apply, Fin.sum_univ_three] at h00 h11 h22 h01 h02 h12
  have a0 : t 0 ^ 2 = 0 := by linear_combination (h11 + h22 - h00) / 2
  have a1 : t 1 ^ 2 = 0 := by linear_combination (h00 + h22 - h11) / 2
  have a2 : t 2 ^ 2 = 0 := by linear_combination (h00 + h11 - h22) / 2
  have ht : t = 0 := by
    funext i; fin_cases i <;> simp <;> exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ‹_›
  apply Eiso_ne_zero
  rw [hE, ht, rank_essential_zero]

end ControlsLean.Vision.Explore
