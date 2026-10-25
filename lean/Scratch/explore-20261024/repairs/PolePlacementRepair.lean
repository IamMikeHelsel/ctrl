import ControlsLean.Controls.PolePlacement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

open Matrix Polynomial

namespace ControlsLean.Controls.Repair

open ControlsLean.Controls

/-- Complexifying the real closed-loop matrix commutes with the companion construction. -/
theorem closedLoop_map_ofReal (a₀ a₁ k₀ k₁ : ℝ) :
    (closedLoop a₀ a₁ k₀ k₁).map (Complex.ofReal) =
      closedLoop (a₀ : ℂ) (a₁ : ℂ) (k₀ : ℂ) (k₁ : ℂ) := by
  rw [closedLoop_eq, closedLoop_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The characteristic polynomial (Mathlib `Matrix.charpoly`) of the closed loop. -/
theorem charpoly_closedLoop {K : Type*} [Field K] (a₀ a₁ k₀ k₁ : K) :
    (closedLoop a₀ a₁ k₀ k₁).charpoly = X ^ 2 + C (a₁ + k₁) * X + C (a₀ + k₀) := by
  rw [charpoly_fin_two, closedLoop_eq]
  simp [trace_fin_two, det_fin_two, sub_eq_add_neg]
  ring

/-- Every point of the complex spectrum of the closed loop is a root of `s² + (a₁+k₁)s + (a₀+k₀)`. -/
theorem spectrum_closedLoop_root (a₀ a₁ k₀ k₁ : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ ((closedLoop a₀ a₁ k₀ k₁).map Complex.ofReal)) :
    z ^ 2 + ((a₁ + k₁ : ℝ) : ℂ) * z + ((a₀ + k₀ : ℝ) : ℂ) = 0 := by
  rw [mem_spectrum_iff_isRoot_charpoly, closedLoop_map_ofReal, charpoly_closedLoop] at hz
  simpa using hz.eq_zero

/-- **Continuous-time pole placement for the companion form (corrected headline).**
For any desired `s² + d₁ s + d₀` with `d₀, d₁ > 0`, there is a state-feedback gain
`(k₀, k₁)` such that the closed-loop matrix `A - B K` has exactly that characteristic
polynomial and every complex eigenvalue of `A - B K` lies in the open left half-plane. -/
theorem exists_gain_closedLoop_hurwitz (a₀ a₁ d₀ d₁ : ℝ) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) :
    ∃ k₀ k₁ : ℝ,
      (closedLoop a₀ a₁ k₀ k₁).charpoly = X ^ 2 + C d₁ * X + C d₀ ∧
      ∀ z ∈ spectrum ℂ ((closedLoop a₀ a₁ k₀ k₁).map Complex.ofReal), z.re < 0 := by
  refine ⟨d₀ - a₀, d₁ - a₁, ?_, fun z hz => ?_⟩
  · rw [charpoly_closedLoop]; ring_nf
  · have h := spectrum_closedLoop_root a₀ a₁ _ _ hz
    have h₁ : a₁ + (d₁ - a₁) = d₁ := by ring
    have h₀ : a₀ + (d₀ - a₀) = d₀ := by ring
    rw [h₁, h₀] at h
    exact isHurwitz2_of_pos hd₁ hd₀ z h

/-- Eigenvector form: any complex eigenpair of the synthesized closed loop has `Re λ < 0`. -/
theorem closedLoop_eigenpair_re_neg (a₀ a₁ d₀ d₁ : ℝ) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (z : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (hAv : (closedLoop a₀ a₁ (d₀ - a₀) (d₁ - a₁)).map Complex.ofReal *ᵥ v = z • v) :
    z.re < 0 := by
  obtain ⟨_, _, hmain⟩ := exists_gain_closedLoop_hurwitz a₀ a₁ d₀ d₁ hd₀ hd₁
  have hdet : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (closedLoop a₀ a₁ (d₀ - a₀) (d₁ - a₁)).map Complex.ofReal).det = 0 := by
    rw [← exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [sub_mulVec, hAv, smul_mulVec, one_mulVec, sub_self]⟩
  rw [closedLoop_map_ofReal, det_sI_sub_closedLoop] at hdet
  have h₁ : ((a₁ : ℂ) + ((d₁ - a₁ : ℝ) : ℂ)) = (d₁ : ℂ) := by push_cast; ring
  have h₀ : ((a₀ : ℂ) + ((d₀ - a₀ : ℝ) : ℂ)) = (d₀ : ℂ) := by push_cast; ring
  rw [h₁, h₀] at hdet
  exact isHurwitz2_of_pos hd₁ hd₀ z hdet

/-- **Exact characterization**: a gain renders the companion closed loop Hurwitz (all complex
eigenvalues in the open LHP) iff `a₀ + k₀ > 0` and `a₁ + k₁ > 0`. -/
theorem closedLoop_hurwitz_iff (a₀ a₁ k₀ k₁ : ℝ) :
    (∀ z ∈ spectrum ℂ ((closedLoop a₀ a₁ k₀ k₁).map Complex.ofReal), z.re < 0) ↔
      0 < a₁ + k₁ ∧ 0 < a₀ + k₀ := by
  rw [← isHurwitz2_iff]
  refine ⟨fun h z hz => h z ?_, fun h z hz => h z ?_⟩
  · rw [mem_spectrum_iff_isRoot_charpoly, closedLoop_map_ofReal, charpoly_closedLoop]
    simpa using hz
  · simpa using spectrum_closedLoop_root a₀ a₁ k₀ k₁ hz

end ControlsLean.Controls.Repair
