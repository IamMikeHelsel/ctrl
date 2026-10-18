module

public import LeanControls.SaturatedLag
public import LeanControls.Generated.TravelQuarterLower
public import LeanControls.VertexCertificate

/-! Exact energy bound for the held additive-input response of the normalized
actuator-lag plant. The exponential is enclosed, not discarded. -/

@[expose] public section
noncomputable section
namespace LeanControls.TravelDisturbance
open Matrix BernsteinCertificate

abbrev State := Fin 3 → ℝ
abbrev P := Generated.TravelQuarterLower.P

def lowerNormalized (t : ℝ) : State := ![t / 2, 0, 1]
def upperNormalized (t : ℝ) : State := ![-t / 2, t, 1 - t]

theorem energy_smul (s : ℝ) (z : State) : energy P (s • z) = s ^ 2 * energy P z := by
  simp only [energy, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem lower_zero_energy : energy P (lowerNormalized 0) = 278 / 25 := by
  norm_num [energy, P, Generated.TravelQuarterLower.P, lowerNormalized,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem lower_end_energy : energy P (lowerNormalized (1 / 5)) = 3049 / 250 := by
  norm_num [energy, P, Generated.TravelQuarterLower.P, lowerNormalized,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upper_zero_energy : energy P (upperNormalized 0) = 278 / 25 := by
  norm_num [energy, P, Generated.TravelQuarterLower.P, upperNormalized,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upper_end_energy : energy P (upperNormalized (1 / 5)) = 7474 / 625 := by
  norm_num [energy, P, Generated.TravelQuarterLower.P, upperNormalized,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem lower_interpolation (t : ℝ) :
    lowerNormalized t = (1 - 5 * t) • lowerNormalized 0 +
      (5 * t) • lowerNormalized (1 / 5) := by
  ext i
  fin_cases i <;> simp [lowerNormalized, Pi.add_apply]; ring

theorem upper_interpolation (t : ℝ) :
    upperNormalized t = (1 - 5 * t) • upperNormalized 0 +
      (5 * t) • upperNormalized (1 / 5) := by
  ext i
  fin_cases i <;> simp [upperNormalized, Pi.add_apply] <;> ring

/-- Convexity of a positive quadratic energy reduces each normalized affine
vertex to its two rational endpoint energies. -/
theorem lower_energy_bound {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) :
    energy P (lowerNormalized t) ≤ 13 := by
  rw [lower_interpolation]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
    _ _ (by positivity) (by linarith)
  · rw [lower_zero_energy]
    norm_num
  · rw [lower_end_energy]
    norm_num

theorem upper_energy_bound {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) :
    energy P (upperNormalized t) ≤ 13 := by
  rw [upper_interpolation]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
    _ _ (by positivity) (by linarith)
  · rw [upper_zero_energy]
    norm_num
  · rw [upper_end_energy]
    norm_num

/-- The exact response lies between scaled polynomial vertices. This statement
includes t=0 via the already checked exponential interpolation theorem. -/
theorem response_enclosed {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      SaturatedLag.response t = (1 - theta) • (t • lowerNormalized t) +
        theta • (t • upperNormalized t) := by
  obtain ⟨theta, ht, ht1, he⟩ := ActuatorLag.exp_interpolation ht0 (by linarith : t ≤ 1)
  refine ⟨theta, ht, ht1, ?_⟩
  ext i
  fin_cases i <;>
    simp [SaturatedLag.response, lowerNormalized, upperNormalized, Pi.add_apply, he] <;> ring

/-- The exact response energy is second order in elapsed time, uniformly down
to zero. No numerical evaluation of the exponential occurs in this proof. -/
theorem response_energy_bound {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) :
    energy P (SaturatedLag.response t) ≤ 13 * t ^ 2 := by
  obtain ⟨theta, ht, ht1, he⟩ := response_enclosed ht0 hthi
  rw [he]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ ht ht1
  · rw [energy_smul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (lower_energy_bound ht0 hthi) (sq_nonneg t)
  · rw [energy_smul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (upper_energy_bound ht0 hthi) (sq_nonneg t)

/-- A constant held disturbance w has exactly the response w • response(t). -/
theorem disturbance_energy_bound {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) (w : ℝ) :
    energy P (w • SaturatedLag.response t) ≤ 13 * t ^ 2 * w ^ 2 := by
  rw [energy_smul]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left (response_energy_bound ht0 hthi) (sq_nonneg w)

/-- Version matching a prescribed absolute disturbance budget. -/
theorem disturbance_energy_of_abs_le {t w W : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5)
    (hw : |w| ≤ W) : energy P (w • SaturatedLag.response t) ≤ 13 * t ^ 2 * W ^ 2 := by
  have ha := abs_le.mp hw
  have hp := mul_nonneg (sub_nonneg.mpr ha.2) (show 0 ≤ W + w by linarith)
  have hw2 : w ^ 2 ≤ W ^ 2 := by nlinarith only [hp]
  exact (disturbance_energy_bound ht0 hthi w).trans
    (mul_le_mul_of_nonneg_left hw2 (by positivity))

theorem response_zero : SaturatedLag.response 0 = 0 := by
  ext i
  fin_cases i <;> simp [SaturatedLag.response]

theorem disturbance_zero (w : ℝ) : w • SaturatedLag.response 0 = 0 := by
  rw [response_zero, smul_zero]

end LeanControls.TravelDisturbance
