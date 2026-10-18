module

public import LeanControls.TravelDisturbance

/-! A uniform quadratic-energy bound for the polynomial response enclosure of
an actuator whose normalized rate lies in `[9/10, 11/10]`. The rate dependence
is represented by a quadratic Bernstein curve; time and remainder dependence
are affine. All endpoint checks are exact rational calculations. -/

@[expose] public section
noncomputable section
namespace LeanControls.UncertainResponse
open Matrix BernsteinCertificate

abbrev State := Fin 3 → ℝ
abbrev P := Generated.TravelQuarterLower.P

/-- The response divided by elapsed time, expressed without division. -/
def normalizedResponse (r h theta : ℝ) : State :=
  ![(1 / 2 - theta) * h, theta * r * h, r - theta * r ^ 2 * h]

/-- Quadratic Bernstein control values for the rate and its square. -/
def rateControl : Fin 3 → ℝ := ![9 / 10, 1, 11 / 10]
def squareControl : Fin 3 → ℝ := ![81 / 100, 99 / 100, 121 / 100]

def rateVertex (i : Fin 3) (h theta : ℝ) : State :=
  ![(1 / 2 - theta) * h, theta * rateControl i * h,
    rateControl i - theta * squareControl i * h]

/-- The elapsed-time-zero control vectors have energy below the common bound. -/
theorem rateVertex_zero_energy (i : Fin 3) (theta : ℝ) :
    energy P (rateVertex i 0 theta) ≤ 16 := by
  fin_cases i <;>
    norm_num [energy, P, Generated.TravelQuarterLower.P, rateVertex,
      rateControl, squareControl, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem rateVertex_end_zero_energy (i : Fin 3) :
    energy P (rateVertex i (1 / 5) 0) ≤ 16 := by
  fin_cases i <;>
    norm_num [energy, P, Generated.TravelQuarterLower.P, rateVertex,
      rateControl, squareControl, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem rateVertex_end_one_energy (i : Fin 3) :
    energy P (rateVertex i (1 / 5) 1) ≤ 16 := by
  fin_cases i <;>
    norm_num [energy, P, Generated.TravelQuarterLower.P, rateVertex,
      rateControl, squareControl, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem rateVertex_theta_interpolation (i : Fin 3) (h theta : ℝ) :
    rateVertex i h theta =
      (1 - theta) • rateVertex i h 0 + theta • rateVertex i h 1 := by
  ext j
  fin_cases j <;> simp [rateVertex, Pi.add_apply] <;> ring

theorem rateVertex_time_interpolation (i : Fin 3) (h theta : ℝ) :
    rateVertex i h theta =
      (1 - 5 * h) • rateVertex i 0 theta +
        (5 * h) • rateVertex i (1 / 5) theta := by
  ext j
  fin_cases j <;> simp [rateVertex, Pi.add_apply] <;> ring

theorem rateVertex_end_energy_bound (i : Fin 3) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    energy P (rateVertex i (1 / 5) theta) ≤ 16 := by
  rw [rateVertex_theta_interpolation]
  exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
    _ _ htheta0 htheta1 (rateVertex_end_zero_energy i) (rateVertex_end_one_energy i)

theorem rateVertex_energy_bound (i : Fin 3) {h theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) :
    energy P (rateVertex i h theta) ≤ 16 := by
  rw [rateVertex_time_interpolation]
  exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
    _ _ (by positivity) (by linarith)
    (rateVertex_zero_energy i theta) (rateVertex_end_energy_bound i htheta0 htheta1)

/-- Exact de Casteljau representation of the quadratic rate dependence. -/
theorem rate_interpolation (r h theta : ℝ) :
    normalizedResponse r h theta =
      (1 - (5 * r - 9 / 2)) •
        ((1 - (5 * r - 9 / 2)) • rateVertex 0 h theta +
          (5 * r - 9 / 2) • rateVertex 1 h theta) +
      (5 * r - 9 / 2) •
        ((1 - (5 * r - 9 / 2)) • rateVertex 1 h theta +
          (5 * r - 9 / 2) • rateVertex 2 h theta) := by
  ext j
  fin_cases j <;>
    simp [normalizedResponse, rateVertex, rateControl, squareControl, Pi.add_apply] <;> ring

/-- Uniform energy bound on the entire rate/remainder/time box, not merely
its rational control vectors. -/
theorem normalized_energy_bound {r h theta : ℝ}
    (hr0 : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) :
    energy P (normalizedResponse r h theta) ≤ 16 := by
  have hq0 : 0 ≤ 5 * r - 9 / 2 := by linarith
  have hq1 : 5 * r - 9 / 2 ≤ 1 := by linarith
  have hv := fun i => rateVertex_energy_bound i htheta0 htheta1 hh0 hh1
  rw [rate_interpolation]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ hq0 hq1
  · exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ hq0 hq1 (hv 0) (hv 1)
  · exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ hq0 hq1 (hv 1) (hv 2)

/-- Second-order response-energy estimate, uniformly valid down to zero time. -/
theorem scaled_response_energy_bound {r h theta : ℝ}
    (hr0 : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) :
    energy P (h • normalizedResponse r h theta) ≤ 16 * h ^ 2 := by
  rw [TravelDisturbance.energy_smul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (normalized_energy_bound hr0 hr1 htheta0 htheta1 hh0 hh1) (sq_nonneg h)

theorem disturbance_energy_bound {r h theta : ℝ}
    (hr0 : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) (w : ℝ) :
    energy P (w • (h • normalizedResponse r h theta)) ≤ 16 * h ^ 2 * w ^ 2 := by
  rw [TravelDisturbance.energy_smul]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left
    (scaled_response_energy_bound hr0 hr1 htheta0 htheta1 hh0 hh1) (sq_nonneg w)

theorem disturbance_energy_of_abs_le {r h theta w W : ℝ}
    (hr0 : 9 / 10 ≤ r) (hr1 : r ≤ 11 / 10)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 5) (hw : |w| ≤ W) :
    energy P (w • (h • normalizedResponse r h theta)) ≤ 16 * h ^ 2 * W ^ 2 := by
  have ha := abs_le.mp hw
  have hp := mul_nonneg (sub_nonneg.mpr ha.2) (show 0 ≤ W + w by linarith)
  have hw2 : w ^ 2 ≤ W ^ 2 := by nlinarith only [hp]
  exact (disturbance_energy_bound hr0 hr1 htheta0 htheta1 hh0 hh1 w).trans
    (mul_le_mul_of_nonneg_left hw2 (by positivity))

theorem scaled_response_zero (r theta : ℝ) :
    (0 : ℝ) • normalizedResponse r 0 theta = 0 := by simp

end LeanControls.UncertainResponse
