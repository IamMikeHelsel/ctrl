import ControlsLean.Estimation.KalmanBucy
import ControlsLean.Controls.Hurwitz2

/-!
# Kalman–Bucy (1961) on a modern camera tracker: closed-form steady state

Constant-velocity target model (pixel position `x₁`, pixel velocity `x₂`):
`ẋ = A x + w`, `y = C x + v`, `A = [[0,1],[0,0]]`, `C = [1,0]`,
process noise intensity `W = diag(0, q)` (white acceleration), measurement noise `V = [r]`.

With `ω = (q/r)^{1/4}` the steady-state covariance is
`P = r · [[√2 ω, ω²], [ω², √2 ω³]]`, the gain is `L = [√2 ω, ω²]ᵀ`, and the error
characteristic polynomial is `s² + √2 ω s + ω²` — a 2nd-order **Butterworth** filter with
damping ratio `1/√2` and bandwidth `(q/r)^{1/4}`.
-/

namespace Revival1961

open Matrix ControlsLean.Estimation ControlsLean.Controls

noncomputable section

def Acv : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def Ccv : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
def Wcv (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, q]
def Vcv (r : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![r]

/-- Tracker bandwidth `ω = (q/r)^{1/4}`. -/
def omega (q r : ℝ) : ℝ := Real.sqrt (Real.sqrt (q / r))

def Pcv (r w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (Real.sqrt 2 * w), r * w ^ 2; r * w ^ 2, r * (Real.sqrt 2 * w ^ 3)]

def Lcv (w : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![Real.sqrt 2 * w; w ^ 2]

lemma omega_pow_four {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) : omega q r ^ 4 = q / r := by
  have h0 : 0 ≤ q / r := div_nonneg hq hr.le
  unfold omega
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt h0]

lemma omega_pos {q r : ℝ} (hq : 0 < q) (hr : 0 < r) : 0 < omega q r := by
  unfold omega; positivity

lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma Pcv_symm (r w : ℝ) : (Pcv r w)ᵀ = Pcv r w := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Pcv]

/-- The closed-form gain satisfies the Kalman–Bucy normal equation `L V = P Cᵀ`. -/
theorem Lcv_normal_eq (r w : ℝ) : Lcv w * Vcv r = Pcv r w * Ccvᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Lcv, Vcv, Pcv, Ccv, Matrix.mul_apply, Fin.sum_univ_two, -Matrix.cons_mul,
      -Matrix.cons_vecMul] <;> ring

/-- **Closed-form steady-state Kalman–Bucy solution.** With `ω⁴ = q/r`, the explicit `P` and
`L` make the steady-state covariance derivative vanish. -/
theorem cv_steadyState {q r w : ℝ} (hr : 0 < r) (hw : w ^ 4 = q / r) :
    kalmanBucyCovDeriv (Pcv r w) Acv Ccv (Wcv q) (Vcv r) (Lcv w) = 0 := by
  have hq : q = r * w ^ 4 := by rw [hw]; field_simp
  have h2 := sqrt2_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [kalmanBucyCovDeriv, Pcv, Acv, Ccv, Wcv, Vcv, Lcv, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, -Matrix.cons_mul, -Matrix.cons_vecMul] <;>
    ring_nf <;> simp only [h2, hq] <;> ring_nf

/-- The library gain `P Cᵀ V⁻¹` equals the closed form `[√2 ω, ω²]ᵀ`. -/
theorem kalmanBucyGain_cv {r w : ℝ} (hr : 0 < r) :
    kalmanBucyGain (Pcv r w) Ccv (Vcv r) = Lcv w := by
  have hdet : IsUnit (Vcv r).det := by
    simp [Vcv, Matrix.det_unique]; exact hr.ne'
  unfold kalmanBucyGain
  rw [← Lcv_normal_eq, Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]

lemma Vcv_posDef {r : ℝ} (hr : 0 < r) : (Vcv r).PosDef := by
  rw [ControlsLean.Tactics.posDef_iff_quad_pos]
  refine ⟨by ext i j; fin_cases i; fin_cases j; rfl, fun x hx => ?_⟩
  have : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
  simp [quad, Vcv, Matrix.mulVec, dotProduct]
  have := sq_pos_of_ne_zero this
  nlinarith

/-- **Headline (1961 → camera tracking).** For any `q > 0`, `r > 0`, the explicit matrix
`P(ω)` with `ω = (q/r)^{1/4}` solves the steady-state Kalman–Bucy Riccati equation
`A P + P Aᵀ − P Cᵀ V⁻¹ C P + W = 0`, and the Kalman gain is `[√2 ω, ω²]ᵀ`. -/
theorem cv_tracker_riccati {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    kalmanBucyResidual (Pcv r (omega q r)) Acv Ccv (Wcv q) (Vcv r) = 0 ∧
      kalmanBucyGain (Pcv r (omega q r)) Ccv (Vcv r) = Lcv (omega q r) := by
  refine ⟨?_, kalmanBucyGain_cv hr⟩
  rw [← kalmanBucyCovDeriv_opt_eq_residual (Pcv_symm _ _) (Vcv_posDef hr),
    kalmanBucyGain_cv hr]
  exact cv_steadyState hr (omega_pow_four hq.le hr)

/-- `P` is positive definite (a genuine covariance). -/
theorem Pcv_posDef {r w : ℝ} (hr : 0 < r) (hw : 0 < w) : (Pcv r w).PosDef := by
  rw [ControlsLean.Tactics.posDef_iff_quad_pos]
  refine ⟨Pcv_symm r w, fun x hx => ?_⟩
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; push Not at h; exact hx (by ext i; fin_cases i <;> simp [h.1, h.2])
  have h2 := sqrt2_sq
  have hs : 0 < Real.sqrt 2 := by positivity
  simp only [quad, Pcv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  have key : 0 < Real.sqrt 2 * x 0 ^ 2 + 2 * w * x 0 * x 1 + Real.sqrt 2 * w ^ 2 * x 1 ^ 2 := by
    have e : Real.sqrt 2 * (Real.sqrt 2 * x 0 ^ 2 + 2 * w * x 0 * x 1 +
        Real.sqrt 2 * w ^ 2 * x 1 ^ 2) = (Real.sqrt 2 * x 0 + w * x 1) ^ 2 + w ^ 2 * x 1 ^ 2 := by
      ring_nf; rw [h2]; ring
    have : 0 < (Real.sqrt 2 * x 0 + w * x 1) ^ 2 + w ^ 2 * x 1 ^ 2 := by
      rcases hx' with h0 | h1
      · by_cases h1 : x 1 = 0
        · rw [h1]; simp; exact sq_pos_of_ne_zero (mul_ne_zero hs.ne' h0)
        · have := pow_pos (mul_pos hw hw) 1
          positivity
      · have : 0 < w ^ 2 * x 1 ^ 2 := by positivity
        nlinarith [sq_nonneg (Real.sqrt 2 * x 0 + w * x 1)]
    nlinarith
  nlinarith [mul_pos hr hw]

/-- Error dynamics matrix `A − L C = [[−√2 ω, 1], [−ω², 0]]`. -/
theorem cv_error_matrix (w : ℝ) :
    Acv - Lcv w * Ccv = !![-(Real.sqrt 2 * w), 1; -(w ^ 2), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Acv, Lcv, Ccv]

/-- Its trace and determinant: characteristic polynomial `s² + √2 ω s + ω²` (Butterworth). -/
theorem cv_error_trace_det (w : ℝ) :
    (Acv - Lcv w * Ccv).trace = -(Real.sqrt 2 * w) ∧ (Acv - Lcv w * Ccv).det = w ^ 2 := by
  rw [cv_error_matrix, trace_fin_two_of, det_fin_two_of]; constructor <;> ring

/-- **Error dynamics are Hurwitz**: `s² + √2 ω s + ω²` has all roots in `Re s < 0`. -/
theorem cv_error_hurwitz {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    IsHurwitz2 (Real.sqrt 2 * omega q r) (omega q r ^ 2) :=
  isHurwitz2_of_pos (by have := omega_pos hq hr; positivity)
    (by have := omega_pos hq hr; positivity)

/-- Damping ratio is exactly `1/√2`: `(2ζω)² = 2ω²` i.e. `ζ² = 1/2`. -/
theorem cv_butterworth_damping (w : ℝ) :
    (Real.sqrt 2 * w) ^ 2 = 2 * (w ^ 2) := by rw [mul_pow, sqrt2_sq]

/-- Steady-state position-error variance `P₁₁ = √2 · r^{3/4} q^{1/4}` grows only like the fourth
root of the process-noise intensity. Stated as `P₁₁⁴ = 4 r³ q`. -/
theorem cv_position_variance {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) :
    (Pcv r (omega q r) 0 0) ^ 4 = 4 * r ^ 3 * q := by
  have h := omega_pow_four hq hr
  have h2 := sqrt2_sq
  simp only [Pcv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have : (r * (Real.sqrt 2 * omega q r)) ^ 4 = r ^ 4 * (Real.sqrt 2 ^ 2) ^ 2 * omega q r ^ 4 := by
    ring
  rw [this, h, h2]; field_simp; ring

end

end Revival1961
