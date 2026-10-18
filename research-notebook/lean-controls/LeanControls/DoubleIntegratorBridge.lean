module

public import LeanControls.Generated.DoubleIntegrator
public import LeanControls.Generated.DoubleIntegratorWide
public import LeanControls.SampledPD

/-! The generated matrix certificates apply to the existing exact held-input
model. This file checks the model and energy identification inside Lean. -/

@[expose] public section
noncomputable section
namespace LeanControls.DoubleIntegratorBridge
open Matrix

/-- The generated transition is exactly the held-input double-integrator step. -/
theorem normal_transition (h x v : ℝ) :
    Generated.DoubleIntegrator.transition h *ᵥ ![x, v] =
      ![SampledPD.position h x v, SampledPD.velocity h x v] := by
  ext i
  fin_cases i <;>
    simp [Generated.DoubleIntegrator.transition, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, SampledPD.position, SampledPD.velocity, SampledPD.control] <;> ring

/-- Matrix energy and the original scalar certificate are the same function. -/
theorem normal_energy (z : Fin 2 → ℝ) :
    BernsteinCertificate.energy Generated.DoubleIntegrator.P z = PD.energy (z 0) (z 1) := by
  simp [BernsteinCertificate.energy, Generated.DoubleIntegrator.P, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, PD.energy]
  ring

/-- The wide-interval certificate uses the same physical transition polynomial. -/
theorem wide_transition (h x v : ℝ) :
    Generated.DoubleIntegratorWide.transition h *ᵥ ![x, v] =
      ![SampledPD.position h x v, SampledPD.velocity h x v] := by
  change Generated.DoubleIntegrator.transition h *ᵥ ![x, v] = _
  exact normal_transition h x v

theorem wide_energy (z : Fin 2 → ℝ) :
    BernsteinCertificate.energy Generated.DoubleIntegratorWide.P z =
      PD.energy (z 0) (z 1) := by
  change BernsteinCertificate.energy Generated.DoubleIntegrator.P z = _
  exact normal_energy z

theorem state_squared_norm (x v : ℝ) :
    BernsteinCertificate.squaredNorm ![x, v] = x ^ 2 + v ^ 2 := by
  simp [BernsteinCertificate.squaredNorm, Fin.sum_univ_succ]

/-- The original generated certificate transfers to the held model on [0,1/2]. -/
theorem normal_decrease {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 2) (x v : ℝ) :
    PD.energy (SampledPD.position h x v) (SampledPD.velocity h x v) ≤
      PD.energy x v - h * (x ^ 2 + v ^ 2) := by
  have hb := Generated.DoubleIntegrator.certified_decrease h0 hhi ![x, v]
  rw [normal_transition, normal_energy, normal_energy, state_squared_norm] at hb
  simpa using hb

/-- A wider interval has a smaller certified decay margin: 1/100 instead of 1. -/
theorem wide_decrease {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 33 / 50) (x v : ℝ) :
    PD.energy (SampledPD.position h x v) (SampledPD.velocity h x v) ≤
      PD.energy x v - (h / 100) * (x ^ 2 + v ^ 2) := by
  have hb := Generated.DoubleIntegratorWide.certified_decrease h0 hhi ![x, v]
  rw [wide_transition, wide_energy, wide_energy, state_squared_norm] at hb
  simpa [div_eq_mul_inv] using hb

theorem wide_contraction {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 33 / 50) (x v : ℝ) :
    PD.energy (SampledPD.position h x v) (SampledPD.velocity h x v) ≤
      (1 - h / 600) * PD.energy x v := by
  have hb := Generated.DoubleIntegratorWide.certified_contraction h0 hhi ![x, v]
  rw [wide_transition, wide_energy, wide_energy] at hb
  norm_num [Generated.DoubleIntegratorWide.upperBound] at hb
  convert hb using 1; ring

/-- Transfer the generated arbitrary-jitter theorem to the original state variables. -/
theorem wide_jitter (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 33 / 50)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 33 / 50)
    (hx : ∀ n, x (n + 1) = SampledPD.position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = SampledPD.velocity (h n) (x n) (v n)) (n : ℕ) :
    PD.energy (x n) (v n) ≤ (1 - hmin / 600) ^ n * PD.energy (x 0) (v 0) := by
  have hdyn : ∀ k, ![x (k + 1), v (k + 1)] =
      Generated.DoubleIntegratorWide.transition (h k) *ᵥ ![x k, v k] := by
    intro k
    rw [wide_transition, hx k, hv k]
  have hb := Generated.DoubleIntegratorWide.certified_jitter h (fun k => ![x k, v k])
    hmin0 hminhi hlo hhi hdyn n
  rw [wide_energy, wide_energy] at hb
  norm_num [Generated.DoubleIntegratorWide.upperBound] at hb
  convert hb using 1; ring

/-- Every intermediate state stays below the energy at the start of its sample.
This is not a pairwise monotonicity claim between arbitrary intermediate times. -/
theorem wide_intersample_bound {h t x v : ℝ} (ht : 0 ≤ t) (hth : t ≤ h)
    (hhi : h ≤ 33 / 50) :
    PD.energy (SampledPD.position t x v) (SampledPD.velocity t x v) ≤ PD.energy x v := by
  have hd := wide_decrease ht (hth.trans hhi) x v
  have hn : 0 ≤ (t / 100) * (x ^ 2 + v ^ 2) := by positivity
  linarith

/-- The sample-index geometric envelope also bounds every point of every nominal
held segment. No assertion about disturbed or saturated segments is made. -/
theorem wide_trajectory_intersample (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 33 / 50)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 33 / 50)
    (hx : ∀ n, x (n + 1) = SampledPD.position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = SampledPD.velocity (h n) (x n) (v n))
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (hth : t ≤ h n) :
    PD.energy (SampledPD.position t (x n) (v n)) (SampledPD.velocity t (x n) (v n)) ≤
      (1 - hmin / 600) ^ n * PD.energy (x 0) (v 0) := by
  exact (wide_intersample_bound ht hth (hhi n)).trans
    (wide_jitter h x v hmin0 hminhi hlo hhi hx hv n)

/-- Exact counterexample to pairwise energy monotonicity inside a held interval:
energy can rise from t=1/2 to t=3/5 while staying below its initial value. -/
theorem intersample_not_monotone :
    (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) ≤ 33 / 50 ∧
    PD.energy (SampledPD.position (1 / 2) 0 1) (SampledPD.velocity (1 / 2) 0 1) = 13 / 64 ∧
    PD.energy (SampledPD.position (3 / 5) 0 1) (SampledPD.velocity (3 / 5) 0 1) = 281 / 500 ∧
    (13 / 64 : ℝ) < 281 / 500 := by
  norm_num [SampledPD.position, SampledPD.velocity, SampledPD.control, PD.energy]

end LeanControls.DoubleIntegratorBridge
