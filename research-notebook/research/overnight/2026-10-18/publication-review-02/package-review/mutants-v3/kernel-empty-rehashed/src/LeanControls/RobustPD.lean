module

public import LeanControls.SampledPD

/-!
# Disturbance and actuator certificates

Errors ex, ev are additive errors at sample boundaries, with a joint squared
bound. Their provenance (quantization, modeling, estimation) must be justified
separately before applying the theorem to an implementation.
-/

@[expose] public section
noncomputable section

namespace LeanControls.RobustPD

open PD SampledPD

/-- A weighted quadratic triangle inequality, certified by a square identity. -/
theorem energy_add_bound (x v ex ev : ℝ) :
    energy (x + ex) (v + ev) ≤ 121 / 120 * energy x v + 121 * energy ex ev := by
  have hp := energy_nonneg (x - 120 * ex) (v - 120 * ev)
  have hid :
      121 * energy x v + 14520 * energy ex ev - 120 * energy (x + ex) (v + ev) =
      energy (x - 120 * ex) (v - 120 * ev) := by
    unfold energy
    ring
  linarith

/-- Uniform robust contraction for sample intervals in `[1/20, 1/6]`. -/
theorem robust_step {h x v ex ev eps : ℝ} (hlo : 1 / 20 ≤ h) (hhi : h ≤ 1 / 6)
    (he : ex ^ 2 + ev ^ 2 ≤ eps ^ 2) :
    energy (position h x v + ex) (velocity h x v + ev) ≤
      119 / 120 * energy x v + 726 * eps ^ 2 := by
  have hbase := energy_contract (by linarith : 0 ≤ h) hhi x v
  have hV := energy_nonneg x v
  have hmult : (1 - h / 3) * energy x v ≤ 59 / 60 * energy x v :=
    mul_le_mul_of_nonneg_right (by linarith) hV
  have hadd := energy_add_bound (position h x v) (velocity h x v) ex ev
  have herr := energy_upper ex ev
  nlinarith only [hbase, hmult, hV, hadd, herr, he]

/-- Any radius satisfying the explicit disturbance budget is invariant. -/
theorem robust_invariant (h x v ex ev : ℕ → ℝ) {eps R : ℝ}
    (hlo : ∀ n, 1 / 20 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (he : ∀ n, ex n ^ 2 + ev n ^ 2 ≤ eps ^ 2)
    (hbudget : 87120 * eps ^ 2 ≤ R) (hinit : energy (x 0) (v 0) ≤ R)
    (hx : ∀ n, x (n + 1) = position (h n) (x n) (v n) + ex n)
    (hv : ∀ n, v (n + 1) = velocity (h n) (x n) (v n) + ev n) :
    ∀ n, energy (x n) (v n) ≤ R := by
  apply invariant_bound (V := fun n => energy (x n) (v n))
    (q := 119 / 120) (d := 726 * eps ^ 2) (by norm_num) (by linarith) hinit
  intro n
  rw [hx n, hv n]
  exact robust_step (hlo n) (hhi n) (he n)

/-- The controller request fits inside an actuator limit on an energy sublevel. -/
theorem control_energy_bound (x v : ℝ) : (control x v) ^ 2 ≤ 10 * energy x v := by
  unfold SampledPD.control energy
  nlinarith [sq_nonneg (4 * x + v), sq_nonneg x]

theorem control_within_limit {x v R U : ℝ} (hU : 0 ≤ U)
    (hE : energy x v ≤ R) (hR : 10 * R ≤ U ^ 2) : |control x v| ≤ U := by
  have hc := control_energy_bound x v
  apply (abs_le).2
  constructor <;> nlinarith

/-- Saturation is explicit, so its inactive region can be proved. -/
def saturate (U u : ℝ) : ℝ := max (-U) (min U u)

theorem saturate_eq {U u : ℝ} (hu : |u| ≤ U) : saturate U u = u := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hu
  simp [saturate, min_eq_right hhi, max_eq_right hlo]

/-- Local safety of the actual saturated update, with jitter and bounded errors.
The certificate proves saturation never activates from the stated initial set. -/
theorem saturated_robust_invariant (h x v ex ev : ℕ → ℝ) {eps R U : ℝ}
    (hU : 0 ≤ U) (hR : 10 * R ≤ U ^ 2)
    (hlo : ∀ n, 1 / 20 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (he : ∀ n, ex n ^ 2 + ev n ^ 2 ≤ eps ^ 2)
    (hbudget : 87120 * eps ^ 2 ≤ R) (hinit : energy (x 0) (v 0) ≤ R)
    (hx : ∀ n, x (n + 1) = x n + h n * v n +
      h n ^ 2 / 2 * saturate U (control (x n) (v n)) + ex n)
    (hv : ∀ n, v (n + 1) = v n +
      h n * saturate U (control (x n) (v n)) + ev n) :
    ∀ n, energy (x n) (v n) ≤ R ∧ |control (x n) (v n)| ≤ U := by
  intro n
  induction n with
  | zero => exact ⟨hinit, control_within_limit hU hinit hR⟩
  | succ n ih =>
    have hsat := saturate_eq ih.2
    have hnext : energy (x (n + 1)) (v (n + 1)) ≤ R := by
      rw [hx n, hv n, hsat]
      change energy (position (h n) (x n) (v n) + ex n)
        (velocity (h n) (x n) (v n) + ev n) ≤ R
      have hs := robust_step (x := x n) (v := v n) (hlo n) (hhi n) (he n)
      linarith [ih.1]
    exact ⟨hnext, control_within_limit hU hnext hR⟩

end LeanControls.RobustPD
