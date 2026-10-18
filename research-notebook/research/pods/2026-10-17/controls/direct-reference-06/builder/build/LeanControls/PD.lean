module

public import LeanControls.Discrete

/-!
# A PD controller for a discrete double integrator

The update here is forward Euler, explicitly, not exact zero-order-hold sampling:
  x⁺ = x + h v,  v⁺ = v + h (-2x - 3v).
The certificate V = 5x² + 2xv + v² establishes geometric decay even with
time-varying step sizes bounded away from zero and above by 1/6.
-/

@[expose] public section

namespace LeanControls.PD

def energy (x v : ℝ) : ℝ := 5 * x ^ 2 + 2 * x * v + v ^ 2
def positionStep (h x v : ℝ) : ℝ := x + h * v
def velocityStep (h x v : ℝ) : ℝ := v + h * (-2 * x - 3 * v)

theorem energy_sos (x v : ℝ) : energy x v = 4 * x ^ 2 + (x + v) ^ 2 := by
  unfold energy
  ring

theorem energy_nonneg (x v : ℝ) : 0 ≤ energy x v := by
  rw [energy_sos]
  positivity

theorem energy_lower (x v : ℝ) : (x ^ 2 + v ^ 2) / 2 ≤ energy x v := by
  unfold energy
  nlinarith [sq_nonneg (2 * x + v), sq_nonneg x]

theorem energy_upper (x v : ℝ) : energy x v ≤ 6 * (x ^ 2 + v ^ 2) := by
  unfold energy
  nlinarith [sq_nonneg (x - v), sq_nonneg v]

theorem energy_step_identity (h x v : ℝ) :
    energy (positionStep h x v) (velocityStep h x v) - energy x v =
      -4 * h * (x ^ 2 + v ^ 2) + h ^ 2 * (4 * x ^ 2 + 8 * x * v + 8 * v ^ 2) := by
  unfold energy positionStep velocityStep
  ring

theorem energy_step_decrease {h : ℝ} (h0 : 0 ≤ h) (hmax : h ≤ 1 / 6) (x v : ℝ) :
    energy (positionStep h x v) (velocityStep h x v) - energy x v ≤
      -2 * h * (x ^ 2 + v ^ 2) := by
  rw [energy_step_identity]
  have hs : 0 ≤ x ^ 2 + v ^ 2 := by positivity
  have hb : 4 * x ^ 2 + 8 * x * v + 8 * v ^ 2 ≤ 12 * (x ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (x - v), sq_nonneg x]
  have hh : 12 * h ^ 2 ≤ 2 * h := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hb (sq_nonneg h)
  have hprod2 := mul_le_mul_of_nonneg_right hh hs
  nlinarith only [hprod, hprod2]

theorem energy_step_contract {h : ℝ} (h0 : 0 ≤ h) (hmax : h ≤ 1 / 6) (x v : ℝ) :
    energy (positionStep h x v) (velocityStep h x v) ≤ (1 - h / 3) * energy x v := by
  have hd := energy_step_decrease h0 hmax x v
  have hu := mul_le_mul_of_nonneg_left (energy_upper x v) h0
  nlinarith only [hd, hu]

/-- All-time bound under arbitrary jitter inside `[hmin, 1/6]`. -/
theorem jitter_energy_bound (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminmax : hmin ≤ 1 / 6)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (hx : ∀ n, x (n + 1) = positionStep (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = velocityStep (h n) (x n) (v n)) (n : ℕ) :
    energy (x n) (v n) ≤ (1 - hmin / 3) ^ n * energy (x 0) (v 0) := by
  apply geometric_bound (V := fun k => energy (x k) (v k))
    (by linarith : 0 ≤ 1 - hmin / 3)
  intro k
  rw [hx k, hv k]
  calc
    energy (positionStep (h k) (x k) (v k)) (velocityStep (h k) (x k) (v k))
        ≤ (1 - h k / 3) * energy (x k) (v k) :=
      energy_step_contract (hmin0.trans (hlo k)) (hhi k) _ _
    _ ≤ (1 - hmin / 3) * energy (x k) (v k) :=
      mul_le_mul_of_nonneg_right (by linarith [hlo k]) (energy_nonneg _ _)

/-- Explicit squared-state bound, with constants rather than an existential rate. -/
theorem jitter_state_bound (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminmax : hmin ≤ 1 / 6)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (hx : ∀ n, x (n + 1) = positionStep (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = velocityStep (h n) (x n) (v n)) (n : ℕ) :
    x n ^ 2 + v n ^ 2 ≤
      12 * (1 - hmin / 3) ^ n * (x 0 ^ 2 + v 0 ^ 2) := by
  have hb := jitter_energy_bound h x v hmin0 hminmax hlo hhi hx hv n
  have hl := energy_lower (x n) (v n)
  have hu := mul_le_mul_of_nonneg_left (energy_upper (x 0) (v 0))
    (pow_nonneg (by linarith : 0 ≤ 1 - hmin / 3) n)
  nlinarith only [hb, hl, hu]

end LeanControls.PD
