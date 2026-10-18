module

public import LeanControls.Trajectories

public section
noncomputable section

namespace LeanControls.BoundaryChecks

open PD SampledPD

/-- At h = 2/3 the held-input update has a nondecaying two-cycle. -/
theorem boundary_position (v : ℝ) : position (2 / 3) 0 v = 0 := by
  unfold position SampledPD.control
  ring

theorem boundary_velocity (v : ℝ) : velocity (2 / 3) 0 v = -v := by
  unfold velocity SampledPD.control
  ring

/-- A trajectory satisfying the exact recurrence but retaining energy one forever. -/
theorem boundary_cycle (n : ℕ) :
    position (2 / 3) 0 ((-1 : ℝ) ^ n) = 0 ∧
    velocity (2 / 3) 0 ((-1 : ℝ) ^ n) = (-1 : ℝ) ^ (n + 1) ∧
    energy 0 ((-1 : ℝ) ^ n) = 1 := by
  refine ⟨boundary_position _, ?_, ?_⟩
  · rw [boundary_velocity, pow_succ]
    ring
  · have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    simp only [energy]
    rw [hs]
    ring

/-- A large step can increase the certificate: sampling bounds are substantive. -/
theorem large_step_increases : energy 0 1 < energy (position 1 0 1) (velocity 1 0 1) := by
  norm_num [energy, position, velocity, SampledPD.control]

/-- A persistent error floor prevents convergence even for a scalar contraction. -/
theorem scalar_error_floor : ∀ _n : ℕ,
    (1 : ℝ) = (9 / 10 : ℝ) * 1 + 1 / 10 := by
  intro _
  norm_num

end LeanControls.BoundaryChecks
