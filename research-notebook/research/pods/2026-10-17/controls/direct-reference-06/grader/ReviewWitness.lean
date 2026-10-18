import DirectReference
open LeanControls.DirectReference LeanControls.ScaledTracking LeanControls.UncertainLag
example : ¬ |jerk 0 0| ≤ (9 : ℝ) := by rw [initial_jerk]; norm_num
example : (44218/1600000 : ℝ) ≠ reference 1 (duration 1) 0 := by
  norm_num [reference, duration, position]
example (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) :
    physicalInput 10 f q j t = q t 2 - 800 * (f t 0 - q t 0) -
      60 * (f t 1 - q t 1) - (f t 2 - q t 2)/2 + j t/96 := by
  norm_num [physicalInput]
  ring
