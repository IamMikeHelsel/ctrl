import DirectReference
open LeanControls.DirectReference
example : ¬ |jerk 0 0| ≤ (9 : ℝ) := by rw [initial_jerk]; norm_num
example : (44218/1600000 : ℝ) ≠ 44217/1600000 := by norm_num
