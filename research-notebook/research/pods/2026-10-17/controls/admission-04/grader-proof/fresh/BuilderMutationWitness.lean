import CausalAdmission
open CausalAdmission
example : IsAdmissible (5/2) 10 400 (3/10)
    (leastAccel (5/2) 10 400) (leastJerk 10 400) (leastSnap 10 400) :=
  least_isAdmissible _ _ (by norm_num) (by norm_num)
example : leastAccel (5/2) 10 400 (3/10) = 0 := by
  rw [← exact_earliest_deadline]
  exact least_reaches_zero (by norm_num) (by norm_num) (by norm_num)
example : ¬ deadline (5/2) 10 400 + 10/400 ≤ (3/10 : ℝ) := by
  norm_num [deadline, rampTime]
