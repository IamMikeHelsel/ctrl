import CausalAdmission
open CausalAdmission
theorem falseStrongerDeadline : ¬ (∀ a j s : ℝ → ℝ,
    IsAdmissible (5/2) 10 400 (3/10) a j s → a (3/10) ≤ 0 →
    deadline (5/2) 10 400 + 10/400 ≤ (3/10 : ℝ)) := by
  intro h
  have ha : IsAdmissible (5/2) 10 400 (3/10)
      (leastAccel (5/2) 10 400) (leastJerk 10 400) (leastSnap 10 400) :=
    least_isAdmissible _ _ (by norm_num) (by norm_num)
  have hz : leastAccel (5/2) 10 400 (3/10) = 0 := by
    rw [← exact_earliest_deadline]
    exact least_reaches_zero (by norm_num) (by norm_num) (by norm_num)
  have hb := h _ _ _ ha hz.le
  norm_num [deadline, rampTime] at hb
#print axioms falseStrongerDeadline
