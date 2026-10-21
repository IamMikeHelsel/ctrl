import Mathlib

namespace R03ClockBounds

noncomputable def bias (t : ℝ) : ℝ :=
  if t≤-1/100 then 0 else if t≤0 then 1/200+t/2 else
    if t≤1/100 then 1/200-t/2 else 0
noncomputable def clock (t : ℝ) : ℝ := t+bias t

theorem bias_bounds (t : ℝ) : 0≤bias t ∧ bias t≤1/200 := by
  unfold bias
  split_ifs <;> constructor <;> linarith

theorem clock_strictly_increasing : StrictMono clock := by
  intro a b hab
  unfold clock bias
  split_ifs <;> linarith

theorem left_clock {t : ℝ} (hlo : -1/100<t) (hhi : t≤0) :
    clock t = 1/200+3/2*t := by
  simp [clock, bias, not_le.mpr hlo, hhi]
  ring

theorem right_clock {t : ℝ} (hlo : 0<t) (hhi : t≤1/100) :
    clock t = 1/200+1/2*t := by
  have hn : ¬t≤-1/100 := by linarith
  unfold clock bias
  rw [if_neg hn, if_neg (not_le.mpr hlo), if_pos hhi]
  ring

end R03ClockBounds
#print axioms R03ClockBounds.bias_bounds
#print axioms R03ClockBounds.clock_strictly_increasing
#print axioms R03ClockBounds.left_clock
#print axioms R03ClockBounds.right_clock
