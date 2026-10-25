import Mathlib
set_option maxHeartbeats 400000
namespace Factory
def statement : Prop :=
  ∀ (x z dx dz ε : ℝ), 0 ≤ ε → ε < z → |dz| ≤ ε →
    0 < z + dz ∧
    |(x+dx)/(z+dz) - x/z| ≤ (|dx| * z + |x| * ε) / (z * (z - ε))
theorem solution : statement := by
  unfold statement
  intro x z dx dz ε he hz hdz
  have hzpos : 0 < z := lt_of_le_of_lt he hz
  have hlo := (abs_le.mp hdz).1
  have hzp : 0 < z + dz := by linarith
  have hmargin : 0 < z - ε := sub_pos.mpr hz
  have hd1 : 0 < z * (z + dz) := mul_pos hzpos hzp
  have hd2 : 0 < z * (z - ε) := mul_pos hzpos hmargin
  refine ⟨hzp, ?_⟩
  have hid : (x + dx) / (z + dz) - x / z =
      (dx * z - x * dz) / (z * (z + dz)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hd1]
  apply (div_le_div_iff₀ hd1 hd2).mpr
  have hn : |dx * z - x * dz| ≤ |dx| * z + |x| * ε := by
    calc
      |dx * z - x * dz| ≤ |dx * z| + |x * dz| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (dx * z) 0 (x * dz))
      _ = |dx| * z + |x| * |dz| := by rw [abs_mul, abs_mul, abs_of_pos hzpos]
      _ ≤ |dx| * z + |x| * ε :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hdz (abs_nonneg x))
  have hb : 0 ≤ |dx| * z + |x| * ε :=
    add_nonneg (mul_nonneg (abs_nonneg dx) hzpos.le) (mul_nonneg (abs_nonneg x) he)
  have hd : z * (z - ε) ≤ z * (z + dz) :=
    mul_le_mul_of_nonneg_left (by linarith) hzpos.le
  exact (mul_le_mul_of_nonneg_right hn hd2.le).trans (mul_le_mul_of_nonneg_left hd hb)
example : statement := solution
#print axioms solution
end Factory
