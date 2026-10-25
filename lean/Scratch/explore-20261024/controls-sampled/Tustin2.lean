import ControlsLean.Controls.Hurwitz2
import ControlsLean.Controls.Jury2

/-!
Tustin on second-order polynomials. Substituting `s = c (z - 1)/(z + 1)` (`c = 2/h`) in
`s² + a s + b` and clearing `(z+1)²` gives
`D z² + (2b - 2c²) z + (c² - a c + b)` with `D = c² + a c + b`.
The continuous polynomial is Hurwitz iff the monic discrete polynomial is Schur.
-/

namespace ControlsLean.Controls

theorem tustin_isHurwitz2_iff_isSchur2 {a b c : ℝ} (hc : 0 < c) (hD : 0 < c ^ 2 + a * c + b) :
    IsHurwitz2 a b ↔
      IsSchur2 ((2 * b - 2 * c ^ 2) / (c ^ 2 + a * c + b))
        ((c ^ 2 - a * c + b) / (c ^ 2 + a * c + b)) := by
  rw [isHurwitz2_iff, isSchur2_iff, abs_lt, abs_lt, lt_div_iff₀ hD, div_lt_iff₀ hD,
    one_add_div hD.ne', lt_div_iff₀ hD, div_lt_div_iff_of_pos_right hD]
  simp only [neg_mul, div_mul_cancel₀ _ hD.ne']
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have hb : 0 < b := by nlinarith
    exact ⟨by nlinarith, hb⟩

/-- The constraint `D > 0` is automatic for Hurwitz polynomials. -/
theorem tustin_isSchur2_of_isHurwitz2 {a b c : ℝ} (hc : 0 < c) (h : IsHurwitz2 a b) :
    IsSchur2 ((2 * b - 2 * c ^ 2) / (c ^ 2 + a * c + b))
        ((c ^ 2 - a * c + b) / (c ^ 2 + a * c + b)) := by
  have ⟨ha, hb⟩ := (isHurwitz2_iff a b).mp h
  exact (tustin_isHurwitz2_iff_isSchur2 hc (by positivity)).mp h

end ControlsLean.Controls

#print axioms ControlsLean.Controls.tustin_isHurwitz2_iff_isSchur2
