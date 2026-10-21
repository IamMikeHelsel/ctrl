import Mathlib
namespace C11Center
theorem minimax_contains (L U p : ℝ) (hL : L ≤ p) (hU : p ≤ U) :
    |p-(L+U)/2| ≤ (U-L)/2 := by
  apply abs_le.mpr; constructor <;> linarith

theorem minimax_lower (L U c R : ℝ) (hL : |L-c| ≤ R) (hU : |U-c| ≤ R) :
    (U-L)/2 ≤ R := by
  have hl := abs_le.mp hL; have hu := abs_le.mp hU; linarith

theorem feasible_center (L U c R : ℝ) :
    (U-c ≤ R ∧ c-L ≤ R) ↔ (U-R ≤ c ∧ c ≤ L+R) := by
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem one_sided_clearance (L U R e : ℝ) (he : 0 ≤ e)
    (hgap : U-L+e ≤ 2*R) :
    U-(U-R+e) ≤ R ∧ (U-R+e)-L ≤ R ∧ (U-R+e)+R = U+e := by
  constructor; · linarith
  constructor; · linarith
  ring

theorem nominal_clearance :
    (141177825/1000000000 : ℝ) - 2221/40000 + 1/1000 = 86652825/1000000000 ∧
    (86652825/1000000000 : ℝ) + 2221/40000 = 142177825/1000000000 ∧
    (142177825/1000000000 : ℝ) < 15/100 ∧
    (141177825/1000000000 : ℝ) - 51464675/1000000000 + 1/1000 < 2*(2221/40000) := by
  norm_num
#print axioms minimax_contains
#print axioms minimax_lower
#print axioms feasible_center
#print axioms one_sided_clearance
#print axioms nominal_clearance
end C11Center
