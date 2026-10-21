import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace V11CriticFaultBridge
-- Both worlds use the SAME four observations. Each full four-branch disjunction
-- asserts at least three valid row bounds, so no selected-branch assumption is hidden.
theorem two_world_diameter (x y X Y o1 o2 o3 o4 e : ℝ) (he : 0 ≤ e)
    (ha :
      (|x-o1|≤e ∧ |y-o2|≤e ∧ |x+y-o3|≤e) ∨
      (|x-o1|≤e ∧ |y-o2|≤e ∧ |x+2*y-o4|≤e) ∨
      (|x-o1|≤e ∧ |x+y-o3|≤e ∧ |x+2*y-o4|≤e) ∨
      (|y-o2|≤e ∧ |x+y-o3|≤e ∧ |x+2*y-o4|≤e))
    (hb :
      (|X-o1|≤e ∧ |Y-o2|≤e ∧ |X+Y-o3|≤e) ∨
      (|X-o1|≤e ∧ |Y-o2|≤e ∧ |X+2*Y-o4|≤e) ∨
      (|X-o1|≤e ∧ |X+Y-o3|≤e ∧ |X+2*Y-o4|≤e) ∨
      (|Y-o2|≤e ∧ |X+Y-o3|≤e ∧ |X+2*Y-o4|≤e)) :
    |x-X|≤6*e ∧ |y-Y|≤4*e := by
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;>
    rcases abs_le.mp ha.1 with ⟨ha1,ha2⟩ <;>
    rcases abs_le.mp ha.2.1 with ⟨ha3,ha4⟩ <;>
    rcases abs_le.mp ha.2.2 with ⟨ha5,ha6⟩ <;>
    rcases abs_le.mp hb.1 with ⟨hb1,hb2⟩ <;>
    rcases abs_le.mp hb.2.1 with ⟨hb3,hb4⟩ <;>
    rcases abs_le.mp hb.2.2 with ⟨hb5,hb6⟩ <;>
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
#print axioms two_world_diameter
end V11CriticFaultBridge
