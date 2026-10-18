import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open Set Filter
open scoped Topology

-- A bounded tractability probe. This is not the full proposed certificate.
namespace RobotMotionPreflight

theorem positive_part_pow_derivative (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max y 0)^n)
      ((n : ℝ) * (max x 0)^(n-1)) x := by
  have away (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt (fun z : ℝ => (max z 0)^n)
        ((n : ℝ) * (max y 0)^(n-1)) y := by
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have heq : (fun z : ℝ => (max z 0)^n) =ᶠ[𝓝 y] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with z hz
        change z < 0 at hz
        simp [max_eq_right (le_of_lt hz), Nat.ne_of_gt (by omega : 0 < n)]
      have hd := (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq heq
      simpa [max_eq_right (le_of_lt hneg), Nat.ne_of_gt (by omega : 0 < n-1)] using hd
    · have heq : (fun z : ℝ => (max z 0)^n) =ᶠ[𝓝 y] (fun z => z^n) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with z hz
        change 0 < z at hz
        simp [max_eq_left (le_of_lt hz)]
      simpa [max_eq_left (le_of_lt hpos)] using
        ((hasDerivAt_id y).pow n).congr_of_eventuallyEq heq
  exact hasDerivAt_of_hasDerivAt_of_ne' away
    (((continuous_id.max continuous_const).pow n).continuousAt)
    ((continuous_const.mul ((continuous_id.max continuous_const).pow (n-1))).continuousAt) x

#print axioms positive_part_pow_derivative
end RobotMotionPreflight
