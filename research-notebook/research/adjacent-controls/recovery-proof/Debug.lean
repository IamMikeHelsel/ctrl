module
public import TerminalBase
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
@[expose] public section
noncomputable section
namespace LeanControls.RecoveryTerminal
open Matrix BernsteinCertificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem exp_point_0 : ((324651/1000000:ℚ):ℝ) ≤ Real.exp ((-9/8:ℚ):ℝ) ∧
    Real.exp ((-9/8:ℚ):ℝ) ≤ ((324653/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((284891/500000:ℚ):ℝ)) (b := ((569783/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_1 : ((2577/8000:ℚ):ℝ) ≤ Real.exp ((-145/128:ℚ):ℝ) ∧
    Real.exp ((-145/128:ℚ):ℝ) ≤ ((322127/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((567561/1000000:ℚ):ℝ)) (b := ((283781/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem held_terminal_coordinates {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℝ) :
    UncertainLag.heldSegment r (5/4) z (-1) =
      ![z 0 + z 1*1.25 - 0.78125 + (z 2+1)*r⁻¹*(1.25-(1-Real.exp (-r*(5/4)))*r⁻¹),
        z 1-1.25+(z 2+1)*(1-Real.exp (-r*(5/4)))*r⁻¹,
        -1+(z 2+1)*Real.exp (-r*(5/4))] := by
  have hn := ne_of_gt hr
  ext i
  fin_cases i <;> dsimp [UncertainLag.heldSegment, UncertainLag.heldSolution] <;>
    field_simp <;> ring

theorem cell_0 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((9/10:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((29/32:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((2577/8000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_1.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((324653/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_0.2
  have hirlo : ((32/29:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((10/9:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((9/10:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  trace_state
  set_option trace.Tactic.inclusion true in
    dyadic_interval (native := false) [prec := 30]


end LeanControls.RecoveryTerminal
