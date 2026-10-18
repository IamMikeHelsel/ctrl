module
public import LeanControls.UncertainTravel
@[expose] public section
noncomputable section
namespace LeanControls.DirectSwitch
open UncertainLag
open BernsteinCertificate

def start : State := ![1, 1/2, 0]
def brake (t : ℝ) : State := heldSegment 1 t start (-1)

/-- The exponential terms cancel from the feedback request for this start. -/
theorem request_polynomial (t : ℝ) :
    input (brake t) = t^2/2 + 3*t/2 - 5/2 := by
  simp [input, SaturatedLag.input, brake, start, heldSegment, heldSolution]
  ring

/-- Every sample through 0.7 still requests full braking. -/
theorem request_before_switch {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 7/10) :
    input (brake t) ≤ -1 := by
  rw [request_polynomial]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]

theorem request_at_switch : input (brake (4/5)) = -49/50 := by
  rw [request_polynomial]
  norm_num

theorem command_at_switch : RobustPD.saturate 1 (input (brake (4/5))) = -49/50 := by
  rw [request_at_switch]
  norm_num [RobustPD.saturate]

/-- The state at release is still outside the invariant ellipsoid. -/
theorem energy_at_switch :
    energy Generated.TravelQuarterLower.P (brake (4/5)) =
      61323/5000 + (997/625)*Real.exp (-(4/5:ℝ)) +
        (189/50)*(Real.exp (-(4/5:ℝ)))^2 := by
  simp [energy, Generated.TravelQuarterLower.P, brake, start, heldSegment,
    heldSolution, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem outside_at_switch :
    12 < energy Generated.TravelQuarterLower.P (brake (4/5)) := by
  rw [energy_at_switch]
  nlinarith [Real.exp_pos (-(4/5:ℝ)), sq_nonneg (Real.exp (-(4/5:ℝ)))]

theorem brake_add (t s : ℝ) :
    heldSegment 1 s (brake t) (-1) = brake (t+s) := by
  ext i
  fin_cases i <;>
    simp [brake, start, heldSegment, heldSolution, Real.exp_add] <;> ring

theorem command_before_switch {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 7/10) :
    RobustPD.saturate 1 (input (brake t)) = -1 := by
  have h := request_before_switch ht0 ht1
  simp only [RobustPD.saturate]
  rw [min_eq_right (by linarith), max_eq_left h]

/-- The actual sampled recurrence follows the brake through its eighth sample. -/
theorem samples_before_switch (n : ℕ) (hn : n ≤ 8) :
    UncertainTravel.samples 1 (fun _ => 1/10) (fun _ => 0) (fun _ => 0) start n =
      brake ((n:ℝ)/10) := by
  induction n with
  | zero => simp [UncertainTravel.samples, brake, heldSegment_zero]
  | succ n ih =>
    have hn7 : n ≤ 7 := by omega
    have ht : (n:ℝ)/10 ≤ 7/10 := by exact_mod_cast (div_le_div_of_nonneg_right
      (show (n:ℝ) ≤ 7 by exact_mod_cast hn7) (by norm_num : (0:ℝ) ≤ 10))
    rw [UncertainTravel.samples_succ, ih (by omega)]
    simp only [UncertainTravel.segment, add_zero]
    rw [command_before_switch (by positivity) ht, brake_add]
    congr 1
    push_cast
    ring

theorem sampled_release_outside :
    let z := UncertainTravel.samples 1 (fun _ => 1/10) (fun _ => 0)
      (fun _ => 0) start 8
    RobustPD.saturate 1 (input z) = -49/50 ∧
      12 < energy Generated.TravelQuarterLower.P z := by
  dsimp only
  rw [samples_before_switch 8 (by omega)]
  norm_num only [Nat.cast_ofNat, show (8:ℝ)/10 = 4/5 by norm_num]
  exact ⟨by simpa only [neg_div] using command_at_switch, outside_at_switch⟩

end LeanControls.DirectSwitch
#print axioms LeanControls.DirectSwitch.request_polynomial
#print axioms LeanControls.DirectSwitch.request_before_switch
#print axioms LeanControls.DirectSwitch.request_at_switch
#print axioms LeanControls.DirectSwitch.command_at_switch
#print axioms LeanControls.DirectSwitch.energy_at_switch
#print axioms LeanControls.DirectSwitch.outside_at_switch
#print axioms LeanControls.DirectSwitch.brake_add
#print axioms LeanControls.DirectSwitch.command_before_switch
#print axioms LeanControls.DirectSwitch.samples_before_switch
#print axioms LeanControls.DirectSwitch.sampled_release_outside
