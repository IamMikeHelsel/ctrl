import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignR11
/-- Same-frame angle and angular-rate estimate errors enter the inverse command additively. -/
theorem sensor_command_bound (eb ev B V a : ℝ) (ha : 0 < a)
    (hb : |eb| ≤ B) (hv : |ev| ≤ V) : |-eb-ev/a| ≤ B+V/a := by
  calc
    |-eb-ev/a| = |eb+ev/a| := by
      rw [show -eb-ev/a=-(eb+ev/a) by ring,abs_neg]
    _ ≤ |eb|+|ev/a| := abs_add_le _ _
    _ = |eb|+|ev|/a := by rw [abs_div,abs_of_pos ha]
    _ ≤ B+V/a := add_le_add hb (div_le_div_of_nonneg_right hv (le_of_lt ha))

/-- Inward vector-field inequalities for an assumed error ODE; global invariance
    still needs an execution/comparison theorem. -/
theorem tube_faces (a D W E delta w : ℝ) (ha : 0 ≤ a)
    (hd : |delta| ≤ D) (hw : |w| ≤ W) (budget : a*D+W ≤ a*E) :
    -a*E+a*delta+w ≤ 0 ∧ a*E+a*delta+w ≥ 0 := by
  obtain ⟨hdl,hdu⟩ := abs_le.mp hd
  obtain ⟨hwl,hwu⟩ := abs_le.mp hw
  have hp := mul_le_mul_of_nonneg_left hdu ha
  have hm := mul_le_mul_of_nonneg_left hdl ha
  constructor <;> nlinarith

theorem measured_budget :
    (33/8000:ℝ)+1/10000+(1/200)/40+(1/100)/40 = 23/5000 ∧
    (23/5000:ℝ) < 1/200 ∧
    (1/10:ℝ)+1+40*(1/200)+40*(33/8000+1/10000+(1/200)/40)+1/100 = 371/250 ∧
    (371/250:ℝ) < 3/2 := by norm_num

/-- Inner reference tracking and outer target tracking are distinct error terms. -/
theorem output_target_bound (theta reference target E G : ℝ)
    (he : |theta-reference| ≤ E) (hg : |reference-target| ≤ G) :
    |theta-target| ≤ E+G := by
  calc
    |theta-target| = |(theta-reference)+(reference-target)| := by ring_nf
    _ ≤ |theta-reference|+|reference-target| := abs_add_le _ _
    _ ≤ E+G := add_le_add he hg
end CampaignR11
#print axioms CampaignR11.sensor_command_bound
#print axioms CampaignR11.tube_faces
#print axioms CampaignR11.measured_budget
#print axioms CampaignR11.output_target_bound
