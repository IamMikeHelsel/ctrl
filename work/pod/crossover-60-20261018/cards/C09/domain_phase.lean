import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
namespace C09Phase

theorem phase_chord (θ : ℝ) : ‖Complex.exp (Complex.I*θ)-1‖≤|θ| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  norm_num
  calc
    2*|Real.sin (θ/2)| ≤ 2*|θ/2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |θ| := by rw [abs_div]; norm_num; ring

theorem phase_change_bound (θ : ℝ) (d : ℂ) (D : ℝ) (hd : ‖d‖≤D) :
    ‖Complex.exp (Complex.I*θ)*d-d‖≤|θ| * D := by
  rw [show Complex.exp (Complex.I*θ)*d-d=(Complex.exp (Complex.I*θ)-1)*d by ring,norm_mul]
  exact mul_le_mul (phase_chord θ) hd (norm_nonneg d) (abs_nonneg θ)

theorem one_beat_phase_budget (δ : ℝ) (hδ : |δ|≤1/100) :
    2*Real.pi*|δ| * 2≤22/175 := by
  have hp : Real.pi<22/7 := lt_trans Real.pi_lt_d20 (by norm_num)
  have h := mul_le_mul_of_nonneg_left hδ (show 0≤4*Real.pi by positivity)
  nlinarith

theorem final_numeric_margin :
    (3/5:ℝ)+22/175=127/175 ∧ (127/175:ℝ)<3/4 ∧
    (3/4:ℝ)-127/175=17/700 := by norm_num

#print axioms phase_chord
#print axioms phase_change_bound
#print axioms one_beat_phase_budget
#print axioms final_numeric_margin
end C09Phase
