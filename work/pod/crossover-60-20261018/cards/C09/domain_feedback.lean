import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
namespace C09Feedback
/-- Joint baseline and demodulation bounds, without replacing shared variables
by independent estimates. -/
theorem coupled_error_bound (x D K eps ell : ℝ)
    (he0 : 0≤ell) (he1 : ell<1)
    (hx : x≤eps+ell*D) (hD : D≤K+x) :
    x≤(eps+ell*K)/(1-ell) ∧ D≤K+(eps+ell*K)/(1-ell) := by
  have hb : x≤(eps+ell*K)/(1-ell) := by
    apply (le_div_iff₀ (by linarith : 0<1-ell)).2
    have h := mul_le_mul_of_nonneg_left hD he0
    nlinarith
  exact ⟨hb,by linarith⟩

theorem phase_free_complex_bound (a d transfer : ℂ) (x D : ℝ)
    (ha : ‖a‖≤x) (hd : ‖d‖≤D) (ht : ‖transfer‖≤1) :
    ‖a+transfer*d‖≤x+D := by
  calc
    _ ≤ ‖a‖+‖transfer*d‖ := norm_add_le _ _
    _ = ‖a‖+‖transfer‖*‖d‖ := by rw [norm_mul]
    _ ≤ x+1*D := add_le_add ha (mul_le_mul ht hd (norm_nonneg d) (by norm_num))
    _ = x+D := by ring

theorem retained_numeric_bounds :
    ((1/40:ℝ)+(1/99)*(3/5))/(1-1/99)=123/3920 ∧
    (3/5:ℝ)+123/3920=495/784 ∧
    (123/3920:ℝ)+495/784=1299/1960 ∧
    (123/3920:ℝ)<1/8 ∧ (1299/1960:ℝ)<3/4 := by norm_num

#print axioms coupled_error_bound
#print axioms phase_free_complex_bound
#print axioms retained_numeric_bounds
end C09Feedback
