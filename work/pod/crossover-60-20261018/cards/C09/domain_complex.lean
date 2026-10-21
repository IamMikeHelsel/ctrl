import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
namespace C09Complex

theorem wheel_residual_bound (w d L e z : ℂ) (ell D E : ℝ)
    (hz : z=w+L*d+e) (hL : ‖L‖≤ell) (hd : ‖d‖≤D) (he : ‖e‖≤E) :
    ‖w-z‖≤ell*D+E := by
  have hell : 0≤ell := le_trans (norm_nonneg L) hL
  have hid : w-z=-(L*d+e) := by rw [hz]; ring
  rw [hid,norm_neg]
  calc
    _ ≤ ‖L*d‖+‖e‖ := norm_add_le _ _
    _ = ‖L‖*‖d‖+‖e‖ := by rw [norm_mul]
    _ ≤ ell*D+E := add_le_add (mul_le_mul hL hd (norm_nonneg d) hell) he

theorem convex_norm_bound (a b : ℂ) (ρ M : ℝ) (hρ0 : 0≤ρ) (hρ1 : ρ≤1)
    (ha : ‖a‖≤M) (hb : ‖b‖≤M) :
    ‖((1-ρ:ℝ):ℂ)*a+(ρ:ℂ)*b‖≤M := by
  have h0 : 0≤1-ρ := by linarith
  calc
    _ ≤ ‖((1-ρ:ℝ):ℂ)*a‖+‖(ρ:ℂ)*b‖ := norm_add_le _ _
    _ = (1-ρ)*‖a‖+ρ*‖b‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
        Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg hρ0]
    _ ≤ M := by
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr ha),mul_nonneg hρ0 (sub_nonneg.mpr hb)]

theorem mixed_residual_bound (w d b z e₀ : ℂ) (ρ M : ℝ)
    (hbase : b=w+d+e₀) (hρ0 : 0≤ρ) (hρ1 : ρ≤1)
    (hw : ‖w-z‖≤M) (hb : ‖b-z-e₀‖≤M) :
    ‖w-z+(ρ:ℂ)*d‖≤M := by
  have h := convex_norm_bound (w-z) (b-z-e₀) ρ M hρ0 hρ1 hw hb
  have hi : ((1-ρ:ℝ):ℂ)*(w-z)+(ρ:ℂ)*(b-z-e₀)=w-z+(ρ:ℂ)*d := by
    rw [hbase]
    push_cast
    ring
  simpa only [hi] using h

theorem baseline_endpoint_bound (b z e₀ : ℂ) (E : ℝ) (he : ‖e₀‖≤E) :
    ‖b-z-e₀‖≤‖b-z‖+E := by
  exact le_trans (norm_sub_le _ _) (add_le_add le_rfl he)

theorem numeric_budgets :
    (1/99:ℝ)*2+1/40=179/3960 ∧ (179/3960:ℝ)<1/8 ∧
    (1/2:ℝ)+1/10=3/5 ∧ (3/5:ℝ)<3/4 := by norm_num

#print axioms wheel_residual_bound
#print axioms convex_norm_bound
#print axioms mixed_residual_bound
#print axioms baseline_endpoint_bound
#print axioms numeric_budgets
end C09Complex
