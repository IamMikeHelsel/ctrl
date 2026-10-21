import Mathlib.Tactic
namespace V12Residual
-- B11=1 fixes scale; residuals correspond to five actual Zhang rows for I,Rx,Ry with c=3/5,s=4/5.
theorem row_inverse (b12 b22 b13 b23 b33 : ℝ) :
 b13=(5/4)*((3/5)*b12+(4/5)*b13)-(3/4)*b12 ∧
 b23=(3/4)*b12-(5/4)*((3/5)*b12-(4/5)*b23) ∧
 b33-1=-(25/16)*(1-(9/25)*b22-(24/25)*b23-(16/25)*b33)
            -(9/16)*(b22-1)-(3/2)*b23 := by constructor; ring; constructor <;> ring

theorem metric_bounds (b12 b22 b13 b23 b33 e : ℝ) (he : 0≤e)
 (h0 : |b12|≤e) (h1 : |b22-1|≤e)
 (h2 : |(3/5)*b12+(4/5)*b13|≤e)
 (h3 : |(3/5)*b12-(4/5)*b23|≤e)
 (h4 : |1-(9/25)*b22-(24/25)*b23-(16/25)*b33|≤e) :
 |b13|≤2*e ∧ |b23|≤2*e ∧ |b33-1|≤(41/8)*e := by
 rw [abs_le] at h0 h1 h2 h3 h4
 have hp : -(2*e)≤b13 ∧ b13≤2*e := by constructor <;> linarith
 have hq : -(2*e)≤b23 ∧ b23≤2*e := by constructor <;> linarith
 refine ⟨abs_le.mpr hp,abs_le.mpr hq,?_⟩
 rw [abs_le]; constructor <;> linarith

-- Row diagonal-dominance margin. Matrix norm and physical pixel-to-row noise binding remain separate.
theorem row_margins (e : ℝ) (he : 0≤e) (hsmall : e≤1/100) :
 1-3*e≥73/80 ∧ 1-4*e≥73/80 ∧ 1-(73/8)*e≥727/800 := by
 constructor; linarith; constructor <;> linarith
end V12Residual
#print axioms V12Residual.row_inverse
#print axioms V12Residual.metric_bounds
#print axioms V12Residual.row_margins
