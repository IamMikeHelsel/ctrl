import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace V11Selection
/-- The omitted cross term is needed when interpreting variance after admission. -/
theorem posterior_square_with_cross (e v k : ℝ) :
    ((1-k)*e+k*v)^2 = (1-k)^2*e^2+k^2*v^2+2*k*(1-k)*e*v := by ring
/-- Four equally weighted product-law worlds (e,v)=(-1,-1),(-1,1),(1,-1),(1,1).
This certifies their moments arithmetically; the product-law enumeration is explicit. -/
theorem four_world_moments :
    ((-1:ℝ)+(-1)+1+1)/4=0 ∧
    ((-1:ℝ)+1+(-1)+1)/4=0 ∧
    ((-1:ℝ)^2+(-1)^2+1^2+1^2)/4=1 ∧
    ((-1:ℝ)^2+1^2+(-1)^2+1^2)/4=1 ∧
    ((-1:ℝ)*(-1)+(-1)*1+1*(-1)+1*1)/4=0 ∧
    ((((-1:ℝ)+(-1))/2)^2+((-1+1)/2)^2+((1+(-1))/2)^2+((1+1)/2)^2)/4=1/2 := by
  norm_num
/-- Residual-zero admission keeps exactly the two equal-sign worlds.
Their mean error stays zero but their covariance cross term becomes one. -/
theorem accepted_world_moments :
    ((-1:ℝ)-(-1)=0) ∧ ¬ ((1:ℝ)-(-1)=0) ∧
    ¬ ((-1:ℝ)-1=0) ∧ ((1:ℝ)-1=0) ∧
    ((-1:ℝ)+1)/2=0 ∧
    ((-1:ℝ)*(-1)+1*1)/2=1 ∧
    ((((-1:ℝ)+(-1))/2)^2+((1+1)/2)^2)/2=1 ∧
    (1:ℝ)/2 < 1 := by norm_num
#print axioms posterior_square_with_cross
#print axioms four_world_moments
#print axioms accepted_world_moments
end V11Selection
