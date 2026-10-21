import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
namespace CampaignC03Dual
open MeasureTheory
 theorem support_pointwise (p u S : ℝ) (h : |u| ≤ S) : p*u ≤ S* |p| := by
  calc
    p*u ≤ |p*u| := le_abs_self _
    _ = |p| * |u| := abs_mul _ _
    _ ≤ |p| * S := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = S* |p| := mul_comm _ _
 theorem dual_polynomial (x : ℝ) :
 (1-x)^3/6 = (-x^3/6+x^2/4-5*x/48+1/96)+(5/32-19*x/48+x^2/4) := by ring
 theorem dual_factor (x : ℝ) :
 -x^3/6+x^2/4-5*x/48+1/96 = -(x-1/2)*(x^2-x+1/8)/6 := by ring
 theorem moment_rejection (m0 m1 m2 m3 B : ℝ) (h0 : m0=0) (h1 : m1=0) (h2 : m2=0)
 (hbound : -m3/6+m2/4-5*m1/48+m0/96≤B) : -m3/6≤B := by simpa [h0,h1,h2] using hbound
 theorem primitive_area (a : ℝ) (ha : a*(1-a)=1/8) :
 2*(-a^4/24+a^3/12-5*a^2/96+a/96)+
 2*(-(1-a)^4/24+(1-a)^3/12-5*(1-a)^2/96+(1-a)/96)=1/384 := by
  have h : 2*(-a^4/24+a^3/12-5*a^2/96+a/96)+
   2*(-(1-a)^4/24+(1-a)^3/12-5*(1-a)^2/96+(1-a)/96) =
   a*(1-a)/24-(a*(1-a))^2/6 := by ring
  rw [h,ha]
  norm_num
 theorem physical_budget :
 (400*(1/10)^4/384:ℝ)=1/9600 ∧ (1/9600:ℝ)<1/1000 ∧
 (1/1000:ℝ)<400*(1/10)^4/24 := by norm_num
 theorem jerk_authority (r : ℝ) (hr : r^2=2) (hp : 0≤r) : |20*(r-1)|<10 := by
  have hu : r<3/2 := by nlinarith
  have hl : 1<r := by nlinarith
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith
 theorem integral_support (P u : ℝ → ℝ) (a b S : ℝ) (hab : a≤b)
 (hf : IntervalIntegrable (fun t => P t*u t) volume a b)
 (hg : IntervalIntegrable (fun t => S* |P t|) volume a b)
 (hu : ∀ t ∈ Set.Icc a b, |u t|≤S) :
 (∫ t in a..b, P t*u t) ≤ ∫ t in a..b, S* |P t| := by
  apply intervalIntegral.integral_mono_on hab hf hg
  intro t ht
  exact support_pointwise _ _ _ (hu t ht)
 theorem integral_gate (P u : ℝ → ℝ) (a b S q B : ℝ) (hab : a≤b)
 (hf : IntervalIntegrable (fun t => P t*u t) volume a b)
 (hg : IntervalIntegrable (fun t => S* |P t|) volume a b)
 (hu : ∀ t ∈ Set.Icc a b, |u t|≤S)
 (hbind : q = ∫ t in a..b, P t*u t)
 (hbudget : (∫ t in a..b, S* |P t|) ≤ B) : q≤B := by
  rw [hbind]
  exact le_trans (integral_support P u a b S hab hf hg hu) hbudget
end CampaignC03Dual
#print axioms CampaignC03Dual.support_pointwise
#print axioms CampaignC03Dual.dual_polynomial
#print axioms CampaignC03Dual.dual_factor
#print axioms CampaignC03Dual.moment_rejection
#print axioms CampaignC03Dual.primitive_area
#print axioms CampaignC03Dual.physical_budget
#print axioms CampaignC03Dual.jerk_authority
#print axioms CampaignC03Dual.integral_support
#print axioms CampaignC03Dual.integral_gate
