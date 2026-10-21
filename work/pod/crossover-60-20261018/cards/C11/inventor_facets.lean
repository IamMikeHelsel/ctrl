import Mathlib.Tactic
namespace C11Inventor

/-- Actual pending-command drift in the third C3 tilted coordinate. -/
theorem third_facet_inward (v a r d : ℝ)
    (hv : v ≤ 813/20000) (ha : 0 ≤ a)
    (hr : 8 ≤ r) (hd : d ≤ 1/100) :
    v+a/2+r*(-121/100+d-a)/16 ≤ -11187/20000 := by
  have p : 0 ≤ (r-8)*(a+6/5) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(1/100-d) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem third_facet_lower (v a r d : ℝ)
    (hv : 367/20000 ≤ v) (hal : 0 ≤ a) (hah : a ≤ 13/10)
    (hrl : 0 ≤ r) (hrh : r ≤ 12) (hd : -1/100 ≤ d) :
    -24433/20000 ≤ v+a/2+r*(-121/100+d-a)/16 := by
  have p : 0 ≤ (12-r)*(a+61/50) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(d+1/100) := mul_nonneg hrl (by linarith)
  nlinarith

theorem other_facets_positive (v a : ℝ)
    (hv : 367/20000 ≤ v) (ha : 14561/12500 ≤ a) :
    0 < v ∧ 0 < v+a/4 := by constructor <;> linarith

/-- Exact opposite-side barriers for the three sign-monotone facets through startup. -/
theorem no_sign_crossing (t : ℝ) (ht : 0 ≤ t) (hD : t ≤ 1/2000) :
    (-143/3200:ℝ)+(813/20000)*t < 0 ∧
    (-559/16000:ℝ)+(7313/20000)*t < 0 ∧
    0 < (117/3200:ℝ)-(24433/20000)*t := by
  constructor
  · linarith
  constructor <;> linarith

theorem startup_margin : (443/8000:ℝ)+(3/20000)=2221/40000 := by norm_num

end C11Inventor
#print axioms C11Inventor.third_facet_inward
#print axioms C11Inventor.third_facet_lower
#print axioms C11Inventor.other_facets_positive
#print axioms C11Inventor.no_sign_crossing
#print axioms C11Inventor.startup_margin

namespace C11Inventor

theorem pending_feedback_range (v a r d : ℝ)
    (hvl : 367/20000 ≤ v) (hvh : v ≤ 813/20000)
    (hal : 0 ≤ a) (hah : a ≤ 13/10)
    (hrl : 8 ≤ r) (hrh : r ≤ 12)
    (hdl : -1/100 ≤ d) (hdh : d ≤ 1/100) :
    4687/2500 ≤ -8*v-6*a-r*(-121/100+d-a)/2 ∧
    -8*v-6*a-r*(-121/100+d-a)/2 ≤ 17933/2500 := by
  have p : 0 ≤ (r-8)*(a+6/5) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(1/100-d) := mul_nonneg (by linarith) (by linarith)
  have s : 0 ≤ (12-r)*(a+61/50) := mul_nonneg (by linarith) (by linarith)
  have t : 0 ≤ r*(d+1/100) := mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith

theorem initial_facet_box (x mx v mv a ma : ℝ)
    (hvl : 29/1000 ≤ mv) (hvh : mv ≤ 3/100)
    (hal : 123/100 ≤ ma) (hah : ma ≤ 31/25)
    (hxl : -1/1000 ≤ x-mx) (hxh : x-mx ≤ 1/1000)
    (hel : -1/100 ≤ v-mv) (heh : v-mv ≤ 1/100)
    (hfl : -1/20 ≤ a-ma) (hfh : a-ma ≤ 1/20) :
    (-189/4000 ≤ x-mx-mv/4-ma/32 ∧ x-mx-mv/4-ma/32 ≤ -143/3200) ∧
    (-169/4000 ≤ x-mx-mv/4-ma/32+v/4 ∧ x-mx-mv/4-ma/32+v/4 ≤ -559/16000) ∧
    (117/3200 ≤ x-mx-mv/4-ma/32+v/2+a/16 ∧
       x-mx-mv/4-ma/32+v/2+a/16 ≤ 443/8000) := by
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

end C11Inventor
#print axioms C11Inventor.pending_feedback_range
#print axioms C11Inventor.initial_facet_box
