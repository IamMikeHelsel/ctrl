-- Adapted from inventor_facets; broader coupled guard, distinct bounds.
import Mathlib.Tactic
namespace C11Polygon

/-- Actual pending-command drift in the third C3 tilted coordinate. -/
theorem third_facet_inward (v a r d : ℝ)
    (hv : v ≤ 1769/10000) (ha : 0 ≤ a)
    (hr : 8 ≤ r) (hd : d ≤ 1/100) :
    v+a/2+r*(-121/100+d-a)/16 ≤ -4231/10000 := by
  have p : 0 ≤ (r-8)*(a+6/5) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(1/100-d) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem third_facet_lower (v a r d : ℝ)
    (hv : 187/20000 ≤ v) (hal : 0 ≤ a) (hah : a ≤ 13/10)
    (hrl : 0 ≤ r) (hrh : r ≤ 12) (hd : -1/100 ≤ d) :
    -24613/20000 ≤ v+a/2+r*(-121/100+d-a)/16 := by
  have p : 0 ≤ (12-r)*(a+61/50) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(d+1/100) := mul_nonneg hrl (by linarith)
  nlinarith

theorem other_facets_positive (v a : ℝ)
    (hv : 187/20000 ≤ v) (ha : 1061/12500 ≤ a) :
    0 < v ∧ 0 < v+a/4 := by constructor <;> linarith

/-- Exact opposite-side barriers for the three sign-monotone facets through startup. -/
theorem no_sign_crossing (t : ℝ) (ht : 0 ≤ t) (hD : t ≤ 1/2000) :
    (-139/16000:ℝ)+(1769/10000)*t < 0 ∧
    (-19/16000:ℝ)+(5019/10000)*t < 0 ∧
    -(2221/40000:ℝ) < (9/16000:ℝ)-(24613/20000)*t := by
  constructor
  · linarith
  constructor <;> linarith


end C11Polygon
#print axioms C11Polygon.third_facet_inward
#print axioms C11Polygon.third_facet_lower
#print axioms C11Polygon.other_facets_positive
#print axioms C11Polygon.no_sign_crossing

namespace C11Polygon

theorem pending_feedback_range (v a r d : ℝ)
    (hvl : 187/20000 ≤ v) (hvh : v ≤ 1769/10000)
    (hal : 0 ≤ a) (hah : a ≤ 13/10)
    (hrl : 8 ≤ r) (hrh : r ≤ 12)
    (hdl : -1/100 ≤ d) (hdh : d ≤ 1/100) :
    981/1250 ≤ -8*v-6*a-r*(-121/100+d-a)/2 ∧
    -8*v-6*a-r*(-121/100+d-a)/2 ≤ 18113/2500 := by
  have p : 0 ≤ (r-8)*(a+6/5) := mul_nonneg (by linarith) (by linarith)
  have q : 0 ≤ r*(1/100-d) := mul_nonneg (by linarith) (by linarith)
  have s : 0 ≤ (12-r)*(a+61/50) := mul_nonneg (by linarith) (by linarith)
  have t : 0 ≤ r*(d+1/100) := mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith

theorem initial_facet_box (x mx v mv a ma : ℝ)
    (hvl : 1/50 ≤ mv) (hcap : 8*mv+ma ≤ 37/25)
    (hal : 3/20 ≤ ma) (hah : ma ≤ 5/4)
    (hxl : -1/1000 ≤ x-mx) (hxh : x-mx ≤ 1/1000)
    (hel : -1/100 ≤ v-mv) (heh : v-mv ≤ 1/100)
    (hfl : -1/20 ≤ a-ma) (hfh : a-ma ≤ 1/20) :
    (-189/4000 ≤ x-mx-mv/4-ma/32 ∧ x-mx-mv/4-ma/32 ≤ -139/16000) ∧
    (-681/16000 ≤ x-mx-mv/4-ma/32+v/4 ∧ x-mx-mv/4-ma/32+v/4 ≤ -19/16000) ∧
    (9/16000 ≤ x-mx-mv/4-ma/32+v/2+a/16 ∧
       x-mx-mv/4-ma/32+v/2+a/16 ≤ 443/8000) := by
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

end C11Polygon
#print axioms C11Polygon.pending_feedback_range
#print axioms C11Polygon.initial_facet_box
