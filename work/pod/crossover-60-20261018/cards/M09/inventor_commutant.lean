import Mathlib.Tactic

namespace M09Inventor

/-- Abstract matrix-algebra identity; `ua` is the adjoint in applications. -/
theorem preserves_product {R : Type*} [Ring R] (ua k u w : R)
    (metric : ua*k*u = k) (commutes : w*u = u*w) :
    ua*(k*w)*u = k*w := by
  calc
    ua*(k*w)*u = (ua*k)*(w*u) := by noncomm_ring
    _ = (ua*k)*(u*w) := by rw [commutes]
    _ = (ua*k*u)*w := by noncomm_ring
    _ = k*w := by rw [metric]

/-- Jointly preserving a metric and an operator fixes their affine product form. -/
theorem preserves_affine {R : Type*} [Ring R] (ua k u w : R)
    (metric : ua*k*u = k) (commutes : w*u = u*w) :
    ua*(k+k*w)*u = k+k*w := by
  calc
    ua*(k+k*w)*u = ua*k*u + ua*(k*w)*u := by noncomm_ring
    _ = k+k*w := by rw [metric, preserves_product ua k u w metric commutes]

/-- A real scalar multiplier that commutes with u can be included in the fixed operator. -/
theorem product_commutes {R : Type*} [Ring R] (c w u : R)
    (hc : c*u = u*c) (hw : w*u = u*w) :
    (c*w)*u = u*(c*w) := by
  calc
    (c*w)*u = c*(w*u) := by noncomm_ring
    _ = c*(u*w) := by rw [hw]
    _ = (c*u)*w := by noncomm_ring
    _ = (u*c)*w := by rw [hc]
    _ = u*(c*w) := by noncomm_ring

end M09Inventor
#print axioms M09Inventor.preserves_product
#print axioms M09Inventor.preserves_affine
#print axioms M09Inventor.product_commutes
