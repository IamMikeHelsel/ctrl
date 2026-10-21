import Mathlib.Tactic
namespace M08Beta
/-- dr denotes one divergence component of Ricci; ds the matching scalar
curvature derivative. The geometric contracted Bianchi premise is explicit. -/
theorem contracted_bianchi_coefficient (β dr ds : ℝ) (h : 2*dr=ds) :
    2*dr-β*ds=(1-β)*ds := by nlinarith

theorem nonconstant_gradient_selects (β dr ds : ℝ) (h : 2*dr=ds) (hn : ds≠0) :
    2*dr-β*ds=0 ↔ β=1 := by
  rw [contracted_bianchi_coefficient β dr ds h]
  constructor
  · intro he
    rcases mul_eq_zero.mp he with hh | hh
    · linarith
    · exact False.elim (hn hh)
  · intro he
    simp [he]

theorem all_gradients_select (β : ℝ) :
    (∀ dr ds : ℝ, 2*dr=ds → 2*dr-β*ds=0) ↔ β=1 := by
  constructor
  · intro h
    have hh := h (1/2) 1 (by norm_num)
    linarith
  · intro h dr ds hb
    rw [h]
    linarith

theorem constant_scalar_cannot_select (β : ℝ) : 2*(0:ℝ)-β*0=0 := by ring

theorem dimension14_trace (β scal : ℝ) : 2*scal-14*β*scal=(2-14*β)*scal := by ring

/-- A pointwise constant-sectional-curvature algebraic tensor field with K=x0
has dr=13, ds=182. These violate differential contracted Bianchi; it must not
be substituted into the preceding geometric premise. -/
theorem algebraic_affine_field_is_not_differential :
    2*(13:ℝ)≠182 ∧ (2*(13:ℝ)-(1/7)*182=0) ∧ (2*(13:ℝ)-1*182≠0) := by norm_num

#print axioms contracted_bianchi_coefficient
#print axioms nonconstant_gradient_selects
#print axioms all_gradients_select
#print axioms constant_scalar_cannot_select
#print axioms dimension14_trace
#print axioms algebraic_affine_field_is_not_differential
end M08Beta
