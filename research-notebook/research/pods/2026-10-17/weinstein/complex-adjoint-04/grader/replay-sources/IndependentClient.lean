import AdjointControls
import ComplexContraction
import CliffordControls

noncomputable section
open scoped TensorProduct BigOperators
open GUComplex GUClifford GUContraction
namespace IndependentAdjointReview

theorem actual_tensor_algebra : CCl = (ℂ ⊗[ℝ] CliffordAlgebra Q) := rfl

theorem faithful_real_inclusion (a b : Cl) : embed a = embed b ↔ a = b :=
  embed_injective.eq_iff

theorem conjugate_tensor_law (z : ℂ) (a : Cl) :
    bar (z ⊗ₜ[ℝ] a) = star z ⊗ₜ[ℝ] star a := bar_tmul z a

theorem literal_commutator_closure (a b : CCl)
    (ha : bar a = -a) (hb : bar b = -b) :
    bar (a*b-b*a) = -(a*b-b*a) := commutator_skew a b ha hb

theorem literal_jordan_closure (a b : CCl)
    (ha : bar a = -a) (hb : bar b = -b) :
    bar (Complex.I • (a*b+b*a)) = -(Complex.I • (a*b+b*a)) :=
  iAnti_skew a b ha hb

theorem faithful_fourform_defect : complexK fourform ≠ 0 := by
  rw [complexK_embed]
  intro h
  apply fourform_K_ne_zero
  apply embed_injective
  simpa only [map_zero] using h

theorem complex_sectional_value : complexK sectional = algebraMap ℝ CCl (-2) := by
  rw [complex_clifford_contraction sectional sectional_curvature, sectional_scalar]

theorem literal_complex_curvature (R : Tensor) (h : Curvature R) :
    (∑ p ∈ (Finset.univ.filter (fun p : Ix × Ix => p.1 < p.2)),
      ∑ q ∈ (Finset.univ.filter (fun q : Ix × Ix => q.1 < q.2)),
        (eps p.1 * eps p.2 * eps q.1 * eps q.2 * R p.1 p.2 q.1 q.2) •
          (cgamma p.1 * cgamma p.2 * cgamma q.1 * cgamma q.2 +
            cgamma q.1 * cgamma q.2 * cgamma p.1 * cgamma p.2)) =
      algebraMap ℝ (ℂ ⊗[ℝ] CliffordAlgebra Q)
        (-∑ b, eps b * ∑ a, eps a * R a b a b) :=
  complex_clifford_contraction R h

theorem actual_bar_and_fixed_bar_differ :
    bar (iAnti (cgamma 0) (cgamma 0)) ≠ fixedBar (iAnti (cgamma 0) (cgamma 0)) := by
  have hs := iAnti_skew (cgamma 0) (cgamma 0) (gamma_skew 0) (gamma_skew 0)
  change bar (iAnti (cgamma 0) (cgamma 0)) = -iAnti (cgamma 0) (cgamma 0) at hs
  intro heq
  exact fixedBar_iAnti_not_skew (heq.symm.trans hs)

theorem wrong_product_rule_is_false :
    ¬ (∀ a b : CCl, bar (a*b) = bar a * bar b) := by
  intro h
  exact bar_product_wrong_order_false (h (cgamma 0) (cgamma 7))

end IndependentAdjointReview
