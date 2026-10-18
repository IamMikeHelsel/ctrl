import CliffordControls

noncomputable section
open scoped BigOperators
open GUClifford GUContraction

namespace IndependentReview

-- Expose the main statement without using K as an opaque specification.
theorem literal_sorted_target (R : Tensor) (h : Curvature R) :
    (∑ p ∈ (Finset.univ.filter (fun p : Ix × Ix => p.1 < p.2)),
      ∑ q ∈ (Finset.univ.filter (fun q : Ix × Ix => q.1 < q.2)),
        (eps p.1 * eps p.2 * eps q.1 * eps q.2 * R p.1 p.2 q.1 q.2) •
          (gamma p.1 * gamma p.2 * gamma q.1 * gamma q.2 +
            gamma q.1 * gamma q.2 * gamma p.1 * gamma p.2)) =
        algebraMap ℝ (CliffordAlgebra Q) (-∑ b, eps b * ∑ a, eps a * R a b a b) :=
  actual_clifford_contraction R h

theorem literal_all_index_bridge (R : Tensor) (h : PairSymmetries R) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      (eps a * eps b * eps c * eps d * R a b c d) •
        (gamma a * gamma b * gamma c * gamma d)) = (2 : ℝ) • K R :=
  actual_normalization_bridge R h

def mixedSection : Tensor := fun a b c d => delta 0 7 a b * delta 0 7 c d

theorem mixed_curvature : Curvature mixedSection := by
  constructor
  · constructor <;> intros <;> unfold mixedSection delta <;> ring
  · intros; unfold mixedSection delta; ring

theorem mixed_scalar : scal mixedSection = -2 := by
  norm_num [scal, Ric, mixedSection, delta, eta, eps, mul_sub, sub_mul,
    mul_ite, ite_mul, Finset.sum_sub_distrib, Finset.sum_ite_irrel]

theorem mixed_K : K mixedSection = algebraMap ℝ Cl 2 := by
  rw [actual_clifford_contraction mixedSection mixed_curvature, mixed_scalar]
  norm_num

-- The metric signs are checked in the actual algebra, not merely in R.
theorem negative_generator_square : gamma 7 * gamma 7 = (-1 : Cl) := by
  rw [gamma_sq]
  norm_num [eps]

theorem mixed_blade_square :
    (gamma 0 * gamma 7) * (gamma 0 * gamma 7) = (1 : Cl) := by
  norm_num [mul_assoc, gamma_move 7 0 (by decide), gamma_square_move, gamma_sq, eps]

theorem exact_non_bianchi_control :
    PairSymmetries fourform ∧
    (∀ b d, Ric fourform b d = 0) ∧
    (fourform 0 1 2 3 - fourform 0 2 1 3 + fourform 0 3 1 2 = 3) ∧
    (K fourform = (12 : ℝ) • blade0123) ∧
    (blade0123 * blade0123 = 1) ∧ K fourform ≠ 0 :=
  ⟨fourform_pair, fourform_Ric_zero, fourform_bianchi_residual,
    fourform_K, blade0123_square, fourform_K_ne_zero⟩

theorem wrong_sign_is_mathematically_false :
    ¬ (∀ R : Tensor, Curvature R → K R = algebraMap ℝ Cl (scal R)) := by
  intro h
  exact sectional_false_positive_sign (h sectional sectional_curvature)

end IndependentReview
