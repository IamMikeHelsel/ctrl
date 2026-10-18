import QuadraticTwist
import SpinEquivariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace GUGeneralBoost
open GUClifford HyperbolicSpinor GUQuadraticTwist

def element (x y : ℝ) : Cl := x • (1 : Cl) + y • chirality

def inverse (x y : ℝ) : Cl :=
  ((x*x-y*y)⁻¹) • (x • (1 : Cl) - y • chirality)

theorem right_inverse (x y : ℝ) (h : x*x-y*y ≠ 0) :
    element x y * inverse x y = 1 := by
  calc
    _ = ((x*x-y*y)⁻¹ * (x*x-y*y)) • (1 : Cl) := by
      simp only [element, inverse, mul_smul_comm, mul_sub, add_mul,
        smul_mul_assoc, mul_smul_comm, one_mul, mul_one, chirality_square]
      module
    _ = 1 := by simp [h]

theorem left_inverse (x y : ℝ) (h : x*x-y*y ≠ 0) :
    inverse x y * element x y = 1 := by
  calc
    _ = ((x*x-y*y)⁻¹ * (x*x-y*y)) • (1 : Cl) := by
      simp only [element, inverse, smul_mul_assoc, sub_mul, mul_add,
        smul_mul_assoc, mul_smul_comm, one_mul, mul_one, chirality_square]
      module
    _ = 1 := by simp [h]

def unit (x y : ℝ) (h : x*x-y*y ≠ 0) : Clˣ where
  val := element x y
  inv := inverse x y
  val_inv := right_inverse x y h
  inv_val := left_inverse x y h

theorem conjugation_formula (x y : ℝ) (v : V) :
    element x y * CliffordAlgebra.ι Q v * inverse x y =
      ((x*x+y*y)/(x*x-y*y)) • CliffordAlgebra.ι Q v +
      ((2*x*y)/(x*x-y*y)) • (chirality * CliffordAlgebra.ι Q v) := by
  have ha : CliffordAlgebra.ι Q v * chirality = -(chirality * CliffordAlgebra.ι Q v) := by
    rw [chirality_anticommutes_vector v, neg_neg]
  have ht : chirality * CliffordAlgebra.ι Q v * chirality = -CliffordAlgebra.ι Q v := by
    rw [mul_assoc, ha, mul_neg, ← mul_assoc, chirality_square, one_mul]
  simp only [element, inverse, mul_smul_comm, mul_sub, add_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ht, ha, div_eq_mul_inv]
  module

theorem element_commutes_spin (x y : ℝ) (s : Cl) (hs : s ∈ spinGroup Q) :
    element x y * s = s * element x y := by
  simp only [element, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, chirality_commutes_spin s hs]

theorem normalized_denominator (a b : ℝ) (h : a*a-b*b=1) :
    (a+1)*(a+1)-b*b = 2*(a+1) := by nlinarith

theorem normalized_denominator_nonzero (a b : ℝ) (h : a*a-b*b=1) (ha : a ≠ -1) :
    (a+1)*(a+1)-b*b ≠ 0 := by
  rw [normalized_denominator a b h]
  exact mul_ne_zero (by norm_num) (by intro hh; apply ha; linarith)

theorem normalized_conjugation (a b : ℝ) (h : a*a-b*b=1) (ha : a ≠ -1) (v : V) :
    element (a+1) b * CliffordAlgebra.ι Q v * inverse (a+1) b = twistedVector a b v := by
  have han : a+1 ≠ 0 := by intro hh; apply ha; linarith
  have hca : ((a+1)*(a+1)+b*b)/((a+1)*(a+1)-b*b) = a := by
    rw [normalized_denominator a b h]
    apply (div_eq_iff (mul_ne_zero (by norm_num) han)).mpr
    nlinarith
  have hcb : (2*(a+1)*b)/((a+1)*(a+1)-b*b) = b := by
    rw [normalized_denominator a b h]
    apply (div_eq_iff (mul_ne_zero (by norm_num) han)).mpr
    ring
  rw [conjugation_formula, hca, hcb]
  rfl

/-- The exceptional hyperbola point is implemented by the full volume itself. -/
def volumeUnit : Clˣ where
  val := chirality
  inv := chirality
  val_inv := chirality_square
  inv_val := chirality_square

theorem exceptional_conjugation (b : ℝ) (h : (-1 : ℝ)*(-1)-b*b=1) (v : V) :
    chirality * CliffordAlgebra.ι Q v * chirality = twistedVector (-1) b v := by
  have hb : b=0 := by nlinarith [sq_nonneg b]
  subst b
  have ha : CliffordAlgebra.ι Q v * chirality = -(chirality * CliffordAlgebra.ι Q v) := by
    rw [chirality_anticommutes_vector v, neg_neg]
  rw [mul_assoc, ha, mul_neg, ← mul_assoc, chirality_square, one_mul]
  simp [twistedVector]

/-- Complete inner-equivalence result for this two-parameter normalized family.
This does not classify all invariant tensors or all Clifford representations. -/
theorem normalized_family_inner (a b : ℝ) (h : a*a-b*b=1) :
    ∃ u : Clˣ,
      (∀ v : V, (u : Cl) * CliffordAlgebra.ι Q v * (↑(u⁻¹) : Cl) = twistedVector a b v) ∧
      (∀ s : Cl, s ∈ spinGroup Q → (u : Cl) * s = s * (u : Cl)) := by
  by_cases ha : a = -1
  · subst a
    refine ⟨volumeUnit, ?_, ?_⟩
    · intro v
      exact exceptional_conjugation b h v
    · intro s hs
      exact chirality_commutes_spin s hs
  · refine ⟨unit (a+1) b (normalized_denominator_nonzero a b h ha), ?_, ?_⟩
    · intro v
      exact normalized_conjugation a b h ha v
    · intro s hs
      exact element_commutes_spin (a+1) b s hs

#print axioms GUGeneralBoost.normalized_family_inner
#print axioms GUGeneralBoost.conjugation_formula
end GUGeneralBoost
