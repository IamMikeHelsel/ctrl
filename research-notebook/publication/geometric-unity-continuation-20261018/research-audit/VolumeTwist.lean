import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Pi

/-! Conditional algebra used by the invariant-choice hand proof. This file does
not define the Spin group, invariant tensors, or the concrete full volume. -/
namespace GUVolumeTwist

section StarAlgebra
variable {A : Type*} [Ring A] [StarRing A]

/-- A pair of skew elements with opposite product orders has skew product. -/
theorem skew_twist_of_anticommute (w v : A)
    (hw : star w = -w) (hv : star v = -v)
    (hanti : w * v = -(v * w)) : star (w * v) = -(w * v) := by
  rw [star_mul, hv, hw, neg_mul_neg]
  rw [hanti, neg_neg]

/-- A pair of commuting skew elements has self-adjoint product. -/
theorem selfadjoint_twist_of_commute (w b : A)
    (hw : star w = -w) (hb : star b = -b)
    (hcomm : w * b = b * w) : star (w * b) = w * b := by
  rw [star_mul, hb, hw, neg_mul_neg, ← hcomm]

omit [StarRing A] in
/-- Equivariance of left multiplication by w under a specified unit conjugation.
Commutation with the chosen unit is an explicit premise. -/
theorem conjugate_twist (s : Aˣ) (w x : A)
    (hs : (s : A) * w = w * (s : A)) :
    (s : A) * (w * x) * (↑(s⁻¹) : A) =
      w * ((s : A) * x * (↑(s⁻¹) : A)) := by
  calc
    _ = ((s : A) * w) * x * (↑(s⁻¹) : A) := by simp only [mul_assoc]
    _ = _ := by rw [hs]; simp only [mul_assoc]

end StarAlgebra

section ComplexStarAlgebra
variable {A : Type*} [Ring A] [StarRing A]
    [Module ℂ A] [StarModule ℂ A]

/-- The factor i is essential: it converts the self-adjoint even twist to skew. -/
theorem imaginary_twist_skew (w b : A)
    (hw : star w = -w) (hb : star b = -b)
    (hcomm : w * b = b * w) :
    star (Complex.I • (w * b)) = -(Complex.I • (w * b)) := by
  rw [star_smul, selfadjoint_twist_of_commute w b hw hb hcomm]
  simp

end ComplexStarAlgebra

section IndependentChoices
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Two independent vectors give an injective affine family of choices.
The explicit independence premise keeps the theorem separate from a future
proof of independence of actual GU invariant tensors. -/
theorem independent_affine_family_injective (x y : M)
    (h : ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0) :
    Function.Injective (fun t : K => x + t • y) := by
  intro a b hab
  have hs : a • y = b • y := add_left_cancel hab
  have hz : (a-b) • y = 0 := by rw [sub_smul, hs, sub_self]
  have hi := h 0 (a-b) (by simpa using hz)
  exact sub_eq_zero.mp hi.2

/-- A chosen independent pair is distinct. -/
theorem independent_choices_distinct (x y : M)
    (h : ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0) : x ≠ y := by
  intro he
  have hz : (1 : K) • x + (-1 : K) • y = 0 := by simp [he]
  exact one_ne_zero (h 1 (-1) hz).1

/-- Independence at one input suffices to certify independence of two maps. -/
theorem function_independence_of_evaluation {V : Type*} (F G : V → M) (v : V)
    (h : ∀ a b : K, a • F v + b • G v = 0 → a = 0 ∧ b = 0) :
    ∀ a b : K, a • F + b • G = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  exact h a b (congrFun hab v)

end IndependentChoices

section NonScalarTwist
variable {K A : Type*} [Field K] [Ring A] [Nontrivial A] [Algebra K A]

/-- A non-scalar multiplier gives two independent choices at any invertible input.
No Clifford classification, group action, or PBW theorem is assumed here. -/
theorem independent_unit_twist (w : A) (u : Aˣ)
    (hnot : ∀ r : K, w ≠ algebraMap K A r) :
    ∀ a b : K, a • (u : A) + b • (w * (u : A)) = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have hz : a • (1 : A) + b • w = 0 := by
    have hh := congrArg (fun t : A => t * (↑(u⁻¹) : A)) hab
    simpa only [add_mul, smul_mul_assoc, mul_assoc, Units.val_inv_eq_inv_val,
      Units.mul_inv, mul_one, zero_mul] using hh
  have hb : b = 0 := by
    by_contra hb
    have hw : b • w = -(a • (1 : A)) := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hz)
    have he : w = algebraMap K A (-a / b) := by
      calc
        w = (b⁻¹ * b) • w := by simp [hb]
        _ = b⁻¹ • (b • w) := by rw [mul_smul]
        _ = b⁻¹ • (-(a • (1 : A))) := by rw [hw]
        _ = algebraMap K A (-a / b) := by
          simp [Algebra.algebraMap_eq_smul_one, smul_smul, div_eq_mul_inv, mul_comm]
    exact hnot (-a / b) he
  subst b
  have ha : a • (1 : A) = 0 := by simpa using hz
  exact ⟨(smul_eq_zero.mp ha).resolve_right one_ne_zero, rfl⟩

end NonScalarTwist

#print axioms GUVolumeTwist.independent_unit_twist
#print axioms GUVolumeTwist.skew_twist_of_anticommute
#print axioms GUVolumeTwist.selfadjoint_twist_of_commute
#print axioms GUVolumeTwist.conjugate_twist
#print axioms GUVolumeTwist.imaginary_twist_skew
#print axioms GUVolumeTwist.independent_affine_family_injective
#print axioms GUVolumeTwist.independent_choices_distinct
#print axioms GUVolumeTwist.function_independence_of_evaluation
end GUVolumeTwist
