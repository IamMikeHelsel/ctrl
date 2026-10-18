import VolumeTwistActual
import Mathlib.Tactic.Module

noncomputable section
namespace GUQuadraticTwist
open GUClifford HyperbolicSpinor

/-- Actual two-parameter vector map. Neither parameter is silently normalized. -/
def twistedVector (a b : ℝ) (v : V) : Cl :=
  a • CliffordAlgebra.ι Q v + b • (chirality * CliffordAlgebra.ι Q v)

theorem chirality_twisted_square (v : V) :
    (chirality * CliffordAlgebra.ι Q v) * (chirality * CliffordAlgebra.ι Q v) =
    -(CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by
  let x := CliffordAlgebra.ι Q v
  have ha : x * chirality = -(chirality * x) := by
    rw [chirality_anticommutes_vector v, neg_neg]
  change (chirality * x) * (chirality * x) = -(x*x)
  calc
    _ = chirality * (x * chirality) * x := by simp only [mul_assoc]
    _ = chirality * (-(chirality*x)) * x := by rw [ha]
    _ = -(x*x) := by simp only [mul_neg, neg_mul, ← mul_assoc, chirality_square, one_mul]

theorem twistedVector_square (a b : ℝ) (v : V) :
    twistedVector a b v * twistedVector a b v =
      (a*a-b*b) • (Q v • (1 : Cl)) := by
  let x := CliffordAlgebra.ι Q v
  have ha : x * chirality = -(chirality * x) := by
    rw [chirality_anticommutes_vector v, neg_neg]
  have hm : x * (chirality*x) = -(chirality * (x*x)) := by
    rw [← mul_assoc, ha, neg_mul, mul_assoc]
  have ht : (chirality*x)*(chirality*x) = -(x*x) := chirality_twisted_square v
  have hs : x*x = Q v • (1 : Cl) := by
    simp [x, Algebra.algebraMap_eq_smul_one]
  change (a • x + b • (chirality*x)) * (a • x + b • (chirality*x)) = _
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hm, ht]
  simp only [smul_neg, mul_assoc]
  rw [hs]
  module

theorem normalized_twistedVector_square (a b : ℝ) (h : a*a-b*b=1) (v : V) :
    twistedVector a b v * twistedVector a b v = Q v • (1 : Cl) := by
  rw [twistedVector_square, h, one_smul]

theorem rational_choice_normalized :
    (5/3 : ℝ)*(5/3)-(4/3)*(4/3)=1 := by norm_num

theorem rational_twistedVector_square (v : V) :
    twistedVector (5/3) (4/3) v * twistedVector (5/3) (4/3) v = Q v • (1 : Cl) :=
  normalized_twistedVector_square _ _ rational_choice_normalized v

/-- The exact normalization condition is a hyperbola, not a single point. -/
theorem twistedVector_preserves_square_iff (a b : ℝ) :
    (∀ v : V, twistedVector a b v * twistedVector a b v = Q v • (1 : Cl)) ↔
      a*a-b*b=1 := by
  constructor
  · intro h
    have he := h (e 0)
    rw [twistedVector_square, Q_e] at he
    simp only [eps, Fin.val_zero, Nat.ofNat_pos, ↓reduceIte, one_smul] at he
    apply (RingHom.injective (algebraMap ℝ Cl))
    simpa [Algebra.algebraMap_eq_smul_one] using he
  · intro h v
    exact normalized_twistedVector_square a b h v

/-- The actual vector map is real-linear. -/
def twistedLinear (a b : ℝ) : V →ₗ[ℝ] Cl where
  toFun := twistedVector a b
  map_add' v w := by simp [twistedVector, mul_add, smul_add, add_add_add_comm]
  map_smul' t v := by simp [twistedVector, smul_add, smul_smul, mul_comm]

/-- A normalized choice gives an actual Clifford algebra endomorphism. -/
def twistedLift (a b : ℝ) (h : a*a-b*b=1) : Cl →ₐ[ℝ] Cl :=
  CliffordAlgebra.lift Q ⟨twistedLinear a b, fun v => by
    change twistedVector a b v * twistedVector a b v = algebraMap ℝ Cl (Q v)
    simpa [Algebra.algebraMap_eq_smul_one] using normalized_twistedVector_square a b h v⟩

theorem twistedLift_on_vector (a b : ℝ) (h : a*a-b*b=1) (v : V) :
    twistedLift a b h (CliffordAlgebra.ι Q v) = twistedVector a b v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- The rational normalized choice is not the original vector inclusion. -/
theorem rational_twist_nontrivial :
    twistedVector (5/3) (4/3) (e 0) ≠ gamma 0 := by
  intro h
  have hr : ((5/3 : ℝ)-1) • gamma 0 + (4/3 : ℝ) • (chirality * gamma 0) = 0 := by
    calc
      _ = twistedVector (5/3) (4/3) (e 0) - gamma 0 := by
        unfold twistedVector gamma
        module
      _ = 0 := sub_eq_zero.mpr h
  have hb := (GUVolumeTwistActual.actual_vector_pair_independent _ _ hr).2
  norm_num at hb

#print axioms GUQuadraticTwist.twistedVector_preserves_square_iff
#print axioms GUQuadraticTwist.twistedLift
#print axioms GUQuadraticTwist.rational_twist_nontrivial
#print axioms GUQuadraticTwist.twistedVector_square
#print axioms GUQuadraticTwist.rational_twistedVector_square
end GUQuadraticTwist
