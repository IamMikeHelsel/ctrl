import CliffordModel
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

noncomputable section
open scoped TensorProduct
namespace GUComplex
open GUClifford

instance realCliffordStarModule : StarModule ℝ Cl where
  star_smul r a := by simp [CliffordAlgebra.star_smul]

abbrev CCl := ℂ ⊗[ℝ] Cl

def embed : Cl →ₐ[ℝ] CCl := Algebra.TensorProduct.includeRight

theorem embed_injective : Function.Injective embed :=
  Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap ℝ ℂ))

instance complexCliffordNontrivial : Nontrivial CCl :=
  Function.Injective.nontrivial embed_injective

def bar (a : CCl) : CCl := star a

theorem bar_tmul (z : ℂ) (a : Cl) : bar (z ⊗ₜ[ℝ] a) = star z ⊗ₜ[ℝ] star a := rfl

theorem bar_add (a b : CCl) : bar (a+b) = bar a + bar b := star_add a b

theorem bar_sub (a b : CCl) : bar (a-b) = bar a - bar b := star_sub a b

theorem bar_mul (a b : CCl) : bar (a*b) = bar a * bar b := star_mul a b

theorem bar_involutive (a : CCl) : bar (bar a) = a := star_star a

theorem bar_scalar (z : ℂ) : bar (algebraMap ℂ CCl z) = algebraMap ℂ CCl (star z) := by
  simp [bar, Algebra.TensorProduct.algebraMap_apply]

theorem bar_smul (z : ℂ) (a : CCl) : bar (z • a) = star z • bar a := by
  rw [Algebra.smul_def z a, bar_mul, bar_scalar, Algebra.smul_def (star z) (bar a)]
  exact (Algebra.commutes (star z) (bar a)).symm

theorem bar_I_smul (a : CCl) : bar (Complex.I • a) = -Complex.I • bar a := by
  rw [bar_smul]
  simp

theorem bar_embed (a : Cl) : bar (embed a) = embed (star a) := by
  simp [embed, bar]

def cgamma (a : Ix) : CCl := embed (gamma a)

theorem bar_gamma (a : Ix) : bar (cgamma a) = -cgamma a := by
  simp [cgamma, bar_embed, gamma]

def Skew (a : CCl) : Prop := bar a = -a

def commutator (a b : CCl) : CCl := a*b-b*a

def iAnti (a b : CCl) : CCl := Complex.I • (a*b+b*a)

theorem commutator_skew (a b : CCl) (ha : Skew a) (hb : Skew b) :
    Skew (commutator a b) := by
  change bar a = -a at ha
  change bar b = -b at hb
  unfold Skew commutator
  rw [bar_sub, bar_mul, bar_mul, ha, hb]
  rw [neg_mul_neg b a, neg_mul_neg a b]
  abel

theorem iAnti_skew (a b : CCl) (ha : Skew a) (hb : Skew b) :
    Skew (iAnti a b) := by
  change bar a = -a at ha
  change bar b = -b at hb
  unfold Skew iAnti
  rw [bar_I_smul, bar_add, bar_mul, bar_mul, ha, hb]
  rw [neg_mul_neg b a, neg_mul_neg a b]
  simp only [neg_smul]
  rw [add_comm]

theorem gamma_skew (a : Ix) : Skew (cgamma a) := bar_gamma a

theorem cgamma_sq (a : Ix) : cgamma a * cgamma a = eps a • (1 : CCl) := by
  simp only [cgamma, ← map_mul, gamma_sq, map_smul, map_one]

theorem cgamma_zero_sq : cgamma 0 * cgamma 0 = 1 := by
  simpa [eps] using cgamma_sq 0

theorem cgamma_seven_sq : cgamma 7 * cgamma 7 = -1 := by
  simpa [eps] using cgamma_sq 7

theorem scalar_injective : Function.Injective (algebraMap ℂ CCl) := RingHom.injective _

end GUComplex
