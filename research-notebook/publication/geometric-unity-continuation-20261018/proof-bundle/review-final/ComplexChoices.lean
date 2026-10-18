import Chirality
import ComplexAdjoint
import VolumeTwist
noncomputable section
namespace HyperbolicSpinor
open GUClifford GUComplex

instance complexChoicesStarModule : StarModule ℂ CCl where
  star_smul z a := bar_smul z a

/-- Alternating Clifford inclusion, before descent through exterior power. -/
def bivector (v w : V) : Cl :=
  (1/2 : ℝ) • (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w -
    CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v)

theorem bivector_star (v w : V) : star (bivector v w) = -bivector v w := by
  simp only [bivector, CliffordAlgebra.star_smul, star_sub, star_mul,
    CliffordAlgebra.star_ι, neg_mul_neg, smul_sub]
  abel

theorem chirality_commutes_bivector_map (v w : V) :
    chirality * bivector v w = bivector v w * chirality := by
  simp only [bivector, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    chirality_commutes_bivector]

def complexVolume : CCl := embed chirality

def imaginaryVolume : CCl := Complex.I • complexVolume

theorem complexVolume_square : complexVolume * complexVolume = 1 := by
  rw [complexVolume, ← map_mul, chirality_square, map_one]

theorem complexVolume_bar : bar complexVolume = -complexVolume := by
  rw [complexVolume, bar_embed, chirality_star, map_neg]

theorem imaginaryVolume_square : imaginaryVolume * imaginaryVolume = -1 := by
  simp only [imaginaryVolume, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, complexVolume_square, neg_smul, one_smul]

theorem imaginaryVolume_not_real_scalar (r : ℝ) :
    imaginaryVolume ≠ algebraMap ℝ CCl r := by
  intro h
  have hs := imaginaryVolume_square
  rw [h, ← map_mul] at hs
  have hn : algebraMap ℝ CCl (r*r) = algebraMap ℝ CCl (-1) := by simpa only [map_neg, map_one] using hs
  have hr := (RingHom.injective (algebraMap ℝ CCl)) hn
  nlinarith [sq_nonneg r]

def bivectorChoice (p : V × V) : CCl := embed (bivector p.1 p.2)
def twistedBivectorChoice (p : V × V) : CCl := imaginaryVolume * bivectorChoice p

theorem bivectorChoice_skew (p : V × V) : Skew (bivectorChoice p) := by
  dsimp [Skew, bivectorChoice]
  rw [bar_embed, bivector_star, map_neg]

theorem twistedBivectorChoice_skew (p : V × V) : Skew (twistedBivectorChoice p) := by
  have hc : complexVolume * bivectorChoice p = bivectorChoice p * complexVolume := by
    dsimp [complexVolume, bivectorChoice]
    rw [← map_mul, ← map_mul, chirality_commutes_bivector_map]
  change bar ((Complex.I • complexVolume) * bivectorChoice p) =
    -((Complex.I • complexVolume) * bivectorChoice p)
  rw [smul_mul_assoc]
  exact GUVolumeTwist.imaginary_twist_skew complexVolume (bivectorChoice p)
    complexVolume_bar (bivectorChoice_skew p) hc

theorem bivector_basis01 : bivector (e 0) (e 1) = gamma 0 * gamma 1 := by
  change (1/2 : ℝ) • (gamma 0*gamma 1-gamma 1*gamma 0) = _
  rw [gamma_swap 1 0 (by decide), sub_neg_eq_add]
  have ht : gamma 0 * gamma 1 + gamma 0 * gamma 1 = (2 : ℝ) • (gamma 0 * gamma 1) := by
    rw [two_smul]
  rw [ht, smul_smul]
  norm_num

def bivectorUnit : CClˣ where
  val := embed (gamma 0 * gamma 1)
  inv := embed (gamma 1 * gamma 0)
  val_inv := by
    rw [← map_mul]
    have h0 : gamma 0*gamma 0 = (1 : Cl) := by norm_num [gamma_sq, eps]
    have h1 : gamma 1*gamma 1 = (1 : Cl) := by norm_num [gamma_sq, eps]
    simp only [mul_assoc, ← mul_assoc (gamma 1) (gamma 1), h1, one_mul, h0, map_one]
  inv_val := by
    rw [← map_mul]
    have h0 : gamma 0*gamma 0 = (1 : Cl) := by norm_num [gamma_sq, eps]
    have h1 : gamma 1*gamma 1 = (1 : Cl) := by norm_num [gamma_sq, eps]
    simp only [mul_assoc, ← mul_assoc (gamma 0) (gamma 0), h0, one_mul, h1, map_one]

theorem bivector_pair_independent :
    ∀ a b : ℝ, a • bivectorChoice + b • twistedBivectorChoice = 0 → a=0 ∧ b=0 := by
  apply GUVolumeTwist.function_independence_of_evaluation _ _ (e 0, e 1)
  have hi := GUVolumeTwist.independent_unit_twist imaginaryVolume bivectorUnit
    imaginaryVolume_not_real_scalar
  simpa only [bivectorChoice, twistedBivectorChoice, bivector_basis01, bivectorUnit] using hi

end HyperbolicSpinor
