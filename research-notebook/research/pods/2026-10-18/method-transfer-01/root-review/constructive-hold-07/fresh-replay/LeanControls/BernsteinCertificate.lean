module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic
public import LeanControls.Discrete

/-!
# Exact interval certificates for matrix-valued polynomials

The certificate producer is untrusted. It supplies an exact reconstruction and
positive-semidefinite coefficient witnesses; Lean checks both hypotheses.
This is a sufficient certificate scheme, not a complete decision procedure.
-/
@[expose] public section
noncomputable section
namespace LeanControls.BernsteinCertificate
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weight (degree k : ℕ) (t : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ degree k).eval t

theorem weight_nonneg (degree k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ weight degree k t := by
  simp only [weight, bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_natCast, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have : 0 ≤ 1 - t := by linarith
  positivity

theorem weight_sum (degree : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (degree + 1), weight degree k t = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval t) (bernsteinPolynomial.sum ℝ degree)
  simpa [weight, Polynomial.eval_finsetSum] using h

/-- LDL witnesses need no square roots or numerical eigenvalue decisions. -/
theorem psd_of_ldl (C L : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hC : C = L * diagonal d * L.transpose) : C.PosSemidef := by
  rw [hC]
  simpa using (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L

def combination (degree : ℕ) (C : ℕ → Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  ∑ k ∈ Finset.range (degree + 1), weight degree k t • C k

omit [Fintype ι] [DecidableEq ι] in
theorem combination_psd (degree : ℕ) (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ k < degree + 1, (C k).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (combination degree C t).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k hk
  exact (hC k (Finset.mem_range.mp hk)).smul (weight_nonneg degree k ht0 ht1)

omit [Fintype ι] [DecidableEq ι] in
/-- Soundness on an arbitrary nondegenerate closed interval. -/
theorem interval_psd (degree : ℕ) (C : ℕ → Matrix ι ι ℝ)
    (Q : ℝ → Matrix ι ι ℝ) {a b : ℝ} (hab : a < b)
    (hC : ∀ k < degree + 1, (C k).PosSemidef)
    (hidentity : ∀ t : ℝ, Q (a + (b - a) * t) = combination degree C t)
    {h : ℝ} (ha : a ≤ h) (hb : h ≤ b) : (Q h).PosSemidef := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have ht0 : 0 ≤ (h - a) / (b - a) := div_nonneg (sub_nonneg.mpr ha) hden.le
  have ht1 : (h - a) / (b - a) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hid : a + (b - a) * ((h - a) / (b - a)) = h := by field_simp; ring
  rw [← hid, hidentity]
  exact combination_psd degree C hC ht0 ht1

omit [Fintype ι] [DecidableEq ι] in
/-- A finite collection of interval certificates can cover a larger domain. -/
theorem covered_psd {κ : Type*} (Q : ℝ → Matrix ι ι ℝ)
    (left right : κ → ℝ) (lo hi : ℝ)
    (hcover : ∀ h, lo ≤ h → h ≤ hi → ∃ k, left k ≤ h ∧ h ≤ right k)
    (hlocal : ∀ k h, left k ≤ h → h ≤ right k → (Q h).PosSemidef)
    {h : ℝ} (hlo : lo ≤ h) (hhi : h ≤ hi) : (Q h).PosSemidef := by
  obtain ⟨k, hk⟩ := hcover h hlo hhi
  exact hlocal k h hk.1 hk.2

def energy (P : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)
def squaredNorm (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

omit [DecidableEq ι] in
theorem energy_mul (P A : Matrix ι ι ℝ) (x : ι → ℝ) :
    energy P (A *ᵥ x) = energy (A.transpose * P * A) x := by
  simp only [energy, Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_mulVec, Matrix.mul_assoc]

/-- Link a matrix inequality to the actual one-step state-energy guarantee. -/
theorem step_decrease (P A : Matrix ι ι ℝ) (h c : ℝ)
    (hcert : (P - A.transpose * P * A - (h * c) • (1 : Matrix ι ι ℝ)).PosSemidef)
    (x : ι → ℝ) : energy P (A *ᵥ x) ≤ energy P x - h * c * squaredNorm x := by
  have hp := hcert.dotProduct_mulVec_nonneg x
  rw [energy_mul]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_trivial] at hp
  have hn : x ⬝ᵥ x = squaredNorm x := by simp [dotProduct, squaredNorm, pow_two]
  rw [hn] at hp
  simp only [smul_eq_mul] at hp
  dsimp [energy]
  linarith

theorem energy_bounds (P : Matrix ι ι ℝ) {lower upper : ℝ}
    (hlo : (P - lower • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hhi : (upper • (1 : Matrix ι ι ℝ) - P).PosSemidef) (x : ι → ℝ) :
    lower * squaredNorm x ≤ energy P x ∧ energy P x ≤ upper * squaredNorm x := by
  have hl := hlo.dotProduct_mulVec_nonneg x
  have hu := hhi.dotProduct_mulVec_nonneg x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_trivial, smul_eq_mul] at hl hu
  have hn : x ⬝ᵥ x = squaredNorm x := by simp [dotProduct, squaredNorm, pow_two]
  rw [hn] at hl hu
  exact ⟨sub_nonneg.mp hl, sub_nonneg.mp hu⟩

theorem contract_of_decrease (P A : Matrix ι ι ℝ) {h c upper : ℝ}
    (h0 : 0 ≤ h) (hc : 0 ≤ c) (hu : 0 < upper)
    (hupper : (upper • (1 : Matrix ι ι ℝ) - P).PosSemidef)
    (hdec : ∀ x, energy P (A *ᵥ x) ≤ energy P x - h * c * squaredNorm x)
    (x : ι → ℝ) : energy P (A *ᵥ x) ≤ (1 - h * c / upper) * energy P x := by
  have hp := hupper.dotProduct_mulVec_nonneg x
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_trivial, smul_eq_mul] at hp
  have hn : x ⬝ᵥ x = squaredNorm x := by simp [dotProduct, squaredNorm, pow_two]
  rw [hn] at hp
  have hm := mul_le_mul_of_nonneg_left (sub_nonneg.mp hp)
    (div_nonneg (mul_nonneg h0 hc) hu.le)
  have hid : (h * c / upper) * (upper * squaredNorm x) = h * c * squaredNorm x := by
    field_simp
  rw [hid] at hm
  dsimp [energy] at *
  nlinarith only [hdec x, hm]

theorem jitter_energy (P : Matrix ι ι ℝ) (A : ℝ → Matrix ι ι ℝ)
    (h : ℕ → ℝ) (x : ℕ → ι → ℝ) {hmin hmax c upper : ℝ}
    (hmin0 : 0 ≤ hmin) (hc : 0 ≤ c) (hu : 0 < upper)
    (hq : 0 ≤ 1 - hmin * c / upper)
    (hP : P.PosSemidef)
    (hupper : (upper • (1 : Matrix ι ι ℝ) - P).PosSemidef)
    (hcert : ∀ t, hmin ≤ t → t ≤ hmax → ∀ z,
      energy P (A t *ᵥ z) ≤ energy P z - t * c * squaredNorm z)
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ hmax)
    (hdyn : ∀ k, x (k + 1) = A (h k) *ᵥ x k) (n : ℕ) :
    energy P (x n) ≤ (1 - hmin * c / upper) ^ n * energy P (x 0) := by
  apply geometric_bound (V := fun k => energy P (x k)) hq
  intro k
  rw [hdyn k]
  have hb := contract_of_decrease P (A (h k)) (hmin0.trans (hlo k)) hc hu hupper
    (hcert (h k) (hlo k) (hhi k)) (x k)
  have hn : 0 ≤ energy P (x k) := by simpa [energy] using hP.dotProduct_mulVec_nonneg (x k)
  have hr : 1 - h k * c / upper ≤ 1 - hmin * c / upper := by
    have hm := mul_le_mul_of_nonneg_right (hlo k) hc
    have hh := div_le_div_of_nonneg_right hm hu.le
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hr hn)

end LeanControls.BernsteinCertificate
