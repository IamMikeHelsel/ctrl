module
public import LeanControls.BernsteinCertificate

/-! A common positive quadratic energy bound is preserved by convex interpolation
of transition vertices. This permits checked polynomial enclosures of an exact
nonpolynomial transition; the enclosure itself remains a separate obligation. -/
@[expose] public section
noncomputable section
namespace LeanControls.VertexCertificate
open Matrix BernsteinCertificate
variable {ι : Type*} [Fintype ι]

theorem energy_mix_identity (P : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    energy P ((1 - t) • x + t • y) =
      (1 - t) * energy P x + t * energy P y -
        t * (1 - t) * energy P (x - y) := by
  simp only [energy, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem energy_mix_bound (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (x y : ι → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    energy P ((1 - t) • x + t • y) ≤ (1 - t) * energy P x + t * energy P y := by
  rw [energy_mix_identity]
  have hE : 0 ≤ energy P (x - y) := hP.dotProduct_mulVec_nonneg _
  have hnonneg := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hE
  linarith

theorem shared_bound (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    (x y : ι → ℝ) {t b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : energy P x ≤ b) (hy : energy P y ≤ b) :
    energy P ((1 - t) • x + t • y) ≤ b := by
  have hmix := energy_mix_bound P hP x y ht0 ht1
  have hxb := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht1)
  have hyb := mul_le_mul_of_nonneg_left hy ht0
  nlinarith only [hmix, hxb, hyb]

theorem matrix_enclosure (P A B C : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {t b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : C = (1 - t) • A + t • B) (x : ι → ℝ)
    (hA : energy P (A *ᵥ x) ≤ b) (hB : energy P (B *ᵥ x) ≤ b) :
    energy P (C *ᵥ x) ≤ b := by
  rw [hC, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  exact shared_bound P hP _ _ ht0 ht1 hA hB

end LeanControls.VertexCertificate
