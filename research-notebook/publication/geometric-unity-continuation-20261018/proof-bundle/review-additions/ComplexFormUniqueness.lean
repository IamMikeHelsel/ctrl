import ComplexBridge
import Mathlib.Data.Matrix.Basis

noncomputable section
namespace HyperbolicSpinor
open GUComplex

/-- Full compatibility includes the specified conjugate-linear Clifford adjoint. -/
def ComplexCompatible (H : CMatrix) : Prop :=
  ∀ x : CCl, (complexMatrixEquiv x).conjTranspose * H = H * complexMatrixEquiv (bar x)

theorem complex_compatible_centralizer (H : CMatrix) (h : ComplexCompatible H) (A : CMatrix) :
    A * (H*Kc) = (H*Kc) * A := by
  obtain ⟨x, hx⟩ := complexMatrixEquiv.surjective A.conjTranspose
  have hi := h x
  rw [complexMatrixEquiv_bar, hx, Matrix.conjTranspose_conjTranspose] at hi
  have hh := congrArg (fun M : CMatrix => M*Kc) hi
  simpa only [mul_assoc, Kc_square, mul_one] using hh

theorem complexCompatible_scalar (H : CMatrix) (h : ComplexCompatible H) :
    ∃ c : ℂ, H = c • Kc := by
  have hc : H*Kc ∈ Set.range (Matrix.scalar (Finset (Fin 7))) :=
    Matrix.mem_range_scalar_of_commute_single (fun i j _ =>
      complex_compatible_centralizer H h (Matrix.single i j 1))
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  have hh := congrArg (fun M : CMatrix => M*Kc) hc
  have hs : Matrix.scalar (Finset (Fin 7)) c = c • (1 : CMatrix) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  rw [hs] at hh
  simpa [mul_assoc, Kc_square] using hh.symm

theorem scalar_complexCompatible (c : ℂ) : ComplexCompatible (c • Kc) := by
  intro x
  rw [complexMatrixEquiv_bar]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [← mul_assoc, Kc_square, one_mul]

theorem complexCompatible_iff (H : CMatrix) :
    ComplexCompatible H ↔ ∃ c : ℂ, H = c • Kc := by
  exact ⟨complexCompatible_scalar H, by rintro ⟨c, rfl⟩; exact scalar_complexCompatible c⟩

theorem hermitian_complexCompatible_real_scalar (H : CMatrix) (h : ComplexCompatible H)
    (hH : H.conjTranspose = H) : ∃ c : ℝ, H = (c : ℂ) • Kc := by
  obtain ⟨c, rfl⟩ := complexCompatible_scalar H h
  have hk : Kc ≠ 0 := by
    intro hz
    have hs := Kc_square
    rw [hz, zero_mul] at hs
    exact zero_ne_one hs
  have hc : star c = c := by
    apply smul_left_injective ℂ hk
    simpa only [Matrix.conjTranspose_smul, Kc_conjTranspose] using hH
  have him : c.im = 0 := by
    have hi := congrArg Complex.im hc
    change -c.im = c.im at hi
    linarith
  refine ⟨c.re, ?_⟩
  have he : (c.re : ℂ) = c := by
    apply Complex.ext <;> simp [him]
  rw [he]

end HyperbolicSpinor
