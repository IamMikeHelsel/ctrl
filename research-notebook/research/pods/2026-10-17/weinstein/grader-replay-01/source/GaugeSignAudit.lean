import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
Finite-dimensional sign audit of Geometric Unity (2021), (6.4), (6.13),
(6.19), (7.3)-(7.4). The ring result applies to real matrices.
The derivative is not assumed to obey the desired identity: it is the concrete
covariant derivative of a constant matrix field, D_A x = A*x - x*A.
A nonzero defect in this special case refutes the universal displayed identity.
-/
noncomputable section
namespace GUOperatorAudit

variable {R : Type*} [Ring R]

/-- One component of a covariant derivative for constant matrix fields. -/
def covDerivative (A x : R) : R := A*x - x*A

/-- The product rule is proved from the concrete definition. -/
theorem covDerivative_mul (A x y : R) :
    covDerivative A (x*y) = covDerivative A x*y + x*covDerivative A y := by
  unfold covDerivative
  noncomm_ring

/-- Adjoint action used in the right gauge convention. -/
def conjugate (h : Rˣ) (x : R) : R := (↑h⁻¹ : R)*x*↑h

/-- The inhomogeneous connection term h⁻¹ D_A h. -/
def shift (A : R) (h : Rˣ) : R := (↑h⁻¹ : R)*covDerivative A ↑h

/-- Product law for the connection term, proved rather than postulated. -/
theorem shift_mul (A : R) (e h : Rˣ) :
    shift A (e*h) = conjugate h (shift A e) + shift A h := by
  simp only [shift, conjugate, Units.val_mul, mul_inv_rev, covDerivative_mul]
  simp only [mul_add, mul_assoc]
  rw [← mul_assoc (↑e⁻¹ : R) (↑e : R), Units.inv_mul, one_mul]

/-- Pointwise product rule, with arbitrary derivative values of e and h.
This is the exact local algebra needed for any covariant derivative, after a
one-form is evaluated on a tangent vector. No constancy assumption is used. -/
theorem pointwise_shift_product (e h : Rˣ) (de dh : R) :
    (↑(e*h)⁻¹ : R) * (de * ↑h + ↑e * dh) =
      conjugate h ((↑e⁻¹ : R) * de) + (↑h⁻¹ : R) * dh := by
  simp only [conjugate, mul_inv_rev, Units.val_mul, mul_add, mul_assoc]
  rw [← mul_assoc (↑e⁻¹ : R) (↑e : R), Units.inv_mul, one_mul]

/-- Exact defect for arbitrary pointwise derivative data. The product derivative
is expanded by the same Leibniz rule used in the author's (6.5) and (7.4). -/
theorem pointwise_printed_torsion_defect (e h : Rˣ) (de dh w : R) :
    (conjugate h w - (↑h⁻¹ : R) * dh) -
      (↑(e*h)⁻¹ : R) * (de * ↑h + ↑e * dh) =
    conjugate h (w - (↑e⁻¹ : R) * de) -
      ((↑h⁻¹ : R) * dh + (↑h⁻¹ : R) * dh) := by
  rw [pointwise_shift_product]
  unfold conjugate
  noncomm_ring

/-- The torsion formula printed in (7.3). -/
def torsionMinus (A : R) (e : Rˣ) (w : R) : R := w - shift A e

/-- Alternative sign, explicitly our audited convention, not the printed (7.3). -/
def torsionPlus (A : R) (e : Rˣ) (w : R) : R := w + shift A e

/-- Second component after the negative tilted transformation (6.13). -/
def tiltedMinus (A : R) (h : Rˣ) (w : R) : R := conjugate h w - shift A h

/-- Positive convention used after the first equality in the proof (7.4). -/
def tiltedPlus (A : R) (h : Rˣ) (w : R) : R := conjugate h w + shift A h

/-- Exact defect when the printed negative tilt and printed torsion are combined. -/
theorem printed_torsion_defect (A : R) (e h : Rˣ) (w : R) :
    torsionMinus A (e*h) (tiltedMinus A h w) =
      conjugate h (torsionMinus A e w) - (shift A h + shift A h) := by
  unfold torsionMinus tiltedMinus
  rw [shift_mul]
  unfold conjugate
  noncomm_ring

/-- Keeping the printed torsion, the positive tilt makes its covariance exact. -/
theorem positive_tilt_torsion_covariant (A : R) (e h : Rˣ) (w : R) :
    torsionMinus A (e*h) (tiltedPlus A h w) =
      conjugate h (torsionMinus A e w) := by
  unfold torsionMinus tiltedPlus
  rw [shift_mul]
  unfold conjugate
  noncomm_ring

/-- Keeping the printed negative tilt, changing torsion to the plus convention works. -/
theorem negative_tilt_plus_torsion_covariant (A : R) (e h : Rˣ) (w : R) :
    torsionPlus A (e*h) (tiltedMinus A h w) =
      conjugate h (torsionPlus A e w) := by
  unfold torsionPlus tiltedMinus
  rw [shift_mul]
  unfold conjugate
  noncomm_ring

/-- Right action (6.2) on the zero connection offset. -/
def rightActionAtBase (A : R) (h : Rˣ) (w : R) : R := shift A h + w

theorem negative_tilt_stabilizes_base (A : R) (h : Rˣ) :
    rightActionAtBase A h (-shift A h) = 0 := by
  simp [rightActionAtBase]

/-- Positive tilt does not generally stabilize the selected base connection. -/
theorem positive_tilt_base_defect (A : R) (h : Rˣ) :
    rightActionAtBase A h (shift A h) = shift A h + shift A h := rfl

/-- A finite-dimensional witness: three-by-three real matrices. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def baseMatrix : Mat := !![0,-1,0;1,0,0;0,0,0]
def gaugeMatrix : Mat := !![-1,0,0;0,1,0;0,0,-1]
def gaugeInverse : Mat := gaugeMatrix

def witnessGauge : Matˣ where
  val := gaugeMatrix
  inv := gaugeInverse
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gaugeMatrix, gaugeInverse, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gaugeMatrix, gaugeInverse, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The chosen connection coefficient lies in the orthogonal Lie algebra. -/
theorem baseMatrix_skew : baseMatrix.transpose = -baseMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [baseMatrix, Matrix.transpose_apply]

/-- The gauge witness preserves a positive-definite metric. -/
theorem gaugeMatrix_orthogonal : gaugeMatrix.transpose * gaugeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeMatrix, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- It is orientation preserving as well. -/
theorem gaugeMatrix_det : gaugeMatrix.det = 1 := by
  norm_num [gaugeMatrix, Matrix.det_fin_three]

theorem witness_shift_nonzero : shift baseMatrix witnessGauge ≠ 0 := by
  intro h
  have hc := congrArg (fun M : Mat => M 0 1) h
  norm_num [shift, covDerivative, baseMatrix, witnessGauge, gaugeMatrix,
    gaugeInverse, Matrix.mul_apply, Fin.sum_univ_succ] at hc

/-- The displayed (7.4) covariance equality fails for the displayed (6.13) sign. -/
theorem printed_covariance_counterexample :
    torsionMinus baseMatrix (1*witnessGauge)
      (tiltedMinus baseMatrix witnessGauge 0) ≠
    conjugate witnessGauge (torsionMinus baseMatrix 1 0) := by
  intro h
  have hc := congrArg (fun M : Mat => M 0 1) h
  norm_num [torsionMinus, tiltedMinus, conjugate, shift, covDerivative,
    baseMatrix, witnessGauge, gaugeMatrix, gaugeInverse,
    Matrix.mul_apply, Fin.sum_univ_succ] at hc

/-- Over real matrices, the mixed-convention identity works exactly for zero shift. -/
theorem printed_covariance_iff_zero_shift (A : Mat) (e h : Matˣ) (w : Mat) :
    torsionMinus A (e*h) (tiltedMinus A h w) =
      conjugate h (torsionMinus A e w) ↔ shift A h = 0 := by
  rw [printed_torsion_defect]
  constructor
  · intro heq
    ext i j
    have hc := congrArg (fun M : Mat => M i j) heq
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply] at hc ⊢
    linarith
  · intro heq
    simp [heq]

end GUOperatorAudit
