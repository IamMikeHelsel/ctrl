import GaugeSignAudit

/-!
A precise coefficient model for the pointwise conjugation mechanism of GU (9.3).
The indices have the actual exterior-form dimensions in base dimension 14.
Every contraction is DEFINED by fixed real coefficients. Its equivariance is
proved from matrix multiplication, not assumed as an input hypothesis.

This model does not assert that the coefficient arrays are Hodge-star or wedge
coefficients. Supplying those arrays and proving that bridge is a separate step.
It also makes no claim that the expression stays in the specified Lie algebra,
annihilates Weyl curvature, or has the required Bianchi identity.
-/
noncomputable section
open scoped BigOperators
namespace GUOperatorAudit

variable {R : Type*} [Ring R] [Algebra ℝ R]

omit [Algebra ℝ R] in
@[simp] theorem conjugate_add (h : Rˣ) (x y : R) :
    conjugate h (x+y) = conjugate h x + conjugate h y := by
  simp [conjugate, mul_add, add_mul]

omit [Algebra ℝ R] in
@[simp] theorem conjugate_sub (h : Rˣ) (x y : R) :
    conjugate h (x-y) = conjugate h x - conjugate h y := by
  simp [conjugate, mul_sub, sub_mul]

omit [Algebra ℝ R] in
@[simp] theorem conjugate_mul (h : Rˣ) (x y : R) :
    conjugate h (x*y) = conjugate h x * conjugate h y := by
  unfold conjugate
  simp only [mul_assoc]
  rw [← mul_assoc (↑h : R) (↑h⁻¹ : R), Units.mul_inv, one_mul]

@[simp] theorem conjugate_smul (h : Rˣ) (c : ℝ) (x : R) :
    conjugate h (c • x) = c • conjugate h x := by
  simp [conjugate]

omit [Algebra ℝ R] in
@[simp] theorem conjugate_sum {I : Type*} (h : Rˣ) (s : Finset I) (f : I → R) :
    conjugate h (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate h (f i) := by
  simp [conjugate, Finset.mul_sum, Finset.sum_mul]

/-- Pointwise action on any finite coordinate array. -/
def gauge {I : Type*} (h : Rˣ) (f : I → R) : I → R := fun i => conjugate h (f i)

/-- A fixed real coefficient linear map. -/
def linearCoeff {I O : Type*} [Fintype I]
    (C : O → I → ℝ) (f : I → R) : O → R := fun o => ∑ i, C o i • f i

/-- A fixed real coefficient bilinear contraction, with ordered matrix product. -/
def productCoeff {I J O : Type*} [Fintype I] [Fintype J]
    (C : O → I → J → ℝ) (f : I → R) (g : J → R) : O → R :=
  fun o => ∑ i, ∑ j, C o i j • (f i * g j)

@[simp] theorem linearCoeff_gauge {I O : Type*} [Fintype I]
    (C : O → I → ℝ) (h : Rˣ) (f : I → R) :
    linearCoeff C (gauge h f) = gauge h (linearCoeff C f) := by
  ext o
  simp [linearCoeff, gauge, conjugate, Finset.mul_sum, Finset.sum_mul]

@[simp] theorem productCoeff_gauge {I J O : Type*} [Fintype I] [Fintype J]
    (C : O → I → J → ℝ) (h : Rˣ) (f : I → R) (g : J → R) :
    productCoeff C (gauge h f) (gauge h g) = gauge h (productCoeff C f g) := by
  ext o
  simp only [productCoeff, gauge]
  simp only [conjugate, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]
  congr 1
  ext i
  congr 1
  ext j
  congr 1
  symm
  exact conjugate_mul h (f i) (g j)

omit [Algebra ℝ R] in
@[simp] theorem gauge_product (e h : Rˣ) {I : Type*} (f : I → R) :
    gauge (e*h) f = gauge h (gauge e f) := by
  ext i
  simp [gauge, conjugate, mul_inv_rev, mul_assoc]

@[simp] theorem gauge_sub {I : Type*} (h : Rˣ) (f g : I → R) :
    gauge h (f-g) = gauge h f - gauge h g := by
  ext i
  exact conjugate_sub h (f i) (g i)

@[simp] theorem gauge_smul {I : Type*} (h : Rˣ) (c : ℝ) (f : I → R) :
    gauge h (c • f) = c • gauge h f := by
  ext i
  exact conjugate_smul h c (f i)

/-- Coordinate index for a k-form on the fourteen-dimensional observerse. -/
abbrev FormIndex (k : ℕ) := Fin (Nat.choose 14 k)
abbrev Form (R : Type*) (k : ℕ) := FormIndex k → R

/-- Required coefficient types. The two summands of (9.3) both land in degree 13. -/
structure SwerveCoefficients where
  star2 : FormIndex 12 → FormIndex 2 → ℝ
  star14 : FormIndex 0 → FormIndex 14 → ℝ
  star1 : FormIndex 13 → FormIndex 1 → ℝ
  wedge1_12 : FormIndex 13 → FormIndex 1 → FormIndex 12 → ℝ
  wedge2_12 : FormIndex 14 → FormIndex 2 → FormIndex 12 → ℝ
  wedge1_0 : FormIndex 1 → FormIndex 1 → FormIndex 0 → ℝ

/-- Fixed-coefficient instantiation of the algebraic expression in (9.3). -/
def swerve (C : SwerveCoefficients) (p1 : Form R 1) (p2 : Form R 2)
    (e : Rˣ) (x : Form R 2) : Form R 13 :=
  productCoeff C.wedge1_12 (gauge e p1) (linearCoeff C.star2 x) -
    (1/2 : ℝ) • linearCoeff C.star1
      (productCoeff C.wedge1_0 (gauge e p1)
        (linearCoeff C.star14
          (productCoeff C.wedge2_12 (gauge e p2) (linearCoeff C.star2 x))))

/-- The compensation mechanism holds for every fixed coefficient choice. -/
theorem swerve_covariant (C : SwerveCoefficients) (p1 : Form R 1) (p2 : Form R 2)
    (e h : Rˣ) (x : Form R 2) :
    swerve C p1 p2 (e*h) (gauge h x) = gauge h (swerve C p1 p2 e x) := by
  simp [swerve]

end GUOperatorAudit
