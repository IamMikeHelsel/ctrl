import RealAdjoint
import SplitSignature

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- Infinitesimal preservation of a fixed real bilinear form. -/
def FormSkew (H A : SpinMatrix) : Prop := A.transpose * H + H * A = 0

/-- The actual Clifford conjugation's minus eigenspace. -/
def CliffordSkew (x : Cl) : Prop := star x = -x

theorem formSkew_iff_adjoint (A : SpinMatrix) :
    FormSkew K A ↔ realAdjoint A = -A := by
  constructor
  · intro h
    have hh := congrArg (fun B : SpinMatrix => K * B) h
    simp only [mul_add, mul_zero, ← mul_assoc, K_square, one_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  · intro h
    have hh := congrArg (fun B : SpinMatrix => K * B) h
    simp only [realAdjoint_apply, ← mul_assoc, K_square, one_mul, mul_neg] at hh
    exact (add_eq_zero_iff_eq_neg).mpr hh

theorem cliffordSkew_iff_formSkew (x : Cl) :
    CliffordSkew x ↔ FormSkew K (splitMatrixEquiv x) := by
  rw [formSkew_iff_adjoint]
  constructor
  · intro h
    change star x = -x at h
    have hh := congrArg splitMatrixEquiv h
    simpa only [map_neg, splitMatrixEquiv_star, realAdjoint_apply] using hh
  · intro h
    apply splitMatrixEquiv.injective
    simpa only [map_neg, splitMatrixEquiv_star, realAdjoint_apply] using h

theorem cliffordSkew_commutator (x y : Cl) (hx : CliffordSkew x) (hy : CliffordSkew y) :
    CliffordSkew (x*y-y*x) := by
  dsimp [CliffordSkew] at *
  rw [star_sub, star_mul, star_mul, hx, hy]
  simp only [neg_mul_neg]
  abel

theorem formSkew_commutator (A B : SpinMatrix) (hA : FormSkew K A)
    (hB : FormSkew K B) : FormSkew K (A*B-B*A) := by
  rw [formSkew_iff_adjoint] at *
  rw [map_sub, realAdjoint_mul, realAdjoint_mul, hA, hB]
  simp only [neg_mul_neg]
  abel

/-- The concrete representation restricts to a bijection of the two skew loci. -/
def skewEquiv : {x : Cl // CliffordSkew x} ≃ {A : SpinMatrix // FormSkew K A} where
  toFun x := ⟨splitMatrixEquiv x, (cliffordSkew_iff_formSkew x).mp x.property⟩
  invFun A := ⟨splitMatrixEquiv.symm A,
    (cliffordSkew_iff_formSkew _).mpr (by simpa using A.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact splitMatrixEquiv.symm_apply_apply x
  right_inv A := by apply Subtype.ext; simp

/-- Coordinates in the explicit split basis, with both inverse equations known. -/
def splitCoordinates (A : SpinMatrix) : SpinMatrix := Uinverse * A * U

theorem splitCoordinates_mul (A B : SpinMatrix) :
    splitCoordinates (A*B) = splitCoordinates A * splitCoordinates B := by
  dsimp [splitCoordinates]
  calc
    Uinverse * (A * B) * U = Uinverse * A * (U * Uinverse) * B * U := by
      rw [Uinverse_right]; simp only [mul_one, mul_assoc]
    _ = Uinverse * A * U * (Uinverse * B * U) := by simp only [mul_assoc]

theorem split_defect (A : SpinMatrix) :
    (splitCoordinates A).transpose * (U.transpose*K*U) +
      (U.transpose*K*U) * splitCoordinates A =
      U.transpose * (A.transpose*K+K*A) * U := by
  have ht : Uinverse.transpose * U.transpose = (1 : SpinMatrix) := by
    rw [← Matrix.transpose_mul, Uinverse_right, Matrix.transpose_one]
  simp only [splitCoordinates, Matrix.transpose_mul, mul_add, add_mul]
  simp only [mul_assoc]
  have ht' : Uinverse.transpose * (U.transpose * (K * U)) = K * U := by
    rw [← mul_assoc, ht, one_mul]
  rw [ht']
  have hu : U * (Uinverse * (A * U)) = A * U := by
    rw [← mul_assoc, Uinverse_right, one_mul]
  rw [hu]

theorem splitCoordinates_formSkew_iff (A : SpinMatrix) :
    FormSkew D (splitCoordinates A) ↔ FormSkew K A := by
  have he : FormSkew (U.transpose*K*U) (splitCoordinates A) ↔ FormSkew K A := by
    dsimp [FormSkew]
    rw [split_defect]
    constructor
    · intro h
      have hh := congrArg (fun B : SpinMatrix => Uinverse.transpose * B * Uinverse) h
      have ht : Uinverse.transpose * U.transpose = (1 : SpinMatrix) := by
        rw [← Matrix.transpose_mul, Uinverse_right, Matrix.transpose_one]
      have hcancel : Uinverse.transpose *
          (U.transpose * (A.transpose*K+K*A) * U) * Uinverse =
          A.transpose*K+K*A := by
        calc
          _ = (Uinverse.transpose * U.transpose) *
              (A.transpose*K+K*A) * (U * Uinverse) := by simp only [mul_assoc]
          _ = _ := by rw [ht, Uinverse_right, one_mul, mul_one]
      rw [hcancel, mul_zero, zero_mul] at hh
      exact hh
    · intro h
      rw [h, mul_zero, zero_mul]
  rw [U_congruence] at he
  have hs : FormSkew ((2 : ℝ) • D) (splitCoordinates A) ↔
      FormSkew D (splitCoordinates A) := by
    simp only [FormSkew, mul_smul_comm, smul_mul_assoc, ← smul_add]
    exact smul_eq_zero.trans (or_iff_right (by norm_num))
  exact hs.symm.trans he

theorem formSkew_add (H A B : SpinMatrix) (hA : FormSkew H A)
    (hB : FormSkew H B) : FormSkew H (A+B) := by
  dsimp [FormSkew] at *
  simp only [Matrix.transpose_add, add_mul, mul_add]
  calc
    _ = (A.transpose * H + H*A) + (B.transpose*H + H*B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

theorem formSkew_smul (H A : SpinMatrix) (c : ℝ) (hA : FormSkew H A) :
    FormSkew H (c • A) := by
  dsimp [FormSkew] at *
  simp only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hA, smul_zero]

theorem splitMatrixEquiv_commutator (x y : Cl) :
    splitMatrixEquiv (x*y-y*x) =
      splitMatrixEquiv x * splitMatrixEquiv y - splitMatrixEquiv y * splitMatrixEquiv x := by
  simp only [map_sub, map_mul]

theorem actual_split_skew_iff (x : Cl) :
    CliffordSkew x ↔ FormSkew D (splitCoordinates (splitMatrixEquiv x)) := by
  rw [splitCoordinates_formSkew_iff, cliffordSkew_iff_formSkew]

end HyperbolicSpinor
