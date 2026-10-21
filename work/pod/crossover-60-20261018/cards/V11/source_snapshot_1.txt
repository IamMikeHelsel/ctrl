/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import ControlsLean.Estimation.ScalarKalman

/-!
# The Sherman–Morrison–Woodbury Identity and Multi-Dimensional Information Filtering

This module formalizes the Sherman–Morrison–Woodbury matrix inversion identity in an
arbitrary associative ring $R$, and proves the exact equivalence between the multi-dimensional
Kalman covariance filter update and the Information filter precision update.

## Mathematical Formulation

Let $R$ be an associative ring.

1. **Two-Sided Inverse**:
   An element $b \in R$ is a two-sided inverse of $a \in R$, denoted `IsInverse a b`, if:
   $$a \cdot b = 1 \quad \text{and} \quad b \cdot a = 1.$$

2. **The Sherman–Morrison–Woodbury Identity**:
   For $A, U, C, V \in R$ such that $A$ is invertible with inverse $A^{-1}$, $C$ is invertible
   with inverse $C^{-1}$, and the modified matrix $M = C^{-1} + V A^{-1} U$ is invertible
   with inverse $M^{-1}$, the inverse of $A + U C V$ is given by:
   $$\mathrm{woodbury}(A^{-1}, U, M^{-1}, V) = A^{-1} - A^{-1} U M^{-1} V A^{-1}.$$
   We prove:
   * `woodbury_right_inv`: $(A + U C V) \cdot \mathrm{woodbury}(A^{-1}, U, M^{-1}, V) = 1$.
   * `woodbury_left_inv`: $\mathrm{woodbury}(A^{-1}, U, M^{-1}, V) \cdot (A + U C V) = 1$.
   * `woodbury_isInverse`: $\mathrm{woodbury}(A^{-1}, U, M^{-1}, V)$ is a two-sided inverse.

3. **Kalman / Information Filter Equivalence**:
   In linear state estimation with prior covariance $P$, measurement matrix $C$ (or $V$, with
   $U = V^\top$), and sensor noise covariance $R$:
   * The **Kalman filter covariance update** computes the posterior error covariance:
     $$P^+ = P - P U (R + V P U)^{-1} V P.$$
   * The **Information filter update** works with the information matrix (precision) $Y = P^{-1}$
     and updates additively:
     $$Y^+ = Y + U R^{-1} V.$$
   * Applying the Woodbury identity with $A = P^{-1}$, $A^{-1} = P$, $C_{\text{woodbury}} = R^{-1}$,
     $C_{\text{woodbury}}^{-1} = R$, and innovation covariance $S = R + V P U$, we establish:
     $$(Y^+)^{-1} = P^+.$$
   This generalizes the scalar precision additivity `(postVarOpt P R)⁻¹ = P⁻¹ + R⁻¹`
   from `ControlsLean.Estimation.ScalarKalman` to multi-dimensional matrices and arbitrary rings.

## References

* Sherman, J., & Morrison, W. J. (1950). Adjustment of an Inverse Matrix to Changes in a
  Specified Column or Row of the Original Matrix. *Annals of Math. Stat.*, 21(1), 124–127.
* Woodbury, M. A. (1950). *Inverting Modified Matrices*. Memorandum Report 42,
  Statistical Research Group, Princeton University.
* Anderson, B. D. O., & Moore, J. B. (1979). *Optimal Filtering*. Prentice-Hall, Chapter 6.
* Kailath, T., Sayed, A. H., & Hassibi, B. (2000). *Linear Estimation*. Prentice Hall, Section 9.3.
-/

namespace ControlsLean.Estimation

variable {R : Type*} [Ring R]

/-- Two-sided inverse predicate in an associative ring `R`. -/
def IsInverse (a b : R) : Prop :=
  a * b = 1 ∧ b * a = 1

theorem IsInverse.symm {a b : R} (h : IsInverse a b) : IsInverse b a :=
  ⟨h.2, h.1⟩

/-- The Sherman–Morrison–Woodbury inverse candidate:
Given $A^{-1}$, $U$, $M^{-1}$, and $V$,
`woodbury A_inv U M_inv V = A_inv - A_inv * U * M_inv * V * A_inv`. -/
def woodbury (A_inv U M_inv V : R) : R :=
  A_inv - A_inv * U * M_inv * V * A_inv

/-- **The Sherman–Morrison–Woodbury Right Inverse**:
Under the associativity of ring `R`,
$(A + U C V) \cdot \mathrm{woodbury}(A^{-1}, U, M^{-1}, V) = 1$. -/
theorem woodbury_right_inv (A A_inv C C_inv U V M M_inv : R)
    (hA : A * A_inv = 1) (_hA' : A_inv * A = 1)
    (hC : C * C_inv = 1) (_hC' : C_inv * C = 1)
    (hM_def : M = C_inv + V * A_inv * U)
    (hM : M * M_inv = 1) (_hM' : M_inv * M = 1) :
    (A + U * C * V) * (woodbury A_inv U M_inv V) = 1 := by
  have key : V * A_inv * U = M - C_inv := by rw [hM_def]; abel
  unfold woodbury
  calc (A + U * C * V) * (A_inv - A_inv * U * M_inv * V * A_inv)
    _ = A * A_inv - A * (A_inv * U * M_inv * V * A_inv) +
        (U * C * V) * A_inv - (U * C * V) * (A_inv * U * M_inv * V * A_inv) := by
      noncomm_ring
    _ = 1 - U * M_inv * V * A_inv + U * C * V * A_inv -
        U * C * (V * A_inv * U) * M_inv * V * A_inv := by
      rw [hA]
      simp only [← mul_assoc, hA, one_mul]
    _ = 1 - U * M_inv * V * A_inv + U * C * V * A_inv -
        U * C * (M - C_inv) * M_inv * V * A_inv := by rw [key]
    _ = 1 := by
      have hMC : (M - C_inv) * M_inv = 1 - C_inv * M_inv := by
        rw [sub_mul, hM]
      rw [mul_assoc (U * C) (M - C_inv) M_inv, hMC]
      rw [mul_sub, mul_one, ← mul_assoc (U * C) C_inv M_inv, mul_assoc U C C_inv, hC, mul_one]
      noncomm_ring

/-- **The Sherman–Morrison–Woodbury Left Inverse**:
Under the associativity of ring `R`,
$\mathrm{woodbury}(A^{-1}, U, M^{-1}, V) \cdot (A + U C V) = 1$. -/
theorem woodbury_left_inv (A A_inv C C_inv U V M M_inv : R)
    (_hA : A * A_inv = 1) (hA' : A_inv * A = 1)
    (_hC : C * C_inv = 1) (hC' : C_inv * C = 1)
    (hM_def : M = C_inv + V * A_inv * U)
    (_hM : M * M_inv = 1) (hM' : M_inv * M = 1) :
    (woodbury A_inv U M_inv V) * (A + U * C * V) = 1 := by
  have key : V * A_inv * U = M - C_inv := by rw [hM_def]; abel
  unfold woodbury
  calc (A_inv - A_inv * U * M_inv * V * A_inv) * (A + U * C * V)
    _ = A_inv * A + A_inv * (U * C * V) -
        (A_inv * U * M_inv * V * A_inv) * A -
        (A_inv * U * M_inv * V * A_inv) * (U * C * V) := by
      noncomm_ring
    _ = 1 + A_inv * U * C * V - A_inv * U * M_inv * V -
        A_inv * U * M_inv * (V * A_inv * U) * C * V := by
      rw [hA']
      simp only [mul_assoc, hA', mul_one]
    _ = 1 + A_inv * U * C * V - A_inv * U * M_inv * V -
        A_inv * U * M_inv * (M - C_inv) * C * V := by rw [key]
    _ = 1 := by
      have hMC : M_inv * (M - C_inv) = 1 - M_inv * C_inv := by
        rw [mul_sub, hM']
      have h_mid : A_inv * U * M_inv * (M - C_inv) * C * V =
          (A_inv * U) * (M_inv * (M - C_inv)) * (C * V) := by
        simp only [mul_assoc]
      rw [h_mid, hMC]
      rw [mul_sub, mul_one, sub_mul]
      have hC_cancel : (A_inv * U) * (M_inv * C_inv) * (C * V) = A_inv * U * M_inv * V := by
        calc (A_inv * U) * (M_inv * C_inv) * (C * V)
          _ = (A_inv * U * M_inv) * (C_inv * C) * V := by simp only [mul_assoc]
          _ = (A_inv * U * M_inv) * 1 * V := by rw [hC']
          _ = A_inv * U * M_inv * V := by simp only [mul_one, mul_assoc]
      rw [hC_cancel]
      noncomm_ring

/-- **The Sherman–Morrison–Woodbury Two-Sided Inverse Theorem**:
`woodbury A_inv U M_inv V` is the two-sided inverse of `A + U * C * V`. -/
theorem woodbury_isInverse (A A_inv C C_inv U V M M_inv : R)
    (hA : IsInverse A A_inv)
    (hC : IsInverse C C_inv)
    (hM_def : M = C_inv + V * A_inv * U)
    (hM : IsInverse M M_inv) :
    IsInverse (A + U * C * V) (woodbury A_inv U M_inv V) :=
  ⟨woodbury_right_inv A A_inv C C_inv U V M M_inv hA.1 hA.2 hC.1 hC.2 hM_def hM.1 hM.2,
   woodbury_left_inv A A_inv C C_inv U V M M_inv hA.1 hA.2 hC.1 hC.2 hM_def hM.1 hM.2⟩

/-! ### Multi-Dimensional Information Filter Equivalence -/

/-- Innovation covariance: `S = R_cov + V * P * U`.
In Kalman filtering with measurement matrix `C`, `U = Cᵀ` and `V = C`, so `S = R + C * P * Cᵀ`. -/
def innovationCov (R_cov P U V : R) : R :=
  R_cov + V * P * U

/-- Posterior covariance update in Kalman covariance filter form:
`P⁺ = P - P * U * S_inv * V * P`.
In standard matrix notation where `U = Cᵀ` and `V = C`, this is
`P⁺ = P - P * Cᵀ * S⁻¹ * C * P`. -/
def kalmanPostCov (P U S_inv V : R) : R :=
  P - P * U * S_inv * V * P

/-- Posterior information matrix in Information filter form:
`Y⁺ = P_inv + U * R_inv * V`.
In standard matrix notation where `Y = P⁻¹`, `U = Cᵀ`, and `V = C`, this is
`Y⁺ = Y + Cᵀ * R⁻¹ * C`. -/
def informationPost (P_inv U R_inv V : R) : R :=
  P_inv + U * R_inv * V

/-- Right inverse identity for the Kalman covariance and information filter equivalence:
`Y⁺ * P⁺ = 1`. -/
theorem kalman_information_right_inv (P P_inv R_cov R_inv U V S S_inv : R)
    (hP : IsInverse P P_inv)
    (hR : IsInverse R_cov R_inv)
    (hS_def : S = innovationCov R_cov P U V)
    (hS : IsInverse S S_inv) :
    (informationPost P_inv U R_inv V) * (kalmanPostCov P U S_inv V) = 1 := by
  have hP_inv : IsInverse P_inv P := hP.symm
  have hR_inv : IsInverse R_inv R_cov := hR.symm
  have hM_def : S = R_cov + V * P * U := hS_def
  exact woodbury_right_inv P_inv P R_inv R_cov U V S S_inv
    hP_inv.1 hP_inv.2 hR_inv.1 hR_inv.2 hM_def hS.1 hS.2

/-- Left inverse identity for the Kalman covariance and information filter equivalence:
`P⁺ * Y⁺ = 1`. -/
theorem kalman_information_left_inv (P P_inv R_cov R_inv U V S S_inv : R)
    (hP : IsInverse P P_inv)
    (hR : IsInverse R_cov R_inv)
    (hS_def : S = innovationCov R_cov P U V)
    (hS : IsInverse S S_inv) :
    (kalmanPostCov P U S_inv V) * (informationPost P_inv U R_inv V) = 1 := by
  have hP_inv : IsInverse P_inv P := hP.symm
  have hR_inv : IsInverse R_inv R_cov := hR.symm
  have hM_def : S = R_cov + V * P * U := hS_def
  exact woodbury_left_inv P_inv P R_inv R_cov U V S S_inv
    hP_inv.1 hP_inv.2 hR_inv.1 hR_inv.2 hM_def hS.1 hS.2

/-- **Kalman Covariance and Information Filter Equivalence (Two-Sided Inverse)**:
The posterior information matrix `Y⁺ = P⁻¹ + U R⁻¹ V` and the posterior Kalman covariance
`P⁺ = P - P U (R + V P U)⁻¹ V P` are mutual two-sided inverses.
This establishes that updating precisions additively in information form is mathematically
identical to the optimal minimum-variance covariance update in standard Kalman filter form. -/
theorem kalman_information_equivalence (P P_inv R_cov R_inv U V S S_inv : R)
    (hP : IsInverse P P_inv)
    (hR : IsInverse R_cov R_inv)
    (hS_def : S = innovationCov R_cov P U V)
    (hS : IsInverse S S_inv) :
    IsInverse (informationPost P_inv U R_inv V) (kalmanPostCov P U S_inv V) :=
  ⟨kalman_information_right_inv P P_inv R_cov R_inv U V S S_inv hP hR hS_def hS,
   kalman_information_left_inv P P_inv R_cov R_inv U V S S_inv hP hR hS_def hS⟩

/-- **Kalman Covariance & Information Filter Equivalence (Explicit Form)**:
Specialized formulation matching the single measurement operator `C_mat`. -/
theorem kalman_postVar_information_equiv (P P_inv R_cov R_inv C_mat S S_inv : R)
    (hP : P * P_inv = 1) (hP' : P_inv * P = 1)
    (hR : R_cov * R_inv = 1) (hR' : R_inv * R_cov = 1)
    (hS_def : S = R_cov + C_mat * P * C_mat)
    (hS : S * S_inv = 1) (hS' : S_inv * S = 1) :
    (P_inv + C_mat * R_inv * C_mat) * (P - P * C_mat * S_inv * C_mat * P) = 1 := by
  have := woodbury_right_inv P_inv P R_inv R_cov C_mat C_mat S S_inv
    hP' hP hR' hR (by rw [hS_def]) hS hS'
  exact this

/-! ### Specialization to Commutative Rings and Connection to Scalar Kalman -/

variable {K : Type*} [CommRing K]

/-- In a commutative ring with identity measurement operator ($C = 1$), the Kalman covariance
formula $P - P S^{-1} P$ simplifies to the harmonic product $P R S^{-1}$. -/
theorem kalman_scalar_cov_eq (P R_cov S S_inv : K)
    (hS_def : S = P + R_cov)
    (hS : S * S_inv = 1) :
    P - P * S_inv * P = P * R_cov * S_inv := by
  calc P - P * S_inv * P
    _ = P * 1 - P * S_inv * P := by ring
    _ = P * (S * S_inv) - P * S_inv * P := by rw [hS]
    _ = P * ((P + R_cov) * S_inv) - P * S_inv * P := by rw [hS_def]
    _ = P * R_cov * S_inv := by ring

/-- Commutative scalar information and covariance product:
$(P^{-1} + R^{-1}) \cdot (P R S^{-1}) = 1$ when $S = P + R$.
This directly links the ring-level Woodbury identity to the scalar Kalman precision
relation `inv_postVarOpt` (`(postVarOpt P R)⁻¹ = P⁻¹ + R⁻¹`). -/
theorem kalman_scalar_information_equiv (P P_inv R_cov R_inv S S_inv : K)
    (hP : P * P_inv = 1)
    (hR : R_cov * R_inv = 1)
    (hS_def : S = P + R_cov)
    (hS : S * S_inv = 1) :
    (P_inv + R_inv) * (P * R_cov * S_inv) = 1 := by
  have hP' : P_inv * P = 1 := by rw [mul_comm, hP]
  have hR' : R_inv * R_cov = 1 := by rw [mul_comm, hR]
  calc (P_inv + R_inv) * (P * R_cov * S_inv)
    _ = (P_inv * P) * R_cov * S_inv + (R_inv * R_cov) * P * S_inv := by ring
    _ = 1 * R_cov * S_inv + 1 * P * S_inv := by rw [hP', hR']
    _ = (P + R_cov) * S_inv := by ring
    _ = S * S_inv := by rw [hS_def]
    _ = 1 := hS

end ControlsLean.Estimation
