import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace GUClifford

abbrev Ix := Fin 14
abbrev V := Ix → ℝ
def eps (a : Ix) : ℝ := if a.val < 7 then 1 else -1
def Q : QuadraticForm ℝ V := QuadraticMap.weightedSumSquares ℝ eps
def e (a : Ix) : V := Pi.single a 1
abbrev Cl := CliffordAlgebra Q
def gamma (a : Ix) : Cl := CliffordAlgebra.ι Q (e a)

theorem eps_sq (a : Ix) : eps a * eps a = 1 := by
  unfold eps; split_ifs <;> norm_num

theorem Q_apply (v : V) : Q v = ∑ a, eps a * (v a)^2 := by
  simp [Q, QuadraticMap.weightedSumSquares_apply, pow_two]

theorem Q_e (a : Ix) : Q (e a) = eps a := by
  simp [Q, e, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]

theorem Q_polar_e (a b : Ix) : QuadraticMap.polar Q (e a) (e b) =
    if a=b then 2 * eps a else 0 := by
  classical
  have hp (v w : V) : QuadraticMap.polar Q v w = ∑ a, 2 * eps a * v a * w a := by
    rw [QuadraticMap.polar, Q_apply, Q_apply, Q_apply,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.add_apply]
    ring
  rw [hp]
  simp [e, Pi.single_apply, mul_ite]
  split_ifs with h h h <;> simp_all

theorem gamma_relation (a b : Ix) : gamma a * gamma b + gamma b * gamma a =
    (if a=b then 2 * eps a else 0) • (1 : Cl) := by
  rw [gamma, gamma, CliffordAlgebra.ι_mul_ι_add_swap, Q_polar_e]
  simp [Algebra.algebraMap_eq_smul_one]

theorem gamma_sq (a : Ix) : gamma a * gamma a = eps a • (1 : Cl) := by
  rw [gamma, CliffordAlgebra.ι_sq_scalar, Q_e]
  simp [Algebra.algebraMap_eq_smul_one]

theorem gamma_swap (a b : Ix) (hab : a≠b) : gamma a * gamma b = -(gamma b * gamma a) := by
  have h := gamma_relation a b
  simp [hab] at h
  exact eq_neg_of_add_eq_zero_left h

theorem clifford_nontrivial : Nontrivial Cl := inferInstance

end GUClifford
