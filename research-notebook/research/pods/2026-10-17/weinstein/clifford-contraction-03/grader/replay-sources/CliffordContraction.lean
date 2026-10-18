import CliffordModel
import ContractionAlgebra

noncomputable section
open scoped BigOperators
namespace GUClifford
open GUContraction

abbrev Tensor := Ix → Ix → Ix → Ix → ℝ
def rho (R:Tensor) (a b c d:Ix) : ℝ := eps a * eps b * eps c * eps d * R a b c d
def Ric (R:Tensor) (b d:Ix) : ℝ := ∑ a, eps a * R a b a d
def scal (R:Tensor) : ℝ := ∑ b, eps b * Ric R b b

/-- The increasing-pair sum with actual products in Mathlib's Clifford algebra. -/
def K (R:Tensor) : Cl := GUContraction.sortedK (rho R) gamma

theorem rho_pair (R:Tensor) (h:PairSymmetries R) : PairSymmetries (rho R) := by
  constructor
  · intro a b c d; unfold rho; rw [h.skew1 a b c d]; ring
  · intro a b c d; unfold rho; rw [h.skew2 a b c d]; ring
  · intro a b c d; unfold rho; rw [h.exchange a b c d]; ring

theorem rho_curvature (R:Tensor) (h:Curvature R) : Curvature (rho R) := by
  refine ⟨rho_pair R h.toPairSymmetries, ?_⟩
  intro a b c d
  calc
    _ = (eps a*eps b*eps c*eps d) * (R a b c d-R a c b d+R a d b c) := by
      unfold rho; ring
    _ = 0 := by rw [h.bianchi]; ring

theorem rho_diag (R:Tensor) (a b:Ix) : rho R a b a b=R a b a b := by
  unfold rho
  calc
    _ = (eps a*eps a)*(eps b*eps b)*R a b a b := by ring
    _ = _ := by rw [eps_sq,eps_sq]; ring

theorem trace_rho (R:Tensor) : traceR (rho R) eps = scal R := by
  unfold traceR scal Ric
  simp_rw [rho_diag, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  ring

theorem actual_normalization_bridge (R:Tensor) (h:PairSymmetries R) :
    total (rho R) gamma = (2:ℝ) • K R := by
  exact normalization_bridge (rho R) (rho_pair R h) eps gamma gamma_relation

/-- The scalar contraction, with all four algebraic curvature identities explicit. -/
theorem actual_clifford_contraction (R:Tensor) (h:Curvature R) :
    K R = algebraMap ℝ Cl (-scal R) := by
  unfold K
  rw [sorted_contraction (rho R) (rho_curvature R h) eps gamma gamma_relation, trace_rho]
  simp [Algebra.algebraMap_eq_smul_one]

end GUClifford
