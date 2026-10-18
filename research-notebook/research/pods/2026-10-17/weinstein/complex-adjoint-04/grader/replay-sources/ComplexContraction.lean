import ComplexAdjoint
import CliffordContraction

noncomputable section
namespace GUComplex
open GUClifford GUContraction

-- The same explicit sorted-pair sum, now in the actual complex tensor algebra.
def complexK (R : Tensor) : CCl := sortedK (rho R) cgamma

theorem complexK_embed (R : Tensor) : complexK R = embed (K R) := by
  simp [complexK, K, sortedK, cgamma, map_sum, map_smul, map_add, map_mul]

theorem complex_clifford_contraction (R : Tensor) (h : Curvature R) :
    complexK R = algebraMap ℝ CCl (-scal R) := by
  rw [complexK_embed, actual_clifford_contraction R h]
  exact embed.commutes _

theorem complexK_bar_fixed (R : Tensor) (h : Curvature R) :
    bar (complexK R) = complexK R := by
  rw [complexK_embed, bar_embed, actual_clifford_contraction R h]
  rw [CliffordAlgebra.star_algebraMap]

end GUComplex
