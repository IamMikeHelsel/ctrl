import HodgeBridge
import ContractionCovariance

noncomputable section
namespace GUHodgeBridge

/-- Mathlib H convention. This is exactly the frozen star2 field's type. -/
def mathlibStar2 : GUOperatorAudit.FormIndex 12 → GUOperatorAudit.FormIndex 2 → ℝ := star2

/-- The finite coefficient contraction equals the actual Hodge transformation. -/
theorem frozen_interface_represents (x : E 2) :
    coordinates 12 (H (by decide : 2+12=14) x) =
      GUOperatorAudit.linearCoeff mathlibStar2 (coordinates 2 x) := by
  funext o
  simpa only [GUOperatorAudit.linearCoeff, mathlibStar2, smul_eq_mul] using star2_represents x o

/-- Alpha-wedge-star convention. This coefficient array has the opposite sign. -/
def conventionalStar2 : GUOperatorAudit.FormIndex 12 → GUOperatorAudit.FormIndex 2 → ℝ :=
  fun o i => -star2 o i

theorem conventional_interface_represents (x : E 2) :
    coordinates 12 (S (by decide : 2+12=14) x) =
      GUOperatorAudit.linearCoeff conventionalStar2 (coordinates 2 x) := by
  funext o
  simp only [S, LinearMap.neg_apply, LinearEquiv.coe_coe, map_neg, Pi.neg_apply,
    GUOperatorAudit.linearCoeff, conventionalStar2, smul_eq_mul, neg_mul,
    Finset.sum_neg_distrib]
  exact congrArg Neg.neg (star2_represents x o)

end GUHodgeBridge
