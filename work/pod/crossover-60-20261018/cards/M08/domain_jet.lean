import Mathlib.Tactic
namespace M08Jet
/-- Component normalization for the separately checked H000=1 formal curvature
jet. This lemma does not construct or realize a global metric. -/
theorem jet_divergence (β dr ds : ℝ) (hr : dr=13) (hs : ds=26) :
    2*dr-β*ds=26*(1-β) := by rw [hr,hs]; ring

theorem jet_selects_scalar_coefficient (β : ℝ) :
    26*(1-β)=0 ↔ β=1 := by constructor <;> intro h <;> linarith

#print axioms jet_divergence
#print axioms jet_selects_scalar_coefficient
end M08Jet
