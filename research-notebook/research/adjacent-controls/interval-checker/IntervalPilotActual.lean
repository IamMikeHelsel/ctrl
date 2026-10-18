module
public import IntervalPilot
public import CoefficientCells
@[expose] public section
noncomputable section
namespace LeanControls.IntervalPilotActual
open IntervalChecker IntervalPilot

theorem coeff_sound {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) :
    CoeffMem coeff r (1/20) := by
  obtain ⟨he,hb,hc⟩ := CoefficientCells.cell_0 (r := r) (by simpa using hrlo) (by simpa using hrhi)
  refine ⟨?_,?_,?_,?_,?_⟩
  · norm_num [Mem,coeff,point]
  · norm_num [Mem,coeff,point]
  · simpa [Mem,coeff,div_eq_mul_inv] using he
  · simpa [Mem,coeff,div_eq_mul_inv] using hb
  · simpa [Mem,coeff,div_eq_mul_inv] using hc

/-- One positive-volume initial subbox and a continuum of fixed rates.
All 25 own-feedback endpoints are enclosed; this does not assert a path bound. -/
theorem endpoints {r : ℝ} {z : UncertainLag.State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z) :
    ∀ n≤25, BoxMem (boxes n) (stateTrace (fun _=>r) (fun _=>1/20)
      (fun _=>0) (fun _=>0) z n) :=
  IntervalPilot.endpoints (coeff_sound hrlo hrhi) hz

end LeanControls.IntervalPilotActual
#print axioms LeanControls.IntervalPilotActual.coeff_sound
#print axioms LeanControls.IntervalPilotActual.endpoints
