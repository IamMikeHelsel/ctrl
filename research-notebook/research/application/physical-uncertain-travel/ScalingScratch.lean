import LeanControls.PhysicalTravel
noncomputable section
namespace LeanControls.PhysicalScalingScratch
open SaturatedLag (State)
open PhysicalTravel (scaleFactors normalizeState rescaleState normalizedDurations normalizedDisturbance input vectorField)
def rateVectorField (r u : ℝ) (z : State) : State := ![z 1, z 2, r * (u-z 2)]
theorem time_constant_interval {tau0 tau : ℝ} (htau0 : 0 < tau0) (htau : 0 < tau)
    (hrlo : 9 / 10 ≤ tau0 / tau) (hrhi : tau0 / tau ≤ 11 / 10) :
    10 / 11 ≤ tau / tau0 ∧ tau / tau0 ≤ 10 / 9 := by
  constructor
  · apply (le_div_iff₀ htau0).mpr
    have h := (div_le_iff₀ htau).mp hrhi
    nlinarith
  · apply (div_le_iff₀ htau0).mpr
    have h := (le_div_iff₀ htau).mp hrlo
    nlinarith

/-- The physical derivative retains the actual lag `tau`; it is not replaced
by the nominal normalization constant `tau0`. -/
theorem vectorField_rescale {tau0 tau U : ℝ} (htau0 : 0 < tau0) (htau : 0 < tau)
    (u : ℝ) (z : State) (i : Fin 3) :
    scaleFactors tau0 U i * (rateVectorField (tau0 / tau) u z i / tau0) =
      vectorField tau (U * u) (rescaleState tau0 U z) i := by
  have ht0 : tau0 ≠ 0 := ne_of_gt htau0
  have ht : tau ≠ 0 := ne_of_gt htau
  fin_cases i <;>
    simp [scaleFactors, rateVectorField, vectorField, rescaleState] <;>
    field_simp <;> ring


end LeanControls.PhysicalScalingScratch
