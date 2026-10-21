import LeanControls.TravelSafety
import Mathlib.Tactic

noncomputable section
namespace CampaignS07InventorActive
open LeanControls Matrix
open LeanControls.SaturatedLag

abbrev core : State := ![29/20, -27/20, 37/20]
abbrev lifted : State := ![149/100, -139/100, 189/100]

theorem core_energy : TravelSafety.V core = 237409/20000 := by
  norm_num [TravelSafety.V, TravelSafety.P, core, BernsteinCertificate.energy,
    Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem lifted_energy : TravelSafety.V lifted = 6166449/500000 := by
  norm_num [TravelSafety.V, TravelSafety.P, lifted, BernsteinCertificate.energy,
    Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem strict_energy_separation : TravelSafety.V core < 12 ∧
    12 < TravelSafety.V lifted := by
  rw [core_energy, lifted_energy]
  norm_num

theorem actual_requests : input core = -11/10 ∧ input lifted = -11/10 := by
  norm_num [input, core, lifted]

theorem actual_clamps : RobustPD.saturate 1 (input core) = -1 ∧
    RobustPD.saturate 1 (input lifted) = -1 := by
  rw [actual_requests.1, actual_requests.2]
  norm_num [RobustPD.saturate]

theorem coordinate_lift : lifted =
    ![core 0 + 1/25, core 1 - 1/25, core 2 + 1/25] := by
  ext i
  fin_cases i <;> norm_num [core, lifted]

theorem strict_clipping : 1 < |input core| ∧ 1 < |input lifted| := by
  rw [actual_requests.1, actual_requests.2]
  norm_num

end CampaignS07InventorActive
#print axioms CampaignS07InventorActive.core_energy
#print axioms CampaignS07InventorActive.lifted_energy
#print axioms CampaignS07InventorActive.strict_energy_separation
#print axioms CampaignS07InventorActive.actual_requests
#print axioms CampaignS07InventorActive.actual_clamps
#print axioms CampaignS07InventorActive.coordinate_lift
#print axioms CampaignS07InventorActive.strict_clipping
