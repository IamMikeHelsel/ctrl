import AdmissionInterface
noncomputable section
namespace CriticAdmission
open LeanControls.DigitalHold LeanControls.AdaptiveAdmission
open LeanControls.AdaptiveAdmission.Interface LeanControls.AdaptiveAdmission.Witness

def shiftedReading : State := translate (1/10) exampleReading
def shiftedState (t : ℝ) : State := translate (1/10) (state t)
def shiftedSchedule : Schedule := translateSchedule (1/10) LeanControls.AdaptiveAdmission.Witness.schedule

/-- A real translated finite execution meets the guard but starts above a fixed
absolute .15 position. This refutes an absolute clearance inference, not C3. -/
theorem translated_execution_rejects_absolute_clearance :
    Execution (1/1000) delay shiftedReading shiftedState (fun _ _ => 8)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => shiftedReading) ∧
    IsSchedule (1/1000) delay shiftedSchedule (fun _ _ => 0) (fun _ _ => shiftedReading) ∧
    shiftedSchedule.measurement 0 = shiftedReading ∧ Guard shiftedReading ∧
    (3/20 : ℝ) < shiftedState 0 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact execution_translation actual_execution (1/10)
  · exact schedule_translation actual_schedule (1/10)
  · rfl
  · exact (guard_translation (1/10) exampleReading).mpr (by norm_num [Guard,exampleReading])
  · norm_num [shiftedState,translate,state_initial,exampleReading]
end CriticAdmission
