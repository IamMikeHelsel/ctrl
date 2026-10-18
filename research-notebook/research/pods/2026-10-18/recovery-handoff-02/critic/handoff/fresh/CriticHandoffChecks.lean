import DelayedWitness
import BrakingDelayedWitness
open Set LeanControls.DigitalHold
namespace IndependentHandoffCritic
example : (2*radius-(111/1000:ℝ))=1/20000 := by norm_num [radius]
example : (2*radius-(11/100:ℝ))=21/20000 := by norm_num [radius]
example : (1/2000:ℝ)+(1/1000:ℝ)>1/1000 := by norm_num
example : LeanControls.BrakingDelayedHold.startupLimit < (1/1000:ℝ) := by
 norm_num [LeanControls.BrakingDelayedHold.startupLimit]
example : LeanControls.BrakingDelayedHold.actualCommand (1/2000) LeanControls.BrakingDelayedHold.center
 (fun _ _ => LeanControls.BrakingDelayedHold.exampleReading) false (1/2000) = -121/100 := by
 norm_num [LeanControls.BrakingDelayedHold.actualCommand]
example : LeanControls.BrakingDelayedHold.actualCommand (1/2000) LeanControls.BrakingDelayedHold.center
 (fun _ _ => LeanControls.BrakingDelayedHold.exampleReading) true (1/2000) = 23/100 := by
 norm_num [LeanControls.BrakingDelayedHold.actualCommand,LeanControls.BrakingDelayedHold.center,
  LeanControls.BrakingDelayedHold.exampleReading,command,clip]
example : LeanControls.BrakingDelayedHold.Witness.state LeanControls.BrakingDelayedHold.Witness.delay 2 <
 LeanControls.BrakingDelayedHold.exampleReading 2 :=
 LeanControls.BrakingDelayedHold.Witness.nonzero_delay_and_changed_state.2
example : LeanControls.DelayedHold.Witness.state LeanControls.DelayedHold.Witness.delay 2 >
 LeanControls.DelayedHold.exampleReading 2 := LeanControls.DelayedHold.Witness.nonzero_delay_and_changed_state.2
example {d : ℝ} (hd : |d|≤1/100) : (-121/100:ℝ)+d≤-6/5 :=
 (LeanControls.BrakingDelayedHold.pending_braking_compatibility hd).2
example : ¬ ((-1:ℝ)+1/100≤-6/5) := by norm_num
end IndependentHandoffCritic
