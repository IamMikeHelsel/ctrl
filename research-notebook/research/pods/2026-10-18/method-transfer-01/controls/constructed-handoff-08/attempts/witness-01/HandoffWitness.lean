module
public import HandoffAssembly
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructedHandoff.Witness
open Set Filter DigitalHold ConstructiveHold DetectorBridge DetectorSampling
abbrev early := DetectorReview.earlyState
def oldReads (n : ℕ) : State := early (sample n)
abbrev rates := ConstructiveHold.Witness.rates
abbrev errors := ConstructiveHold.Witness.errors
abbrev noise := ConstructiveHold.Witness.noise

theorem readings_valid : Readings early oldReads := by
  intro n hn; simp [SensorBox,oldReads]

theorem first_632 : First oldReads 632 := by
  constructor
  · norm_num [ClearancePolicy.Guard,oldReads,early,DetectorReview.earlyState,UncertainLag.heldSolution,sample]
  · intro j hj hg
    have hv := (abs_le.mp hg.2.1).2
    have hjr : (j:ℝ)≤631 := by exact_mod_cast (show j≤631 by omega)
    norm_num [oldReads,early,DetectorReview.earlyState,UncertainLag.heldSolution,sample] at hv
    linarith

theorem combined : Assembly early (fun _ => 8) (fun _ => -6/5) (fun _ => 8) (fun _ => -6/5)
    oldReads 632 4 rates errors noise :=
  assemble DetectorReview.early_execution readings_valid (by norm_num) first_632 (by norm_num)
    ConstructiveHold.Witness.rates_bounded ConstructiveHold.Witness.errors_bounded ConstructiveHold.Witness.noise_bounded

def run := trajectory early oldReads 632 4 rates errors noise
def localHold := hold early oldReads 632 4 rates errors noise

theorem exact_times : grid 632=79/250 ∧ grid 632+h=633/2000 ∧ grid 632+grid 4=159/500 := by
  norm_num [grid]

theorem positive_arrival : run (grid 632+h) 1=51/5000 ∧ 0<run (grid 632+h) 1 ∧ grid 632+h<13/40 := by
  have hp := combined.prefix_eq (grid 632+h) ⟨by norm_num [grid],le_rfl⟩
  change trajectory early oldReads 632 4 rates errors noise (grid 632+h) 1=_ ∧ _
  rw [hp]
  norm_num [early,DetectorReview.earlyState,UncertainLag.heldSolution,grid]

theorem physical_prefix_target :
    prefixError (fun _ : ℝ => -6/5) (grid 632) false h=1/100 ∧
    (-121/100:ℝ)+prefixError (fun _ : ℝ => -6/5) (grid 632) false h=-6/5 := by
  norm_num [prefixError]

theorem command_jump :
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center (oldReads 632))
      (readings (oldReads 632) noise localHold) false h=-121/100 ∧
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center (oldReads 632))
      (readings (oldReads 632) noise localHold) true h=2783033/12500000 := by
  have hi (b : Bool) : index b h=0 := DelayedEntry.Witness.startup_index b le_rfl
  norm_num [ClearanceAdmission.actualCommand,readings,hi,ConstructiveHold.measure,ClearanceAdmission.center,
    ClearancePolicy.center,ClearancePolicy.policyRadius,ClearancePolicy.max3,ClearancePolicy.pair,
    ClearancePolicy.offsets,ClearancePolicy.error,WeightedEntry.weight,WeightedEntry.target,
    oldReads,early,DetectorReview.earlyState,UncertainLag.heldSolution,sample,command,clip]

theorem shared_arrival_acceleration : localHold h 2=-6/5 ∧ run (grid 632+h) 2=-6/5 := by
  have hp := state_prefix (oldReads 632) (pending early (grid 632)) rates errors noise 3 (t:=h) le_rfl
  have hg := combined.prefix_eq (grid 632+h) ⟨by norm_num [grid],le_rfl⟩
  constructor
  · change state (oldReads 632) (pending early (grid 632)) rates errors noise 3 h 2=_
    rw [hp]
    norm_num [pending,early,DetectorReview.earlyState,UncertainLag.heldSolution]
  · change trajectory early oldReads 632 4 rates errors noise (grid 632+h) 2=_
    rw [hg]
    norm_num [early,DetectorReview.earlyState,UncertainLag.heldSolution]

theorem fresh_next_reading :
    newReadings oldReads localHold 632 noise 633 2-oldReads 633 2=1/40 := by
  have hp := shared_arrival_acceleration.1
  have hg : grid 1=h := by norm_num [grid]
  norm_num [newReadings,ConstructiveHold.measure,hg,noise,ConstructiveHold.Witness.noise,hp,
    oldReads,early,DetectorReview.earlyState,UncertainLag.heldSolution]

theorem actual_rate_change :
    field (prefixRate (fun _ : ℝ => 8) (grid 632)) rates false (grid 2)=8 ∧
    field (prefixRate (fun _ : ℝ => 8) (grid 632)) rates true (grid 2)=12 := by
  norm_num [field,pendingSide,prefixRate,index,DelayedEntry.Witness.index,DelayedEntry.Witness.delay,grid,rates,ConstructiveHold.Witness.rates]

theorem absolute_dispatch_stamps :
    grid 632+stamp false (grid 2)=grid 632 ∧
    grid 632+stamp true (grid 2)=grid 633 := by
  rw [ConstructiveHold.Witness.second_dispatch_stamps.1,ConstructiveHold.Witness.second_dispatch_stamps.2]
  norm_num [grid]

theorem first_decision_retained : First (newReadings oldReads localHold 632 noise) 632 :=
  new_readings_first first_632

end LeanControls.ConstructedHandoff.Witness
