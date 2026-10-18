module
public import ConstructiveHold
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructiveHold.Witness
open Set Filter DigitalHold
abbrev m : State := ClearanceAdmission.exampleReading
abbrev g := ClearanceAdmission.Witness.pending

theorem prefix_execution : ClearanceAdmission.Execution h h m g
    (fun _ _ => 8) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => m) := by
  constructor
  · exact (continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
      (ClearanceAdmission.Witness.pending_ode t i).continuousAt).continuousOn
  · intro b t ht
    exact ⟨le_rfl,ht.1,by have hh : t≤(1/2000:ℝ) := ht.2; linarith⟩
  · intro b t ht
    norm_num [g,ClearanceAdmission.Witness.pending,ClearanceAdmission.Witness.held,
      AdaptiveAdmission.Witness.held]
  · intro b t ht; norm_num
  · intro b t ht; norm_num
  · intro t ht i
    simpa only [ClearanceAdmission.actualCommand,ite_true,ht.2] using
      (ClearanceAdmission.Witness.pending_ode t i).hasDerivWithinAt (s := Ici t)
  · intro t ht i
    simpa only [ClearanceAdmission.actualCommand,Bool.false_eq_true,ite_false,ht.2,ite_true] using
      (ClearanceAdmission.Witness.pending_ode t i).hasDerivWithinAt (s := Iic t)

def rates (n : ℕ) : ℝ := if n=2 then 12 else 8
def errors (n : ℕ) : ℝ := if n=2 then 1/200 else 0
def noise (_ : ℕ) : State := ![1/2000,1/200,1/40]

theorem rates_bounded (n : ℕ) (_hn : 1≤n) : 8≤rates n ∧ rates n≤12 := by
  simp only [rates]; split_ifs <;> norm_num

theorem errors_bounded (n : ℕ) (_hn : 1≤n) : |errors n|≤1/100 := by
  simp only [errors]; split_ifs <;> norm_num

theorem noise_bounded (n : ℕ) : |noise n 0|≤1/1000 ∧ |noise n 1|≤1/100 ∧ |noise n 2|≤1/20 := by
  norm_num [noise]

def run : ℝ → State := state m g rates errors noise 3

def baseline : ℝ → State := state m g (fun _ => 8) (fun _ => 0) (fun _ _ => 0) 3

theorem changing_four_cell_contract :
    (∀ t ∈ Icc 0 h, run t=g t) ∧
    ClearanceAdmission.Execution (grid 4) h m run
      (field (fun _ _ => 8) rates) (field (fun _ _ => 0) errors) stamp (readings m noise run) ∧
    ClearanceAdmission.IsSchedule (grid 4) h (schedule m noise run) stamp (readings m noise run) ∧
    (schedule m noise run).measurement 0=m ∧
    ∀ t ∈ Icc 0 (grid 4), run t 0 ≤ 3/20-1277551/20100000000 := by
  exact finite_clearance prefix_execution rates_bounded errors_bounded noise_bounded 3
    (by norm_num [ClearanceAdmission.Guard,ClearancePolicy.Guard,m,ClearanceAdmission.exampleReading])

theorem matched_baseline_contract :
    (∀ t ∈ Icc 0 h, baseline t=g t) ∧
    ClearanceAdmission.Execution (grid 4) h m baseline
      (field (fun _ _ => 8) (fun _ => 8)) (field (fun _ _ => 0) (fun _ => 0)) stamp
      (readings m (fun _ _ => 0) baseline) ∧
    ClearanceAdmission.IsSchedule (grid 4) h (schedule m (fun _ _ => 0) baseline) stamp
      (readings m (fun _ _ => 0) baseline) ∧
    (schedule m (fun _ _ => 0) baseline).measurement 0=m ∧
    ∀ t ∈ Icc 0 (grid 4), baseline t 0 ≤ 3/20-1277551/20100000000 := by
  exact finite_clearance prefix_execution (by intros; norm_num) (by intros; norm_num)
    (by intros; norm_num) 3
    (by norm_num [ClearanceAdmission.Guard,ClearancePolicy.Guard,m,ClearanceAdmission.exampleReading])

theorem changed_startup_state : run h 2 < run 0 2 := by
  have hp := state_prefix m g rates errors noise 3 (t := h) le_rfl
  have hz := state_prefix m g rates errors noise 3 (t := 0) (by norm_num)
  have hh := ClearanceAdmission.Witness.nonzero_delay_and_changed_state.2
  rw [ClearanceAdmission.Witness.state_dispatch] at hh
  change state m g rates errors noise 3 h 2 < state m g rates errors noise 3 0 2
  rw [hp,hz]
  have h0 : g 0=m := by
    norm_num [g,m,ClearanceAdmission.exampleReading,ClearanceAdmission.Witness.pending,ClearanceAdmission.Witness.held,AdaptiveAdmission.Witness.held]
  rw [h0]
  exact hh

theorem actual_rate_and_error_jump :
    field (fun _ _ => 8) rates false (grid 2)=8 ∧
    field (fun _ _ => 8) rates true (grid 2)=12 ∧
    field (fun _ _ => 0) errors false (grid 2)=0 ∧
    field (fun _ _ => 0) errors true (grid 2)=1/200 := by
  norm_num [field,pendingSide,index,DelayedEntry.Witness.index,DelayedEntry.Witness.delay,grid,rates,errors]

theorem sensor_noise_is_nonzero :
    measure m noise run 1 0-run (grid 1) 0=1/2000 ∧
    measure m noise run 1 1-run (grid 1) 1=1/200 ∧
    measure m noise run 1 2-run (grid 1) 2=1/40 := by
  norm_num [measure,noise]

theorem first_reading_is_fixed : measure m noise run 0=m ∧
    (fun i => measure m noise run 0 i-run 0 i)=(fun i => m i-g 0 i) := by
  have hz := state_prefix m g rates errors noise 3 (t := 0) (by norm_num)
  constructor
  · rfl
  · funext i
    change m i-state m g rates errors noise 3 0 i=m i-g 0 i
    rw [hz]

theorem first_command_jump :
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center m) (readings m noise run) false h=-121/100 ∧
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center m) (readings m noise run) true h=3635533/12500000 := by
  have hi (b : Bool) : index b h=0 := DelayedEntry.Witness.startup_index b le_rfl
  norm_num [ClearanceAdmission.actualCommand,readings,hi,measure,ClearanceAdmission.center,
    ClearancePolicy.center,ClearancePolicy.policyRadius,ClearancePolicy.max3,ClearancePolicy.pair,
    ClearancePolicy.offsets,ClearancePolicy.error,WeightedEntry.weight,WeightedEntry.target,
    m,ClearanceAdmission.exampleReading,command,clip]

theorem second_dispatch_stamps : stamp false (grid 2)=0 ∧ stamp true (grid 2)=h := by
  norm_num [stamp,DelayedEntry.Witness.stamp,index,DelayedEntry.Witness.index,DelayedEntry.Witness.delay,grid]

theorem final_dispatch_stamps : stamp false (grid 4)=grid 2 ∧ stamp true (grid 4)=grid 3 := by
  norm_num [stamp,DelayedEntry.Witness.stamp,index,DelayedEntry.Witness.index,DelayedEntry.Witness.delay,grid]

theorem first_arrival_latency : h>0 ∧ h+h=1/1000 ∧ (1/1000:ℝ)+h>1/1000 := by norm_num

end LeanControls.ConstructiveHold.Witness
