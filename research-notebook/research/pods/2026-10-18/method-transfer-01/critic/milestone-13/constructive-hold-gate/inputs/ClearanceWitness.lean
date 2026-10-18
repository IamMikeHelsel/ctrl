module
public import ClearanceEntry
public import AdaptiveWitness
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
@[expose] public section
noncomputable section
namespace LeanControls.ClearanceAdmission.Witness
open Set Filter DigitalHold

def delay : ℝ := 1/2000

abbrev held := AdaptiveAdmission.Witness.held
open AdaptiveAdmission.Witness (held_initial held_ode right_join left_join)

def pending (t : ℝ) : State := held (-121/100) exampleReading t

def after (t : ℝ) : State := held (3635533/12500000) (pending delay) (t-delay)

theorem join_state : pending delay = after delay := by simp [after,held_initial]

theorem pending_ode (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => pending s i) (rhs 8 (-121/100) 0 (pending t) i) t := held_ode _ _ _ _

theorem after_ode (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => after s i) (rhs 8 (3635533/12500000) 0 (after t) i) t := by
  simpa [after,Function.comp_def] using (held_ode (3635533/12500000) (pending delay) (t-delay) i).comp t ((hasDerivAt_id t).sub_const delay)

def state (t : ℝ) : State := if t ≤ delay then pending t else after t

theorem state_initial : state 0 = exampleReading := by norm_num [state,pending,delay,held_initial]

theorem state_dispatch : state delay = pending delay := by simp [state]

theorem state_eq_after {t : ℝ} (ht : delay ≤ t) : state t = after t := by
  by_cases hh : t ≤ delay
  · have he : t=delay := le_antisymm hh ht
    simp [he,state,join_state]
  · simp [state,hh]

theorem state_continuous : Continuous state := by
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact continuous_pi (fun i => continuous_iff_continuousAt.mpr (fun t => (pending_ode t i).continuousAt))
  · exact continuous_pi (fun i => continuous_iff_continuousAt.mpr (fun t => (after_ode t i).continuousAt))
  · intro t ht
    simpa [ht] using join_state

theorem actual_execution : Execution (1/1000) delay exampleReading state (fun _ _ => 8)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => exampleReading) := by
  constructor
  · exact state_continuous.continuousOn
  · intro b t ht
    exact ⟨le_rfl,ht.1,by simpa only [sub_zero] using ht.2⟩
  · intro b t ht
    simp [state_initial]
  · intro b t ht; norm_num
  · intro b t ht; norm_num
  · intro t ht i
    have hj := right_join (pending_ode t i) (after_ode t i) (congrFun join_state i)
    by_cases hb : t < delay
    · have hs : state t = pending t := by simp [state,hb.le]
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · norm_num [actualCommand,hb,hs]
    · have hs : state t = after t := state_eq_after (le_of_not_gt hb)
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · norm_num [actualCommand,hb,hs,center,ClearancePolicy.center,ClearancePolicy.policyRadius,ClearancePolicy.max3,ClearancePolicy.pair,ClearancePolicy.offsets,ClearancePolicy.error,WeightedEntry.weight,WeightedEntry.target,exampleReading,command,clip]
  · intro t ht i
    have hj := left_join (pending_ode t i) (after_ode t i) (congrFun join_state i)
    by_cases hb : t ≤ delay
    · have hs : state t = pending t := by simp [state,hb]
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · norm_num [actualCommand,hb,hs]
    · have hs : state t = after t := state_eq_after (le_of_lt (lt_of_not_ge hb))
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · norm_num [actualCommand,hb,hs,center,ClearancePolicy.center,ClearancePolicy.policyRadius,ClearancePolicy.max3,ClearancePolicy.pair,ClearancePolicy.offsets,ClearancePolicy.error,WeightedEntry.weight,WeightedEntry.target,exampleReading,command,clip]

def schedule : Schedule where
  sample n := n/2000
  dispatch n := delay+n/2000
  measurement _ := exampleReading
  index _ _ := 0

theorem actual_schedule : IsSchedule (1/1000) delay schedule (fun _ _ => 0)
    (fun _ _ => exampleReading) := by
  constructor
  · norm_num [schedule]
  · norm_num [schedule]
  · intro b t ht; rfl
  · intro n; dsimp [schedule]
    exact ⟨by positivity,by norm_num [delay]⟩
  · intro m n hmn
    dsimp [schedule]
    have hh : (m:ℝ) < n := by exact_mod_cast hmn
    linarith
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (2000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change delay+(n:ℝ)/2000 ≤ T at hn
    change n < N
    have hh : (n:ℝ) < N := by norm_num [delay] at hn; linarith
    exact_mod_cast hh
  · intro t ht
    norm_num [schedule,delay] at *
    exact ht
  · intro t ht
    norm_num [schedule,delay] at *
    exact ht
  · intro b t ht; norm_num [schedule]
  · intro b t ht; rfl

/-- The dispatch is genuinely delayed and the state is not reset: the
acceleration at dispatch differs from its initially measured value. -/
theorem nonzero_delay_and_changed_state : 0 < delay ∧ state delay 2 < exampleReading 2 := by
  have he : Real.exp (-(1/250:ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [state_dispatch]
  norm_num [pending,held,AdaptiveAdmission.Witness.held,delay,exampleReading]

theorem actual_command_jump :
    actualCommand delay (center exampleReading) (fun _ _ => exampleReading) false delay = -121/100 ∧
    actualCommand delay (center exampleReading) (fun _ _ => exampleReading) true delay = 3635533/12500000 := by
  norm_num [actualCommand,center,ClearancePolicy.center,ClearancePolicy.policyRadius,ClearancePolicy.max3,ClearancePolicy.pair,ClearancePolicy.offsets,ClearancePolicy.error,WeightedEntry.weight,WeightedEntry.target,exampleReading,command,clip]

/-- One nominal positive-delay execution meets the new measured guard and
actual clearance theorem through the first millisecond. No later existence
or detector liveness is asserted. -/
theorem positive_delay_witness :
    0 < delay ∧
    Execution (1/1000) delay exampleReading state (fun _ _ => 8) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => exampleReading) ∧
    IsSchedule (1/1000) delay schedule (fun _ _ => 0) (fun _ _ => exampleReading) ∧
    schedule.sample 0 = 0 ∧ schedule.dispatch 0 = delay ∧ schedule.dispatch 1 = 1/1000 ∧
    (∀ t ∈ Icc 0 (1/1000:ℝ), state t 0 ≤ 3/20-1277551/20100000000) := by
  have hs := ClearanceEntry.sampled_clearance (by norm_num [delay]) (by norm_num [delay])
    (by norm_num [delay,startupLimit]) actual_execution actual_schedule rfl
    (by norm_num [Guard,ClearancePolicy.Guard,exampleReading])
  exact ⟨by norm_num [delay],actual_execution,actual_schedule,by norm_num [schedule],
    by norm_num [schedule],by norm_num [schedule,delay],fun t ht => (hs.2.2.1 t ht).2⟩

end LeanControls.ClearanceAdmission.Witness
