module
public import DelayedEntry
public import AdaptiveWitness
public import Mathlib.Algebra.Order.Floor.Semiring
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.DelayedEntry.Witness
open Set Filter DigitalHold WeightedEntry

def delay : ℝ := 1/2000
def reading (c : ℝ) : State := ![c,0,0]
def pending (c t : ℝ) : State := AdaptiveAdmission.Witness.held (-121/100) (reading c) (t-delay)
def state (c t : ℝ) : State := if t ≤ delay then pending c t else reading c

theorem selected_center (c : ℝ) : AdaptiveAdmission.center (reading c)=c := by
  norm_num [AdaptiveAdmission.center,reading]

theorem pending_ode (c t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => pending c s i) (rhs 8 (-121/100) 0 (pending c t) i) t := by
  simpa [pending,Function.comp_def] using
    (AdaptiveAdmission.Witness.held_ode (-121/100) (reading c) (t-delay) i).comp t
      ((hasDerivAt_id t).sub_const delay)

theorem join_state (c : ℝ) : pending c delay=reading c := by
  simp [pending,AdaptiveAdmission.Witness.held_initial]

theorem state_after (c : ℝ) {t : ℝ} (ht : delay ≤ t) : state c t=reading c := by
  by_cases he : t ≤ delay
  · have ht' : t=delay := le_antisymm he ht
    simp [state,ht',join_state]
  · simp [state,he]

theorem state_continuous (c : ℝ) : Continuous (state c) := by
  refine Continuous.if_le ?_ continuous_const continuous_id continuous_const ?_
  · exact continuous_pi (fun i => continuous_iff_continuousAt.mpr (fun t => (pending_ode c t i).continuousAt))
  · intro t ht
    simpa [ht] using join_state c

/-- Prepared small initial motion fits the sensor box of the equilibrium
reading. This is not the nominal braking capture or a general existence proof. -/
theorem initial_sensor_box (c : ℝ) :
    |reading c 0-state c 0 0| ≤ 1/1000 ∧
    |reading c 1-state c 0 1| ≤ 1/100 ∧
    |reading c 2-state c 0 2| ≤ 1/20 := by
  have hu := Real.exp_bound_div_one_sub_of_interval (x := (1:ℝ)/250)
    (by norm_num) (by norm_num)
  have hl : 1 ≤ Real.exp ((1:ℝ)/250) := Real.one_le_exp_iff.mpr (by norm_num)
  norm_num at hu
  refine ⟨abs_le.mpr ?_,abs_le.mpr ?_,abs_le.mpr ?_⟩ <;>
    constructor <;> norm_num [state,pending,delay,reading,AdaptiveAdmission.Witness.held] <;> linarith

def index (b : Bool) (t : ℝ) : ℕ :=
  if b then Nat.floor (2000*(t-delay)) else Nat.ceil (2000*(t-delay))-1
def stamp (b : Bool) (t : ℝ) : ℝ := (index b t : ℝ)/2000

theorem startup_index (b : Bool) {t : ℝ} (ht : t ≤ delay) : index b t=0 := by
  have h0 : (2000:ℝ)*(t-delay) ≤ 0 := by linarith
  cases b
  · simp [index,Nat.ceil_eq_zero.mpr h0]
  · simp [index,Nat.floor_eq_zero.mpr (show (2000:ℝ)*(t-delay)<1 by linarith)]

theorem right_cell {t : ℝ} (ht : delay ≤ t) :
    delay+(index true t : ℝ)/2000 ≤ t ∧
    t < delay+((index true t+1 : ℕ):ℝ)/2000 := by
  have hlo := Nat.floor_le (show 0 ≤ (2000:ℝ)*(t-delay) by linarith)
  have hhi := Nat.lt_floor_add_one ((2000:ℝ)*(t-delay))
  norm_num [index,Nat.cast_add] at *
  constructor <;> linarith

theorem left_cell {t : ℝ} (ht : delay < t) :
    delay+(index false t : ℝ)/2000 < t ∧
    t ≤ delay+((index false t+1 : ℕ):ℝ)/2000 := by
  have hpos : 1 ≤ Nat.ceil ((2000:ℝ)*(t-delay)) := Nat.one_le_ceil_iff.mpr (by linarith)
  have hn : Nat.ceil ((2000:ℝ)*(t-delay)) ≠ 0 := by omega
  have hh := (Nat.ceil_eq_iff hn).mp (rfl : Nat.ceil ((2000:ℝ)*(t-delay))=Nat.ceil ((2000:ℝ)*(t-delay)))
  have he : Nat.ceil ((2000:ℝ)*(t-delay))-1+1=Nat.ceil ((2000:ℝ)*(t-delay)) := Nat.sub_add_cancel hpos
  have her : ((Nat.ceil ((2000:ℝ)*(t-delay))-1:ℕ):ℝ)+1=(Nat.ceil ((2000:ℝ)*(t-delay)):ℝ) := by
    exact_mod_cast he
  norm_num [index] at *
  rw [her]
  constructor <;> linarith

theorem stamp_age {t : ℝ} (ht : 0 ≤ t) (b : Bool) :
    0 ≤ stamp b t ∧ stamp b t ≤ t ∧ t-stamp b t ≤ 1/1000 := by
  have hnonneg : 0 ≤ stamp b t := by dsimp [stamp]; positivity
  refine ⟨hnonneg,?_⟩
  by_cases hpre : t ≤ delay
  · rw [stamp,startup_index b hpre]
    norm_num
    norm_num [delay] at hpre
    exact ⟨ht,by linarith⟩
  · cases b
    · have hh := left_cell (lt_of_not_ge hpre)
      norm_num [Nat.cast_add,delay] at hh
      dsimp [stamp]
      constructor <;> linarith
    · have hh := right_cell (le_of_not_ge hpre)
      norm_num [Nat.cast_add,delay] at hh
      dsimp [stamp]
      constructor <;> linarith

theorem sample_sensor_box (c : ℝ) (b : Bool) (t : ℝ) :
    |reading c 0-state c (stamp b t) 0| ≤ 1/1000 ∧
    |reading c 1-state c (stamp b t) 1| ≤ 1/100 ∧
    |reading c 2-state c (stamp b t) 2| ≤ 1/20 := by
  by_cases hzero : index b t=0
  · simpa [stamp,hzero] using initial_sensor_box c
  · have hn : 1 ≤ index b t := by omega
    have hs : delay ≤ stamp b t := by
      dsimp [delay,stamp]
      have hh : (1:ℝ) ≤ index b t := by exact_mod_cast hn
      linarith
    rw [state_after c hs]
    norm_num

def schedule (c : ℝ) : Schedule where
  sample n := n/2000
  dispatch n := delay+n/2000
  measurement _ := reading c
  index := index

theorem actual_schedule (H c : ℝ) :
    AdaptiveAdmission.IsSchedule H delay (schedule c) stamp (fun _ _ => reading c) := by
  constructor
  · norm_num [schedule]
  · norm_num [schedule]
  · intro b t ht
    exact startup_index b ht.2
  · intro n
    dsimp [schedule]
    exact ⟨by positivity,by norm_num [delay]⟩
  · intro m n hmn
    dsimp [schedule]
    have hh : (m:ℝ)<n := by exact_mod_cast hmn
    linarith
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (2000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change delay+(n:ℝ)/2000 ≤ T at hn
    change n<N
    have hh : (n:ℝ)<N := by norm_num [delay] at hn; linarith
    exact_mod_cast hh
  · intro t ht
    exact right_cell ht.1
  · intro t ht
    exact left_cell ht.1
  · intro b t ht
    rfl
  · intro b t ht
    rfl

/-- A positive-delay, nonconstant startup followed by exact equilibrium.
Original samples are n/2000 and dispatches are delay+n/2000 for all n. -/
theorem actual_execution (H c : ℝ) :
    AdaptiveAdmission.Execution H delay (reading c) (state c) (fun _ _ => 8)
      (fun _ _ => 0) stamp (fun _ _ => reading c) := by
  constructor
  · exact (state_continuous c).continuousOn
  · intro b t ht
    exact stamp_age ht.1 b
  · intro b t ht
    exact sample_sensor_box c b t
  · intro b t ht
    norm_num
  · intro b t ht
    norm_num
  · intro t ht i
    have hj := AdaptiveAdmission.Witness.right_join (pending_ode c t i)
      (hasDerivAt_const t (reading c i)) (congrFun (join_state c) i)
    by_cases hb : t < delay
    · have hs : state c t=pending c t := by simp [state,hb.le]
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · simp [AdaptiveAdmission.actualCommand,hb,hs]
    · have hs := state_after c (le_of_not_gt hb)
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · fin_cases i <;> norm_num [AdaptiveAdmission.actualCommand,hb,hs,selected_center,AdaptiveAdmission.center,command,reading,clip,rhs]
  · intro t ht i
    have hj := AdaptiveAdmission.Witness.left_join (pending_ode c t i)
      (hasDerivAt_const t (reading c i)) (congrFun (join_state c) i)
    by_cases hb : t ≤ delay
    · have hs : state c t=pending c t := by simp [state,hb]
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · simp [AdaptiveAdmission.actualCommand,hb,hs]
    · have hs := state_after c (le_of_lt (lt_of_not_ge hb))
      convert hj using 1
      · funext s; dsimp [state]; split_ifs <;> rfl
      · fin_cases i <;> norm_num [AdaptiveAdmission.actualCommand,hb,hs,selected_center,AdaptiveAdmission.center,command,reading,clip,rhs]

theorem nonconstant_startup (c : ℝ) : 0 < delay ∧ 0 < state c 0 2 ∧ state c delay=reading c := by
  have he : 1 < Real.exp ((1:ℝ)/250) := Real.one_lt_exp_iff.mpr (by norm_num)
  refine ⟨by norm_num [delay],?_,state_after c le_rfl⟩
  norm_num [state,pending,delay,reading,AdaptiveAdmission.Witness.held]

theorem dispatch_command_sides (c : ℝ) :
    AdaptiveAdmission.actualCommand delay (AdaptiveAdmission.center (reading c))
      (fun _ _ => reading c) false delay = -121/100 ∧
    AdaptiveAdmission.actualCommand delay (AdaptiveAdmission.center (reading c))
      (fun _ _ => reading c) true delay = 0 := by
  norm_num [AdaptiveAdmission.actualCommand,selected_center,AdaptiveAdmission.center,command,reading,clip]

/-- The .111 budget is the digital feedback mismatch. The actual pending
command has a larger mismatch on this genuine execution at time zero. -/
theorem pending_mismatch_is_not_digital_budget (c : ℝ) :
    residual < |AdaptiveAdmission.actualMismatch delay (reading c) (state c)
      (fun _ _ => 0) (fun _ _ => reading c) false 0| := by
  have hs := initial_sensor_box c
  have hm := measurement_cost (c := c) hs.1 hs.2.1 hs.2.2
  have hc : |command c (state c 0)| ≤ 93/1000 := by
    have hz : command c (reading c)=0 := by norm_num [command,reading]
    rw [hz,zero_sub,abs_neg] at hm
    exact hm
  have hh := abs_le.mp hc
  have hn := neg_le_abs (AdaptiveAdmission.actualMismatch delay (reading c) (state c)
    (fun _ _ => 0) (fun _ _ => reading c) false 0)
  norm_num [AdaptiveAdmission.actualMismatch,AdaptiveAdmission.actualCommand,selected_center,delay,residual] at hn ⊢
  linarith

/-- This is a long-horizon nonvacuity witness with positive delay. Its small
prepared initial state is already near the target, not a capture experiment. -/
theorem six_second_instance (c : ℝ) :
    (∀ t ∈ Icc (delay+entryTime) 6,
      weightedRadius (coordinates c (state c t)) ≤ target) ∧
    0 < delay ∧ 0 < state c 0 2 := by
  have hh := delayed_sampled_finite_entry
    (by norm_num [delay] : 0 ≤ delay)
    (by norm_num [delay,entryTime] : delay+entryTime ≤ (6:ℝ))
    (by norm_num [delay,AdaptiveAdmission.startupLimit])
    (actual_execution 6 c) (actual_schedule 6 c) rfl
    (by norm_num [AdaptiveAdmission.Guard,reading])
  refine ⟨?_,(nonconstant_startup c).1,(nonconstant_startup c).2.1⟩
  intro t ht
  simpa only [selected_center] using (hh.2.2.2 t ht).1

/-- Omitting D from this submitted envelope deadline is false. This is an
exact envelope check, not a lower bound on actual settling time. -/
theorem deadline_requires_delay : target < envelope delay entryTime := by
  norm_num [envelope,delay,entryTime,target,radius,drift]

/-- Resetting the retained physical stamp at dispatch creates a negative
sample time. The theorem and witness do not perform this reset. -/
theorem illegal_reset_makes_negative_stamp : stamp false delay-delay < 0 := by
  norm_num [stamp,startup_index false le_rfl,delay]

/-- A larger aggregate residual fails this face test. This does not assert
that the selected tuple occurs on a sampled execution. -/
theorem wider_residual_breaks_face :
    0 < transformedRHS 12 (3/25) ![-(51/50)*target,(101/100)*target,target] 2 := by
  norm_num [transformedRHS,target]

end LeanControls.DelayedEntry.Witness
