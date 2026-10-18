module
public import DelayedHold
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
@[expose] public section
noncomputable section
namespace LeanControls.DelayedHold.Witness
open Set Filter DigitalHold

def delay : ℝ := 1/2000

def held (u : ℝ) (z : State) (t : ℝ) : State :=
  ![z 0+t*z 1+u*t^2/2+(z 2-u)*(t/8-(1-Real.exp (-8*t))/64),
    z 1+u*t+(z 2-u)*(1-Real.exp (-8*t))/8,
    u+(z 2-u)*Real.exp (-8*t)]

theorem held_initial (u : ℝ) (z : State) : held u z 0 = z := by
  ext i
  fin_cases i <;> norm_num [held]

theorem held_ode (u : ℝ) (z : State) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => held u z s i) (rhs 8 u 0 (held u z t) i) t := by
  have he := ((hasDerivAt_id t).const_mul (-8)).exp
  fin_cases i
  · convert ((((hasDerivAt_id t).mul_const (z 1)).const_add (z 0)).add
      ((((hasDerivAt_id t).pow 2).const_mul u).div_const 2)).add
      ((((hasDerivAt_id t).div_const 8).sub ((he.const_sub 1).div_const 64)).const_mul (z 2-u)) using 1
    · rfl
    · dsimp [held,rhs]; ring
  · convert (((hasDerivAt_id t).const_mul u).const_add (z 1)).add
      (((he.const_sub 1).const_mul (z 2-u)).div_const 8) using 1
    · rfl
    · dsimp [held,rhs]; ring
  · convert (he.const_mul (z 2-u)).const_add u using 1
    · rfl
    · dsimp [held,rhs]; ring

def pending (t : ℝ) : State := held (-1) exampleReading t

def after (t : ℝ) : State := held (23/100) (pending delay) (t-delay)

theorem join_state : pending delay = after delay := by simp [after,held_initial]

theorem pending_ode (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => pending s i) (rhs 8 (-1) 0 (pending t) i) t := held_ode _ _ _ _

theorem after_ode (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => after s i) (rhs 8 (23/100) 0 (after t) i) t := by
  simpa [after,Function.comp_def] using (held_ode (23/100) (pending delay) (t-delay) i).comp t ((hasDerivAt_id t).sub_const delay)

theorem right_join {f g : ℝ → ℝ} {df dg t τ : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (he : f τ=g τ) :
    HasDerivWithinAt (fun s => if s ≤ τ then f s else g s)
      (if t < τ then df else dg) (Ici t) t := by
  by_cases ht : t < τ
  · rw [if_pos ht]
    apply (hf.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [if_pos (le_of_lt hs)]
  · rw [if_neg ht]
    have hge : τ ≤ t := le_of_not_gt ht
    apply hg.hasDerivWithinAt.congr_of_mem
    · intro s hs
      by_cases hst : s ≤ τ
      · have heq : s=τ := by change t ≤ s at hs; linarith
        simp [heq,he]
      · simp [hst]
    · exact le_rfl

theorem left_join {f g : ℝ → ℝ} {df dg t τ : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) (he : f τ=g τ) :
    HasDerivWithinAt (fun s => if s ≤ τ then f s else g s)
      (if t ≤ τ then df else dg) (Iic t) t := by
  by_cases ht : t ≤ τ
  · rw [if_pos ht]
    apply hf.hasDerivWithinAt.congr_of_mem
    · intro s hs
      simp only [if_pos (hs.trans ht)]
    · exact le_rfl
  · rw [if_neg ht]
    apply (hg.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Ioi_mem_nhds (lt_of_not_ge ht)] with s hs
    simp only [if_neg (not_le_of_gt hs)]


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

theorem actual_execution : Execution (1/1000) delay state (fun _ _ => 8)
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
      · norm_num [actualCommand,hb,hs,center,exampleReading,command,clip]
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
      · norm_num [actualCommand,hb,hs,center,exampleReading,command,clip]

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
theorem nonzero_delay_and_changed_state : 0 < delay ∧ state delay 2 > exampleReading 2 := by
  have he : Real.exp (-(1/250:ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [state_dispatch]
  norm_num [pending,held,delay,exampleReading]

theorem actual_command_jump :
    actualCommand delay center (fun _ _ => exampleReading) false delay = -1 ∧
    actualCommand delay center (fun _ _ => exampleReading) true delay = 23/100 := by
  norm_num [actualCommand,center,exampleReading,command,clip]

/-- A positive-delay supplied execution meets every premise, using the old
reading unchanged at dispatch. Its first reading reaches age 1 ms at H. -/
theorem positive_delay_witness :
    0 < delay ∧
    Execution (1/1000) delay state (fun _ _ => 8) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => exampleReading) ∧
    IsSchedule (1/1000) delay schedule (fun _ _ => 0) (fun _ _ => exampleReading) ∧
    schedule.sample 0 = 0 ∧ schedule.dispatch 0 = delay ∧ schedule.dispatch 1 = 1/1000 ∧
    (∀ t ∈ Icc 0 (1/1000:ℝ), ∀ i, |coordinates center (state t) i| ≤ radius) := by
  have hs := delayed_sampled_hold (by norm_num [delay]) (by norm_num [delay])
    (by norm_num [delay,startupLimit]) actual_execution actual_schedule rfl
  exact ⟨by norm_num [delay],actual_execution,actual_schedule,by norm_num [schedule],
    by norm_num [schedule],by norm_num [schedule,delay],hs.2.1⟩

end LeanControls.DelayedHold.Witness
