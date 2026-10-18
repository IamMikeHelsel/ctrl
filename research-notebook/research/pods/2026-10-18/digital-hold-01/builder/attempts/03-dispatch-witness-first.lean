module
public import DigitalHold
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
@[expose] public section
noncomputable section
namespace LeanControls.DigitalHold.DispatchWitness
open Set Filter

def switch : ℝ := 1/2000

def flow (t : ℝ) : State :=
  ![(t-switch)^2/2000-(t-switch)/8000+(1-Real.exp (-8*(t-switch)))/64000,
    (t-switch)/1000-(1-Real.exp (-8*(t-switch)))/8000,
    (1-Real.exp (-8*(t-switch)))/1000]

theorem flow_initial : flow switch = ![0,0,0] := by
  ext i
  fin_cases i <;> simp [flow]

theorem flow_ode (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => flow s i) (rhs 8 (1/1000) 0 (flow t) i) t := by
  have hh := (hasDerivAt_id t).sub_const switch
  have he := (hh.const_mul (-8)).exp
  fin_cases i
  · convert (((hh.pow 2).div_const 2000).sub (hh.div_const 8000)).add ((he.const_sub 1).div_const 64000) using 1
    · rfl
    · dsimp [flow,rhs]; ring
  · convert (hh.div_const 1000).sub ((he.const_sub 1).div_const 8000) using 1
    · rfl
    · dsimp [flow,rhs]; ring
  · convert (he.const_sub 1).div_const 1000 using 1
    · rfl
    · dsimp [flow,rhs]; ring

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
      · have heq : s=τ := by linarith [hs]
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

def state (t : ℝ) : State := if t ≤ switch then ![0,0,0] else flow t

def before (b : Bool) (t : ℝ) : Prop := if b then t < switch else t ≤ switch
instance (b : Bool) (t : ℝ) : Decidable (before b t) := inferInstanceAs (Decidable (if b then t < switch else t ≤ switch))

def stamp (b : Bool) (t : ℝ) : ℝ := if before b t then 0 else switch

def reading (b : Bool) (t : ℝ) : State := if before b t then ![0,0,0] else ![-1/8000,0,0]

theorem state_initial : state 0 = ![0,0,0] := by norm_num [state,switch]
theorem state_switch : state switch = ![0,0,0] := by simp [state]
theorem state_eq_flow {t : ℝ} (ht : switch ≤ t) : state t = flow t := by
  by_cases hh : t ≤ switch
  · have he : t=switch := le_antisymm hh ht
    simp [he,state,flow_initial]
  · simp [state,hh]

theorem state_continuous : Continuous state := by
  apply Continuous.if_le continuous_const ?_ continuous_id continuous_const
  · exact continuous_pi (fun i => continuous_iff_continuousAt.mpr (fun t => (flow_ode t i).continuousAt))
  · intro t ht
    simpa [ht] using flow_initial.symm

theorem witness_execution : Execution (1/1000) 0 state (fun _ _ => 8)
    (fun _ _ => 0) stamp reading := by
  constructor
  · exact state_continuous.continuousOn
  · intro b t ht
    cases b <;> dsimp [stamp,before] <;> split_ifs with hb <;> norm_num [switch] at hb ⊢ <;> linarith [ht.1,ht.2]
  · intro b t ht
    by_cases hb : before b t
    · simp [reading,stamp,hb,state_initial]
    · simp [reading,stamp,hb,state_switch]
      norm_num
  · intro b t ht; norm_num
  · intro b t ht; norm_num
  · intro t ht i
    have hj := right_join (hasDerivAt_const t (![0,0,0] i)) (flow_ode t i)
      (congrFun flow_initial.symm i)
    by_cases hb : t < switch
    · have hs : state t = ![0,0,0] := by simp [state,hb.le]
      simpa [state,reading,before,hb,hs,rhs,command,clip] using hj
    · have hs : state t = flow t := state_eq_flow (le_of_not_gt hb)
      simpa [state,reading,before,hb,hs,rhs,command,clip] using hj
  · intro t ht i
    have hj := left_join (hasDerivAt_const t (![0,0,0] i)) (flow_ode t i)
      (congrFun flow_initial.symm i)
    by_cases hb : t ≤ switch
    · have hs : state t = ![0,0,0] := by simp [state,hb]
      simpa [state,reading,before,hb,hs,rhs,command,clip] using hj
    · have hs : state t = flow t := state_eq_flow (le_of_lt (lt_of_not_ge hb))
      simpa [state,reading,before,hb,hs,rhs,command,clip] using hj

def schedule : Schedule where
  sample n := n/2000
  dispatch n := n/2000
  measurement n := if n=0 then ![0,0,0] else ![-1/8000,0,0]
  index b t := if before b t then 0 else 1

theorem witness_schedule : IsSchedule (1/1000) schedule stamp reading := by
  constructor
  · norm_num [schedule]
  · norm_num [schedule]
  · intro b; cases b <;> norm_num [schedule,before,switch]
  · intro n; dsimp [schedule]; exact ⟨by positivity,le_rfl⟩
  · intro m n hmn; dsimp [schedule]
    exact div_lt_div_of_pos_right (by exact_mod_cast hmn) (by norm_num)
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (2000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change (n:ℝ)/2000 ≤ T at hn
    change n < N
    have hh : (n:ℝ) < N := by linarith
    exact_mod_cast hh
  · intro t ht
    by_cases hb : t < switch
    · simp [schedule,before,hb,switch] at *
      exact ⟨ht.1,hb⟩
    · simp [schedule,before,hb]
      norm_num [switch] at hb
      exact ⟨by linarith,ht.2⟩
  · intro t ht
    by_cases hb : t ≤ switch
    · simp [schedule,before,hb,switch] at *
      exact ⟨ht.1,hb⟩
    · simp [schedule,before,hb]
      norm_num [switch] at hb
      exact ⟨by linarith,ht.2⟩
  · intro b t ht
    by_cases hb : before b t <;> simp [schedule,stamp,hb,switch]
  · intro b t ht
    by_cases hb : before b t <;> simp [schedule,reading,hb]

theorem two_cell_sampled_execution :
    IsSampledExecution (1/1000) 0 state (fun _ _ => 8) (fun _ _ => 0) stamp reading schedule ∧
    (∀ i, |coordinates 0 (state 0) i| ≤ radius) := by
  refine ⟨⟨witness_execution,witness_schedule⟩,?_⟩
  intro i
  rw [state_initial]
  fin_cases i <;> norm_num [coordinates,radius]

theorem command_jump : clip (command 0 (reading false switch)) = 0 ∧
    clip (command 0 (reading true switch)) = 1/1000 := by
  norm_num [reading,before,command,clip]

end LeanControls.DigitalHold.DispatchWitness
