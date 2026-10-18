module
public import DirectSettling
public import MutationWitness
@[expose] public section
noncomputable section
namespace LeanControls.SettlingIndependentReview
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures DirectSettling

/-- The concrete eight-phase premise has an exact realization: its own
reference, nominal rate 96/s, and zero disturbance. -/
theorem exact_reference_plant :
    DirectReference.DirectPlant DirectReference.reference (fun _ _ => 96) (fun _ _ => 0) := by
  constructor
  · intro k hk
    constructor
    · exact (DirectReference.reference_continuous k).continuousOn
    · intro t ht i
      convert DirectReference.reference_derivatives k t i using 1 <;>
        fin_cases i <;> dsimp [physicalInput] <;> ring
  · intro k hk t ht; norm_num
  · intro k hk t ht; norm_num
  · intro k hk t ht; norm_num
  · exact DirectReference.reference_matches
  · exact DirectReference.reference_initial

theorem physical_equilibrium (H c : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r (fun t => holdInput 10 c (fun _ => ![c,0,0]) t + (0:ℝ))
      (fun _ => ![c,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro t ht i
    convert hasDerivAt_const t (![c,0,0] i) using 1 <;>
      fin_cases i <;> dsimp [holdInput,command,scaleState] <;> ring

/-- The positive hold-time interval is exercised at its included endpoint. -/
theorem concrete_composition_at_one_second :
    |(3/5:ℝ)-3/5| ≤ 17/320000 ∧ |(0:ℝ)| ≤ 17/4000 ∧ |(0:ℝ)| ≤ 17/50 := by
  have h := fixed_reference_then_hold (H:=1) exact_reference_plant (by norm_num)
    (physical_equilibrium 1 (3/5) (fun _ => 96))
    DirectReference.reference_endpoint.symm
    (by intro t ht; norm_num) (by intro t ht; norm_num) (by intro t ht; norm_num)
    1 (by norm_num)
  exact h

theorem concrete_composition_at_two_seconds :
    |(3/5:ℝ)-3/5| ≤ 1/1024000 ∧ |(0:ℝ)| ≤ 1/12800 ∧ |(0:ℝ)| ≤ 1/160 := by
  have h := fixed_reference_then_zero_disturbance_hold (H:=2) exact_reference_plant
    (by norm_num) (physical_equilibrium 2 (3/5) (fun _ => 96))
    DirectReference.reference_endpoint.symm
    (by intro t ht; norm_num) (by intro t ht; norm_num) 2 (by norm_num)
  exact h

theorem concrete_global_times :
    DirectReference.phaseStart 7 + DirectReference.duration 7 + 1 = (5/2:ℝ) ∧
    DirectReference.phaseStart 7 + DirectReference.duration 7 + 2 = (7/2:ℝ) := by
  rw [DirectReference.final_time]
  norm_num

/-- A nonzero initial physical state at sigma=10, with no finite exact rest. -/
def physicalNonrest (A t : ℝ) : State :=
  ![A*Real.exp (-40*t), -40*A*Real.exp (-40*t), 1600*A*Real.exp (-40*t)]

theorem physical_nonrest_trajectory (A H : ℝ) :
    IsTrajectory H (fun _ => 80)
      (fun t => holdInput 10 0 (physicalNonrest A) t+(0:ℝ)) (physicalNonrest A) := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [physicalNonrest] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-40:ℝ)).exp)
    fin_cases i
    · convert he.const_mul A using 1 <;> dsimp [physicalNonrest] <;> ring
    · convert he.const_mul (-40*A) using 1 <;> dsimp [physicalNonrest] <;> ring
    · convert he.const_mul (1600*A) using 1 <;>
        dsimp [physicalNonrest,holdInput,command,scaleState] <;> ring

theorem physical_nonrest_initial_cube {A : ℝ} (hA : 0 ≤ A) :
    ∀ i, |coordinates 0 (scaleState 10 (physicalNonrest A 0)) i| ≤ A := by
  intro i
  fin_cases i <;> simp [physicalNonrest,coordinates,scaleState,abs_of_nonneg hA] <;>
    ring_nf <;> simp [abs_of_nonneg hA,hA]

theorem physical_nonrest_tight_certificate :
    |physicalNonrest (1/5000) 2 0| ≤ 1/1024000 ∧
    |physicalNonrest (1/5000) 2 1| ≤ 1/12800 ∧
    |physicalNonrest (1/5000) 2 2| ≤ 1/160 := by
  simpa using two_seconds_actual_zero_disturbance (H:=2) (c:=0) (by norm_num)
    (physical_nonrest_trajectory (1/5000) 2)
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    (physical_nonrest_initial_cube (by norm_num)) 2 (by norm_num)

theorem physical_nonrest_not_rest (t : ℝ) : physicalNonrest (1/5000) t 1 ≠ 0 := by
  dsimp [physicalNonrest]
  exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _))

theorem nonzero_initial_velocity_retained :
    physicalNonrest (1/5000) 0 1 = -(1/125:ℝ) := by
  norm_num [physicalNonrest]

/-- Positive constant physical bias permits exact rest, even with changing rate. -/
theorem physical_biased_equilibrium (H : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r
      (fun t => holdInput 10 0 (fun _ => ![1/80000,0,0]) t + (1/100:ℝ))
      (fun _ => ![1/80000,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro t ht i
    convert hasDerivAt_const t ((![1/80000,0,0] : State) i) using 1 <;>
      fin_cases i <;> dsimp [holdInput,command,scaleState] <;> ring

theorem biased_zero_speed_refutes_floor_as_lower_bound :
    ¬ (3/1000:ℝ) ≤ |(![1/80000,0,0] : State) 1| := by norm_num

/-- The sharp first-coordinate boundary blocks the proposed faster exponent. -/
theorem faster_face_exact :
    transformedRHS 8 0 (![1,9/10,4/5] : State) 0 = -(2/5:ℝ) := by
  norm_num [transformedRHS]

theorem missing_floor_exact :
    transformedRHS 8 1 (![0,0,0] : State) 2 = (1/2:ℝ) := by
  norm_num [transformedRHS]

end LeanControls.SettlingIndependentReview
