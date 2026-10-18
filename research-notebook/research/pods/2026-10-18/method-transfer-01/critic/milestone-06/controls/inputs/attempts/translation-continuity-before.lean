module
public import AdaptiveWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.AdaptiveAdmission.Interface
open Set DigitalHold

def translate (δ : ℝ) (s : State) : State := ![s 0+δ,s 1,s 2]

theorem center_translation (δ : ℝ) (m : State) :
    center (translate δ m) = center m+δ := by dsimp [center,translate]; ring

theorem guard_translation (δ : ℝ) (m : State) : Guard (translate δ m) ↔ Guard m := by
  rfl

theorem coordinates_translation (δ : ℝ) (m s : State) :
    coordinates (center (translate δ m)) (translate δ s) = coordinates (center m) s := by
  ext i
  fin_cases i <;> dsimp [coordinates,center,translate] <;> ring

theorem command_translation (δ : ℝ) (m s : State) :
    command (center (translate δ m)) (translate δ s) = command (center m) s := by
  dsimp [command,center,translate]; ring

theorem actualCommand_translation (δ D : ℝ) (m : State)
    (read : Bool → ℝ → State) (b : Bool) (t : ℝ) :
    actualCommand D (center (translate δ m)) (fun b t => translate δ (read b t)) b t =
      actualCommand D (center m) read b t := by
  simp only [actualCommand,command_translation]

theorem rhs_translation (δ r u d : ℝ) (s : State) :
    rhs r u d (translate δ s) = rhs r u d s := by rfl

/-- Translation retains the same timestamps, rates, target errors, physical
velocity and acceleration. The position and measured center move together. -/
theorem execution_translation {H D : ℝ} {m : State}
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H D m f r d stamp read) (δ : ℝ) :
    Execution H D (translate δ m) (fun t => translate δ (f t)) r d stamp
      (fun b t => translate δ (read b t)) := by
  constructor
  · have hc : Continuous (translate δ) := by dsimp [translate]; fun_prop
    exact hc.comp_continuousOn ex.continuous
  · exact ex.causal
  · intro b t ht
    simpa [translate,add_sub_add_right_eq_sub] using ex.error b t ht
  · exact ex.rate
  · exact ex.target_error
  · intro t ht i
    rw [actualCommand_translation,rhs_translation]
    have hd := ex.right_ode t ht i
    fin_cases i
    · simpa [translate] using hd.add_const δ
    · simpa [translate] using hd
    · simpa [translate] using hd
  · intro t ht i
    rw [actualCommand_translation,rhs_translation]
    have hd := ex.left_ode t ht i
    fin_cases i
    · simpa [translate] using hd.add_const δ
    · simpa [translate] using hd
    · simpa [translate] using hd

def translateSchedule (δ : ℝ) (q : Schedule) : Schedule :=
  { q with measurement := fun n => translate δ (q.measurement n) }

theorem schedule_translation {H D : ℝ} {q : Schedule}
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H D q stamp read) (δ : ℝ) :
    IsSchedule H D (translateSchedule δ q) stamp (fun b t => translate δ (read b t)) := by
  constructor
  · exact hs.first_dispatch
  · exact hs.first_sample
  · exact hs.startup_index
  · exact hs.sample_order
  · exact hs.dispatch_order
  · exact hs.locally_finite
  · exact hs.right_cell
  · exact hs.left_cell
  · exact hs.timestamp
  · intro b t ht
    dsimp [translateSchedule]
    rw [hs.held_reading b t ht]

/-- Every allowed sensor error accepts this true-state sub-band. This says
nothing about whether a sampled detector ever observes such a true state. -/
theorem sensor_subband {m s : State}
    (hv : |s 1| ≤ 1/100) (ha : |s 2| ≤ 6/5)
    (ev : |m 1-s 1| ≤ 1/100) (ea : |m 2-s 2| ≤ 1/20) : Guard m := by
  have h1 := abs_le.mp hv
  have h2 := abs_le.mp ha
  have e1 := abs_le.mp ev
  have e2 := abs_le.mp ea
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem guard_nonempty (x : ℝ) : Guard ![x,0,-6/5] := by norm_num [Guard]

/-- Exact worst-case startup coordinate budgets used by the analytic screen. -/
theorem startup_budget_table :
    (1/1000:ℝ)+(613/20000)*(1/2000)+(1/50)/4+(5/4)/32 = 1803113/40000000 ∧
    (1/1000:ℝ)+(613/20000)*(1/2000)+(1/100+(13/10)*(1/2000))/4+(5/4)/32 = 1709613/40000000 ∧
    (1/1000:ℝ)+(613/20000)*(1/2000)+(1/100+(13/10)*(1/2000))/2+
      (1/20+(756/25)*(1/2000))/16+(1/50)/4+(5/4)/32 = 2178913/40000000 ∧
    radius-2178913/40000000 = 42087/40000000 ∧
    2*radius-(103/1000+8/1000) = 1/20000 := by norm_num [radius]

/-- The same nominal reading changes the center and certified travel tube.
The new upper tube is greater than 0.15; no clearance improvement is claimed. -/
theorem nominal_comparison :
    Guard exampleReading ∧ center exampleReading = 323/3200 ∧
    center exampleReading-radius = 3633/80000 ∧
    center exampleReading+radius = 12517/80000 ∧
    (3/20:ℝ) < 12517/80000 ∧
    (141/1600:ℝ)+radius = 2873/20000 := by
  norm_num [Guard,center,exampleReading,radius]

/-- A measured-speed cap of .03 would admit this sensor box, whose initial
true state already lies outside the claimed cube. This is a certificate
counterexample at time zero, not a later trajectory or hardware failure. -/
theorem wider_velocity_rejects_initial_cube :
    (let m : State := ![0,3/100,5/4]; let s : State := ![1/1000,4/100,13/10];
      |s 0-m 0| ≤ 1/1000 ∧ |s 1-m 1| ≤ 1/100 ∧ |s 2-m 2| ≤ 1/20 ∧
      radius < |coordinates (center m) s 2|) := by
  norm_num [coordinates,center,radius]

/-- A measured-acceleration cap of 1.4 has the same initial-cube obstruction. -/
theorem wider_acceleration_rejects_initial_cube :
    (let m : State := ![0,1/50,7/5]; let s : State := ![1/1000,3/100,29/20];
      |s 0-m 0| ≤ 1/1000 ∧ |s 1-m 1| ≤ 1/100 ∧ |s 2-m 2| ≤ 1/20 ∧
      radius < |coordinates (center m) s 2|) := by
  norm_num [coordinates,center,radius]

end LeanControls.AdaptiveAdmission.Interface
