import TaskContract

open Set
noncomputable section
namespace RobotMotion.TaskContract
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

def stepEvents : List QEvent := [(11/50,1/50)]
def stepReference := referenceState 0 (1/5) (realEvents stepEvents)

structure FixedPlant (r w : ℝ → ℝ) (f : ℝ → State) : Prop where
  ode : IsTrajectory 2 r (fun t => physicalInput 10 f stepReference
    (jerk (1/5) (realEvents stepEvents)) t+w t) f
  rateLower : ∀ t ∈ Icc 0 2, 80 ≤ r t
  rateUpper : ∀ t ∈ Icc 0 2, r t ≤ 120
  disturbance : ∀ t ∈ Icc 0 2, |w t| ≤ 1/100
  initial : ∀ i, |coordinates 0 (scaledError 10 f stepReference 0) i| ≤ 1/5000

theorem twenty_mm_task {r w : ℝ → ℝ} {f : ℝ → State} (plant : FixedPlant r w f) :
    PositionTask (1/5) (1/5) (11/50) 0 (1/50) 2 (1/5000) (fun t => f t 0) := by
  have result := checked_isolated_task (h:=1/5) (J:=15/2) (et:=11/50) (ed:=1/50)
    (s:=1/5) (tau:=11/50) (g0:=0) (a:=0) (g:=1/50) (D:=51/50) []
    (by norm_num [check,qGuardPoints,qRoots,qJerk]) (by simp [CompleteBy,realEvents]) (by simp [realEvents])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (σ:=10) (horizon:=2) (R:=1/5000) (W:=1/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [stepReference,stepEvents] using plant.ode)
    (by intro t ht; norm_num; exact plant.rateLower t ht)
    (by intro t ht; norm_num; exact plant.rateUpper t ht)
    plant.disturbance (by norm_num)
    (by simpa [stepReference,stepEvents] using plant.initial)
  simpa using result.2.1

theorem twenty_mm_progress {r w : ℝ → ℝ} {f : ℝ → State} (plant : FixedPlant r w f) :
    (49/5000:ℝ) ≤ f (31/50) 0 := by
  have hp := (twenty_mm_task plant).midpoint (by norm_num)
  norm_num [directed] at hp
  exact hp

theorem twenty_mm_arrival {r w : ℝ → ℝ} {f : ℝ → State} (plant : FixedPlant r w f) :
    ∀ t ∈ Icc (51/50:ℝ) 2, |f t 0-1/50| ≤ 1/5000 := by
  intro t ht
  exact (twenty_mm_task plant).arrival t ⟨by linarith [ht.1],ht.2⟩ (by norm_num; exact ht.1)

theorem twenty_mm_deadline {r w : ℝ → ℝ} {f : ℝ → State} (plant : FixedPlant r w f) :
    ∀ t ∈ Icc (3/2:ℝ) 2, |f t 0-1/50| ≤ 1/5000 := by
  intro t ht
  exact twenty_mm_arrival plant t ⟨by linarith [ht.1],ht.2⟩

/-- The specific halfway deadline fails the .2mm position requirement. -/
theorem halfway_deadline_impossible {r w : ℝ → ℝ} {f : ℝ → State}
    (plant : FixedPlant r w f) :
    (49/5000:ℝ) ≤ |f (31/50) 0-1/50| ∧ ¬ |f (31/50) 0-1/50| ≤ 1/5000 := by
  have hm := (twenty_mm_task plant).midpoint_error (by norm_num)
  norm_num at hm
  have hab := abs_le.mp hm
  have hd := neg_le_abs (f (31/50) 0-1/50)
  constructor <;> linarith

theorem fixed_step_guard : check (1/5) (15/2) 0 stepEvents = true := by
  norm_num [check,qGuardPoints,qRoots,qEventRoots,qJerk,qEventJerk,qH,stepEvents]
theorem fixed_step_admitted :
    (admit (1/5) (15/2) (initial 0) ⟨11/50,11/50,1/50⟩).events = stepEvents := by
  norm_num [admit,causal,initial,candidate,check,qGuardPoints,qRoots,qEventRoots,
    qJerk,qEventJerk,qH,stepEvents]
theorem fixed_peak_bound : (2*|1/50|/(1/5)^3:ℝ) = 5 := by norm_num
theorem fixed_deadline_margin : (11/50+4*(1/5):ℝ) = 51/50 ∧ (51/50:ℝ) ≤ 3/2 := by norm_num

/-- A future event is invisible in the current reference jet but cannot be erased. -/
theorem pending_event_witness :
    referenceJet 0 (1/5) [(1,1/50)] 0 = referenceJet 0 (1/5) [] 0 ∧
    position 0 (1/5) [(1,1/50)] (9/5) = 1/50 ∧
    ¬ CompleteBy (1/5) 0 [(1,1/50)] := by
  refine ⟨?_,?_,?_⟩
  · simpa using prefix_jet (by norm_num : (0:ℝ)<1/5)
      (by norm_num : (0:ℝ)≤1) 0 (1/50) [] (t:=0) (by norm_num)
  · norm_num [position,response,F0,P]
  · norm_num [CompleteBy]

theorem pending_event_guard : check (1/5) (15/2) 0 [(1,1/50)] = true := by
  norm_num [check,qGuardPoints,qRoots,qEventRoots,qJerk,qEventJerk,qH]

/-- The generic post-reference-rest tube is weaker than the benchmark rest limits. -/
theorem actual_rest_not_supplied :
    (1/1000:ℝ) < 8*10*(1/5000) ∧ (1/50:ℝ) < 64*10^2*(1/5000) := by norm_num

end RobotMotion.TaskContract
