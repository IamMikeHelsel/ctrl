import PhysicalArrival
import QuadraticTrajectory

open Set
noncomputable section
namespace RobotMotion.FIRHold
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking
open LeanControls.Settling LeanControls.QuadraticHold
open AccelerationAdmission
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Restrict and translate the clock of the same actual trajectory. -/
theorem trajectory_shift {H t0 : ℝ} (ht0 : 0 ≤ t0)
    {r b : ℝ → ℝ} {f : ℝ → State} (hf : IsTrajectory H r b f) :
    IsTrajectory (H-t0) (fun s => r (t0+s)) (fun s => b (t0+s))
      (fun s => f (t0+s)) := by
  constructor
  · exact hf.continuous.comp (continuous_const.add continuous_id).continuousOn
      (by intro s hs; constructor <;> linarith [hs.1,hs.2])
  · intro s hs i
    have ht : t0+s ∈ Ioo 0 H := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    convert (hf.ode (t0+s) ht i).comp s ((hasDerivAt_id s).const_add t0) using 1 <;>
      simp only [Function.comp_def,mul_one]

/-- A constant reference tail changes only the formula used for the controller.
The state remains the original f(t0+s), including the inherited endpoint. -/
theorem constant_tail_hold {H t0 c : ℝ} (ht0 : 0 ≤ t0)
    {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => physicalInput 10 f q j t+w t) f)
    (hq : ∀ t ∈ Icc t0 H, q t = ![c,0,0] ∧ j t = 0) :
    IsTrajectory (H-t0) (fun s => r (t0+s))
      (fun s => holdInput 10 c (fun u => f (t0+u)) s+w (t0+s))
      (fun s => f (t0+s)) := by
  have hs := trajectory_shift ht0 hf
  constructor
  · exact hs.continuous
  · intro s hs0 i
    have ht : t0+s ∈ Icc t0 H := ⟨by linarith [hs0.1],by linarith [hs0.2]⟩
    obtain ⟨hq0,hj0⟩ := hq (t0+s) ht
    have hu : physicalInput 10 f q j (t0+s) =
        holdInput 10 c (fun u => f (t0+u)) s := by
      dsimp [physicalInput]
      rw [hq0,hj0]
      dsimp [holdInput,command,scaleState]
      ring
    simpa only [hu] using hs.ode s hs0 i

/-- The old tracking coordinates at the stop time are exactly the hold
coordinates. There is no independent endpoint or fresh initial cube premise. -/
theorem tail_cube_identity {c t0 : ℝ} {f q : ℝ → State}
    (hq : q t0 = ![c,0,0]) :
    coordinates 0 (scaledError 10 f q t0) =
      coordinates c (scaleState 10 (f t0)) := by
  funext i
  fin_cases i <;> dsimp [coordinates,scaledError,scaleState,error] <;> rw [hq] <;>
    norm_num <;> ring

/-- A tracking cube and constant reference tail give physical terminal bands
on the same trajectory, two seconds after the reference stop time. -/
theorem tracked_tail_terminal {H t0 c : ℝ} (ht0 : 0 ≤ t0) (hH : t0+2 ≤ H)
    {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => physicalInput 10 f q j t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hq : ∀ t ∈ Icc t0 H, q t = ![c,0,0] ∧ j t = 0)
    (hcube : ∀ t ∈ Icc 0 H, ∀ i, |coordinates 0 (scaledError 10 f q t) i| ≤ 1/5000) :
    ∀ t ∈ Icc (t0+2) H, |f t 0-c| ≤ 1/5000 ∧
      |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50 := by
  have mapped (s : ℝ) (hs : s ∈ Icc 0 (H-t0)) : t0+s ∈ Icc 0 H :=
    ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hi : ∀ i, |coordinates c (scaleState 10 (f (t0+0))) i| ≤ 1/5000 := by
    have hh := hcube t0 ⟨ht0,by linarith⟩
    rw [tail_cube_identity (hq t0 ⟨le_rfl,by linarith⟩).1] at hh
    simpa only [add_zero] using hh
  have terminal := two_seconds_actual_changing_input (H:=H-t0) (c:=c)
    (by linarith) (constant_tail_hold ht0 hf hq)
    (fun s hs => hrlo _ (mapped s hs)) (fun s hs => hrhi _ (mapped s hs))
    (fun s hs => hw _ (mapped s hs)) hi
  intro t ht
  have hs : t-t0 ∈ Icc 2 (H-t0) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hv := terminal (t-t0) hs
  have heq : t0+(t-t0) = t := by ring
  rw [heq] at hv
  have hx := hcube t ⟨by linarith [ht.1],ht.2⟩ 0
  have hqt := (hq t ⟨by linarith [ht.1],ht.2⟩).1
  simpa [coordinates,scaledError,scaleState,error,hqt] using And.intro hx hv

/-- The original delayed FIR return, then the same physical terminal hold.
The guaranteed terminal time is 3.42 s, not the numerical task's 1.7 s. -/
theorem delayed_return_physical_terminal {H : ℝ} (hH : 171/50 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r
      (fun t => physicalInput 10 f
        (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t + w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hi : ∀ i, |coordinates 0 (scaledError 10 f
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000) :
    (∀ t ∈ Icc 0 H, |f t 0-position 0 (1/5) (realEvents deferredReturn) t| ≤ 1/5000) ∧
    1/1000 ≤ f (1/2) 0-f 0 0 ∧
    (∀ t ∈ Icc (71/50) H, |f t 0| ≤ 1/5000) ∧
    (∀ t ∈ Icc (171/50) H, |f t 0| ≤ 1/5000 ∧
      |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50) := by
  have tracked := checked_tracking (h:=1/5) (J:=15/2) 0 deferredReturn deferred_return_jerk
    (σ:=10) (horizon:=H) (R:=1/5000) (W:=1/100)
    (by norm_num) (by linarith) (by norm_num)
    (by norm_num; exact hf)
    (by intro t ht; norm_num; exact hrlo t ht)
    (by intro t ht; norm_num; exact hrhi t ht) hw (by norm_num)
    (by norm_num; exact hi)
  have tube : ∀ t ∈ Icc 0 H,
      |f t 0-position 0 (1/5) (realEvents deferredReturn) t| ≤ 1/5000 := by
    intro t ht
    simpa [coordinates,scaledError,scaleState,error,referenceState] using tracked t ht 0
  have tail (t : ℝ) (ht : t ∈ Icc (71/50:ℝ) H) :
      referenceState 0 (1/5) (realEvents deferredReturn) t = ![0,0,0] ∧
      jerk (1/5) (realEvents deferredReturn) t = 0 := by
    obtain ⟨hq,hv,ha,hj⟩ := deferred_return_reference_contract.2.2.2 t ht.1
    exact ⟨by unfold referenceState; rw [hq,hv,ha],hj⟩
  have terminal := tracked_tail_terminal (t0:=71/50) (c:=0) (by norm_num)
    (by linarith) hf hrlo hrhi hw tail (by
      intro t ht i
      simpa using tracked t ht i)
  refine ⟨tube,?_,?_,?_⟩
  · have h0 := tube 0 ⟨le_rfl,by linarith⟩
    have hmid := tube (1/2) ⟨by norm_num,by linarith⟩
    rw [delayed_reference_initial] at h0
    rw [delayed_reference_progress] at hmid
    obtain ⟨h0a,h0b⟩ := abs_le.mp h0
    obtain ⟨h1a,h1b⟩ := abs_le.mp hmid
    norm_num at h0a h0b h1a h1b ⊢
    linarith
  · intro t ht
    have hx := tube t ⟨by linarith [ht.1],ht.2⟩
    rw [(deferred_return_reference_contract.2.2.2 t ht.1).1,sub_zero] at hx
    exact hx
  · intro t ht
    simpa only [sub_zero] using terminal t ⟨by linarith [ht.1],ht.2⟩

end RobotMotion.FIRHold
