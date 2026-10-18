import TimedAdmission
import Composition

open Set
noncomputable section
namespace RobotMotion.AccelerationAdmission
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

lemma delayed_reference_initial : position 0 (1/5) (realEvents deferredReturn) 0 = 0 := by
  norm_num [position,response,realEvents,realEvent,deferredReturn,F0,P]

lemma delayed_reference_progress : position 0 (1/5) (realEvents deferredReturn) (1/2) = 779/250000 := by
  norm_num [position,response,realEvents,realEvent,deferredReturn,F0,P]

/-- Conditional physical position result for the full delayed-return history.
The sole initial error-cube premise is at time zero; no revision reset occurs.
Physical velocity, acceleration and rest are not conclusions. -/
theorem delayed_return_physical_position {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory (5/2) r
      (fun t => physicalInput 10 f
        (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t + w t) f)
    (hrlo : ∀ t ∈ Icc (0:ℝ) (5/2), 80 ≤ r t)
    (hrhi : ∀ t ∈ Icc (0:ℝ) (5/2), r t ≤ 120)
    (hw : ∀ t ∈ Icc (0:ℝ) (5/2), |w t| ≤ 1/100)
    (hi : ∀ i, |coordinates 0 (scaledError 10 f
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000) :
    (∀ t ∈ Icc (0:ℝ) (5/2),
      |f t 0-position 0 (1/5) (realEvents deferredReturn) t| ≤ 1/5000) ∧
    1/100000 ≤ f (1/2) 0-f 0 0 ∧
    (∀ t ∈ Icc (71/50:ℝ) (5/2), |f t 0| ≤ 1/5000) ∧
    |f (17/10) 0| ≤ 1/5000 := by
  have tracked := checked_tracking (h:=1/5) (J:=15/2) 0 deferredReturn deferred_return_jerk
    (σ:=10) (horizon:=5/2) (R:=1/5000) (W:=1/100)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact hf)
    (by intro t ht; norm_num; exact hrlo t ht)
    (by intro t ht; norm_num; exact hrhi t ht) hw (by norm_num)
    (by norm_num; exact hi)
  have tube : ∀ t ∈ Icc (0:ℝ) (5/2),
      |f t 0-position 0 (1/5) (realEvents deferredReturn) t| ≤ 1/5000 := by
    intro t ht
    simpa [coordinates,scaledError,scaleState,error,referenceState] using tracked t ht 0
  have arrival : ∀ t ∈ Icc (71/50:ℝ) (5/2), |f t 0| ≤ 1/5000 := by
    intro t ht
    have hp := tube t ⟨by linarith [ht.1],ht.2⟩
    have hq := (deferred_return_reference_contract.2.2.2 t ht.1).1
    rw [hq,sub_zero] at hp
    exact hp
  refine ⟨tube,?_,arrival,arrival _ (by norm_num)⟩
  have h0 := tube 0 (by norm_num)
  have hmid := tube (1/2) (by norm_num)
  rw [delayed_reference_initial] at h0
  rw [delayed_reference_progress] at hmid
  obtain ⟨h0a,h0b⟩ := abs_le.mp h0
  obtain ⟨h1a,h1b⟩ := abs_le.mp hmid
  norm_num at h0a h0b h1a h1b ⊢
  linarith

/-- Zero actual initial state satisfies the only initial-cube obligation. -/
theorem zero_initial_cube {f : ℝ → State} (h0 : f 0 = 0) :
    ∀ i, |coordinates 0 (scaledError 10 f
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;>
    norm_num [coordinates,scaledError,scaleState,error,referenceState,h0,position,velocity,
      acceleration,response,realEvents,realEvent,deferredReturn,F0,F1,F2,P]

end RobotMotion.AccelerationAdmission
