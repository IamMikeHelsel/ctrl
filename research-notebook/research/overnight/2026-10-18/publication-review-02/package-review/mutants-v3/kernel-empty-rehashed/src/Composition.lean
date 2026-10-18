import Admission
import ScaledTracking

open Set
noncomputable section
namespace RobotMotion
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

def referenceState (g0 h : ℝ) (es : List Event) (t : ℝ) : State :=
  ![position g0 h es t,velocity h es t,acceleration h es t]

lemma referenceState_continuous (g0 h : ℝ) (es : List Event) :
    Continuous (referenceState g0 h es) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact position_continuous g0 h es
  · exact velocity_continuous h es
  · exact acceleration_continuous h es

lemma referenceState_deriv {h : ℝ} (hh : 0 < h) (g0 : ℝ) (es : List Event) (t : ℝ)
    (i : Fin 3) :
    HasDerivAt (fun s => referenceState g0 h es s i)
      (![referenceState g0 h es t 1,referenceState g0 h es t 2,jerk h es t] i) t := by
  fin_cases i
  · exact position_deriv g0 h es t
  · exact velocity_deriv h es t
  · exact acceleration_deriv hh es t

/-- The exact checker discharges the actual reference derivative and jerk premises.
All physical trajectory, disturbance, rate, initial-state, and budget premises remain explicit. -/
theorem checked_tracking {h J : ℚ} (g0 : ℝ) (es : List QEvent)
    (accepted : check h J 0 es = true)
    {σ horizon R W : ℝ} (hσ : 0 < σ) (hH : 0 ≤ horizon) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory horizon r
      (fun t => physicalInput σ f (referenceState g0 (h:ℝ) (realEvents es))
        (jerk (h:ℝ) (realEvents es)) t + w t) f)
    (hrlo : ∀ t ∈ Icc 0 horizon, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 horizon, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 horizon, |w t| ≤ W)
    (budget : W+(J:ℝ)/(48*σ) ≤ 2*σ^2*R)
    (hi : ∀ i, |coordinates 0
      (scaledError σ f (referenceState g0 (h:ℝ) (realEvents es)) 0) i| ≤ R) :
    ∀ t ∈ Icc 0 horizon, ∀ i, |coordinates 0
      (scaledError σ f (referenceState g0 (h:ℝ) (realEvents es)) t) i| ≤ R := by
  obtain ⟨hh,hJ,hfuture⟩ := (check_real_iff h J 0 es).mp accepted
  exact tracking_cube_scaled hσ hH hR hf
    (referenceState_continuous g0 (h:ℝ) (realEvents es)).continuousOn
    (fun t ht i => referenceState_deriv (by exact_mod_cast hh) g0 (realEvents es) t i)
    hrlo hrhi hw (fun t ht => hfuture t (by simpa using ht.1)) budget hi

/-- Finite guarded admissions give one immutable C3 reference history for this tracking theorem. -/
theorem admitted_tracking {h J g0 : ℚ} (hh : 0 < h) (hJ : 0 ≤ J)
    (ps : List Proposal)
    {σ horizon R W : ℝ} (hσ : 0 < σ) (hH : 0 ≤ horizon) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory horizon r
      (fun t => physicalInput σ f
        (referenceState (g0:ℝ) (h:ℝ) (realEvents (run h J (initial g0) ps).events))
        (jerk (h:ℝ) (realEvents (run h J (initial g0) ps).events)) t + w t) f)
    (hrlo : ∀ t ∈ Icc 0 horizon, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 horizon, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 horizon, |w t| ≤ W)
    (budget : W+(J:ℝ)/(48*σ) ≤ 2*σ^2*R)
    (hi : ∀ i, |coordinates 0
      (scaledError σ f
        (referenceState (g0:ℝ) (h:ℝ) (realEvents (run h J (initial g0) ps).events)) 0) i| ≤ R) :
    ∀ t ∈ Icc 0 horizon, ∀ i, |coordinates 0
      (scaledError σ f
        (referenceState (g0:ℝ) (h:ℝ) (realEvents (run h J (initial g0) ps).events)) t) i| ≤ R := by
  exact tracking_cube_scaled hσ hH hR hf
    (referenceState_continuous _ _ _).continuousOn
    (fun t ht i => referenceState_deriv (by exact_mod_cast hh) _ _ t i)
    hrlo hrhi hw (fun t ht => finite_admission_safe hh hJ ps t ht.1) budget hi

theorem fixed_tracking_budget :
    (1/100:ℝ)+(15/2)/(48*10) = 41/1600 ∧
    (41/1600:ℝ) ≤ 2*10^2*(1/5000) := by norm_num

theorem fixed_physical_jerk_expression :
    (12*10*(56*10^2*(1/5000)+5*(15/2)/(48*10)+1/100):ℝ) = 5799/40 := by norm_num

end RobotMotion
