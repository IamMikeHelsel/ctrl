import IsolatedHistory

open Set
noncomputable section
namespace RobotMotion.TaskContract
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

/-- Positive progress points from the old authoritative goal to the new one.
For an unchanged goal, the chosen positive direction is immaterial to arrival. -/
def directed (a g x : ℝ) : ℝ := if a ≤ g then x-a else a-x

lemma blend_range {a g u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    min a g ≤ a+(g-a)*u ∧ a+(g-a)*u ≤ max a g := by
  by_cases hag : a ≤ g
  · simp only [min_eq_left hag,max_eq_right hag]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hag) hu.1,
      mul_nonneg (sub_nonneg.mpr hag) (sub_nonneg.mpr hu.2)]
  · have hga : g ≤ a := le_of_lt (lt_of_not_ge hag)
    simp only [min_eq_right hga,max_eq_left hga]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hga) hu.1,
      mul_nonneg (sub_nonneg.mpr hga) (sub_nonneg.mpr hu.2)]

lemma blend_distance {a g u : ℝ} (hu : u ≤ 1) :
    |a+(g-a)*u-g| = |g-a| *(1-u) := by
  have he : a+(g-a)*u-g = -(g-a)*(1-u) := by ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hu)]

lemma tube_task_bounds {x a g u R : ℝ} (hu : 0 ≤ u ∧ u ≤ 1)
    (hx : |x-(a+(g-a)*u)| ≤ R) :
    min a g-R ≤ x ∧ x ≤ max a g+R ∧
      |x-g| ≤ |g-a| *(1-u)+R ∧ |g-a| *u-R ≤ directed a g x := by
  have hrange := blend_range (a:=a) (g:=g) hu
  have hab := abs_le.mp hx
  refine ⟨by linarith,by linarith,?_,?_⟩
  · have hd := abs_sub_le x (a+(g-a)*u) g
    rw [blend_distance hu.2] at hd
    linarith
  · by_cases hag : a ≤ g
    · simp [directed,hag,abs_of_nonneg (sub_nonneg.mpr hag)]
      linarith
    · have hga : g-a ≤ 0 := by linarith
      simp [directed,hag,abs_of_nonpos hga]
      linarith

structure PositionTask (h s tau a g horizon R : ℝ) (x : ℝ → ℝ) : Prop where
  hold : ∀ t ∈ Icc 0 horizon, s ≤ t → t ≤ tau → |x t-a| ≤ R
  transition : ∀ t ∈ Icc 0 horizon, s ≤ t →
    min a g-R ≤ x t ∧ x t ≤ max a g+R ∧
      |x t-g| ≤ |g-a| *(1-F0 ((t-tau)/h))+R ∧
      |g-a| *F0 ((t-tau)/h)-R ≤ directed a g (x t)
  midpoint_error : tau+2*h ∈ Icc 0 horizon →
    |x (tau+2*h)-(a+(g-a)/2)| ≤ R
  midpoint : tau+2*h ∈ Icc 0 horizon →
    |g-a|/2-R ≤ directed a g (x (tau+2*h))
  arrival : ∀ t ∈ Icc 0 horizon, tau+4*h ≤ t → |x t-g| ≤ R

lemma retained_task_from_tube {h s tau g0 a g horizon R : ℝ} (hh : 0 < h)
    (old : List Event) (hc : CompleteBy h s old)
    (ha : g0+(old.map Prod.snd).sum = a) (hst : s ≤ tau) (x : ℝ → ℝ)
    (tube : ∀ t ∈ Icc 0 horizon, |x t-position g0 h (old++[(tau,g-a)]) t| ≤ R) :
    PositionTask h s tau a g horizon R x := by
  constructor
  · intro t ht hs hbefore
    simpa only [isolated_hold hh old hc ha hs hbefore] using tube t ht
  · intro t ht hs
    have hx := tube t ht
    rw [isolated_reference hh old hc ha hs] at hx
    exact tube_task_bounds (F0_range _) hx
  · intro ht
    simpa only [isolated_midpoint hh old hc ha hst] using tube (tau+2*h) ht
  · intro ht
    have hx := tube (tau+2*h) ht
    rw [isolated_reference hh old hc ha (by linarith)] at hx
    have he : (tau+2*h-tau)/h = 2 := by field_simp; ring
    rw [he,F0_two] at hx
    have hb := (tube_task_bounds (by norm_num : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1) hx).2.2.2
    convert hb using 1; ring
  · intro t ht hafter
    simpa only [isolated_arrival hh old hc ha hst hafter] using tube t ht

/-- A task result derived from the exact guard and the actual physical trajectory.
The initial cube is at time zero for the complete retained history, never reset. -/
theorem checked_isolated_task {h J et ed : ℚ} {s tau g0 a g D : ℝ}
    (old : List QEvent) (acceptedOld : check h J 0 old = true)
    (hc : CompleteBy (h:ℝ) s (realEvents old))
    (ha : g0+((realEvents old).map Prod.snd).sum = a)
    (hs : 0 ≤ s) (hst : s ≤ tau) (ht : (et:ℝ)=tau) (hd : (ed:ℝ)=g-a)
    (hstep : 2*|g-a|/(h:ℝ)^3 ≤ (J:ℝ)) (hdeadline : tau+4*(h:ℝ) ≤ D)
    {σ horizon R W : ℝ} (hσ : 0 < σ) (hH : 0 ≤ horizon) (hR : 0 ≤ R) (hDH : D ≤ horizon)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory horizon r
      (fun t => physicalInput σ f
        (referenceState g0 (h:ℝ) (realEvents (old++[(et,ed)])))
        (jerk (h:ℝ) (realEvents (old++[(et,ed)]))) t + w t) f)
    (hrlo : ∀ t ∈ Icc 0 horizon, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 horizon, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 horizon, |w t| ≤ W)
    (budget : W+(J:ℝ)/(48*σ) ≤ 2*σ^2*R)
    (hi : ∀ i, |coordinates 0 (scaledError σ f
      (referenceState g0 (h:ℝ) (realEvents (old++[(et,ed)]))) 0) i| ≤ R) :
    check h J 0 (old++[(et,ed)]) = true ∧
    PositionTask (h:ℝ) s tau a g horizon R (fun t => f t 0) ∧
    |f D 0-g| ≤ R ∧
    (∀ t ∈ Icc D horizon, |f t 0-g| ≤ R) := by
  have hnew := isolated_check (g0:=g0) old acceptedOld hc hst et ed ht hd hstep
  have hh : (0:ℝ) < (h:ℝ) := by
    exact_mod_cast ((check_real_iff h J 0 old).mp acceptedOld).1
  have tracked := checked_tracking g0 (old++[(et,ed)]) hnew hσ hH hR
    hf hrlo hrhi hw budget hi
  have tube : ∀ t ∈ Icc 0 horizon,
      |f t 0-position g0 (h:ℝ) (realEvents old++[(tau,g-a)]) t| ≤ R := by
    intro t htime
    have hp := tracked t htime 0
    simpa [coordinates,scaledError,scaleState,error,referenceState,
      realEvents,realEvent,ht,hd] using hp
  have task := retained_task_from_tube hh (realEvents old) hc ha hst
    (fun t => f t 0) tube
  refine ⟨hnew,task,?_,?_⟩
  · exact task.arrival D ⟨by linarith,hDH⟩ hdeadline
  intro t htime
  have ht0 : 0 ≤ t := by linarith [htime.1]
  exact task.arrival t ⟨ht0,htime.2⟩ (hdeadline.trans htime.1)

end RobotMotion.TaskContract
