module
public import LeanControls.ExecutionUniqueness

/-! Recovery-to-controller composition for an independently specified trajectory.
The backup is one held command -1 at a fixed actuator rate; errors begin only
with the sampled controller. All three state coordinates remain continuous. -/
@[expose] public section
noncomputable section
namespace LeanControls.RecoveryHandoff
open Set SamplingClock
open UncertainLag (State heldSegment vectorField input)

/-- The actual switched ODE: fixed negative command before T, followed by the
trajectory's own sampled feedback. No equality to an analytic trajectory,
terminal safety, or uniqueness hypothesis is built into the specification. -/
structure IsRecoveryExecution (r T : ℝ) (h e d : ℕ → ℝ) (z0 : State)
    (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Ici 0)
  initial : f 0 = z0
  backup_ode : ∀ t ∈ Ioo 0 T, ∀ i : Fin 3,
    HasDerivAt (fun s => f s i) (vectorField r (-1) (f t) i) t
  sampled_ode : ∀ n, ∀ t ∈ Ioo (T + sampleTime h n) (T + sampleTime h (n+1)),
    ∀ i : Fin 3, HasDerivAt (fun s => f s i)
      (vectorField r
        (RobustPD.saturate 1 (input (f (T + sampleTime h n)) + e n) + d n)
        (f t) i) t

/-- Continuity and the backup ODE determine the full state through the handoff. -/
theorem backup_eq {r T : ℝ} (hr : r ≠ 0) (h e d : ℕ → ℝ) (z0 : State)
    {f : ℝ → State} (hf : IsRecoveryExecution r T h e d z0 f)
    {s : ℝ} (hs : s ∈ Icc 0 T) : f s = heldSegment r s z0 (-1) := by
  have heq := ExecutionUniqueness.eq_heldSegment hr
    (hf.continuous.mono (fun t ht => ht.1)) hf.backup_ode hs
  simpa [hf.initial] using heq

/-- Translate the actual future ODE and its own sampled states into the
existing execution contract. The handoff initial state is f(T), without reset. -/
theorem shifted_isExecution {r T : ℝ} (hT : 0 ≤ T) (h e d : ℕ → ℝ) (z0 : State)
    {f : ℝ → State} (hf : IsRecoveryExecution r T h e d z0 f) :
    ExecutionUniqueness.IsExecution r h e d (f T) (fun s => f (T+s)) := by
  refine ⟨hf.continuous.comp (continuous_const.add continuous_id).continuousOn
    (fun s hs => add_nonneg hT hs), by simp, ?_⟩
  intro n s hs i
  have ht : T+s ∈ Ioo (T+sampleTime h n) (T+sampleTime h (n+1)) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa using! (hf.sampled_ode n (T+s) ht i).comp s
    ((hasDerivAt_id s).const_add T)

/-- The future of any actual recovery execution equals the already verified
sampled construction, initialized at the exact backup terminal state. -/
theorem after_handoff_eq {r T : ℝ} (hr : r ≠ 0) (hT : 0 ≤ T)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsRecoveryExecution r T h e d z0 f)
    {s : ℝ} (hs : 0 ≤ s) :
    f (T+s) = UncertainTravel.state r h e d (heldSegment r T z0 (-1)) s := by
  have heq := ExecutionUniqueness.execution_eq_state r hr h e d (f T)
    hmin0 hlo (shifted_isExecution hT h e d z0 hf) hs
  rw [backup_eq hr h e d z0 hf ⟨hT, le_rfl⟩] at heq
  exact heq

/-- Analytic backup safety plus its terminal energy certificate give all-time
travel safety for every actual continuous execution of the switched ODE. -/
theorem travel_limit {r T : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hT : 0 ≤ T) (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90)
    (hbackup : ∀ s ∈ Icc 0 T, |heldSegment r s z0 (-1) 0| ≤ 2)
    (hterminal : UncertainTravel.V (heldSegment r T z0 (-1)) ≤ 12)
    {f : ℝ → State} (hf : IsRecoveryExecution r T h e d z0 f)
    {t : ℝ} (ht : 0 ≤ t) : |f t 0| ≤ 2 := by
  have hr : r ≠ 0 := ne_of_gt (by linarith)
  by_cases hbefore : t ≤ T
  · rw [backup_eq hr h e d z0 hf ⟨ht, hbefore⟩]
    exact hbackup t ⟨ht, hbefore⟩
  · have hs : 0 ≤ t-T := by linarith
    have heq := after_handoff_eq hr hT h e d z0 hmin0 hlo hf hs
    have hadd : T+(t-T) = t := by ring
    rw [hadd] at heq
    rw [heq]
    exact UncertainTravel.travel_limit hrlo hrhi h e d _ hmin0 hlo hhi hbudget hterminal hs

/-- One explicit execution: no state reset at the handoff. The value at T is
chosen from the backup branch; endpoint equality makes the choice immaterial. -/
def execution (r T : ℝ) (h e d : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  if t ≤ T then heldSegment r t z0 (-1)
  else UncertainTravel.state r h e d (heldSegment r T z0 (-1)) (t-T)

theorem execution_eq_backup (r T : ℝ) (h e d : ℕ → ℝ) (z0 : State)
    {t : ℝ} (ht : t ≤ T) : execution r T h e d z0 t = heldSegment r t z0 (-1) := by
  simp [execution, ht]

theorem execution_eq_control (r T : ℝ) (h e d : ℕ → ℝ) (z0 : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {t : ℝ} (ht : T ≤ t) : execution r T h e d z0 t =
      UncertainTravel.state r h e d (heldSegment r T z0 (-1)) (t-T) := by
  have hz := UncertainTravel.state_at_sample r h e d (heldSegment r T z0 (-1)) hmin0 hlo 0
  simp only [sampleTime_zero, UncertainTravel.samples_zero] at hz
  rcases eq_or_lt_of_le ht with heq | hlt
  · rw [← heq]
    simp [execution, hz]
  · simp [execution, not_le.mpr hlt]

/-- Both full-state pieces are continuous and agree at T, including acceleration. -/
theorem execution_continuousOn {r T : ℝ} (hr : r ≠ 0) (_hT : 0 ≤ T)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    ContinuousOn (execution r T h e d z0) (Ici 0) := by
  have hb : Continuous (fun t => heldSegment r t z0 (-1)) :=
    continuous_pi (fun i => continuous_iff_continuousAt.mpr
      (fun t => (UncertainLag.heldSegment_ode hr t z0 (-1) i).continuousAt))
  have hleft : ContinuousOn (execution r T h e d z0) (Icc 0 T) :=
    hb.continuousOn.congr (fun t ht => execution_eq_backup r T h e d z0 ht.2)
  have hc := UncertainExecution.state_continuousOn_nonnegative r hr h e d
    (heldSegment r T z0 (-1)) hmin0 hlo
  have hright : ContinuousOn (execution r T h e d z0) (Ici T) :=
    (hc.comp (continuous_id.sub continuous_const).continuousOn
      (fun t ht => sub_nonneg.mpr ht)).congr
      (fun t ht => execution_eq_control r T h e d z0 hmin0 hlo ht)
  exact (hleft.union_of_isClosed hright isClosed_Icc isClosed_Ici).mono (by
    intro t ht
    by_cases hbefore : t ≤ T
    · exact Or.inl ⟨ht, hbefore⟩
    · exact Or.inr (le_of_not_ge hbefore))

/-- Existence under the differential-equation contract needs no safety or
terminal-energy premise. Rate is fixed; there is no backup disturbance. -/
theorem constructed_isRecoveryExecution {r T : ℝ} (hr : r ≠ 0) (hT : 0 ≤ T)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    IsRecoveryExecution r T h e d z0 (execution r T h e d z0) := by
  refine ⟨execution_continuousOn hr hT h e d z0 hmin0 hlo, ?_, ?_, ?_⟩
  · simp [execution, hT, UncertainLag.heldSegment_zero]
  · intro t ht i
    have heq : (fun s => execution r T h e d z0 s i) =ᶠ[nhds t]
        (fun s => heldSegment r s z0 (-1) i) := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      exact congrFun (execution_eq_backup r T h e d z0 hs.le) i
    rw [execution_eq_backup r T h e d z0 ht.2.le]
    exact (UncertainLag.heldSegment_ode hr t z0 (-1) i).congr_of_eventuallyEq heq
  · intro n t ht i
    have hn0 : 0 ≤ sampleTime h n :=
      (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
    have htn : T ≤ T+sampleTime h n := by linarith
    have htT : T < t := by linarith [ht.1]
    have base := ExecutionUniqueness.constructed_isExecution r hr h e d
      (heldSegment r T z0 (-1)) hmin0 hlo
    have hlocal : t-T ∈ Ioo (sampleTime h n) (sampleTime h (n+1)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hd := (base.ode n (t-T) hlocal i).comp t ((hasDerivAt_id t).sub_const T)
    have heq : (fun s => execution r T h e d z0 s i) =ᶠ[nhds t]
        (fun s => UncertainTravel.state r h e d (heldSegment r T z0 (-1)) (s-T) i) := by
      filter_upwards [Ioi_mem_nhds htT] with s hs
      exact congrFun (execution_eq_control r T h e d z0 hmin0 hlo hs.le) i
    rw [execution_eq_control r T h e d z0 hmin0 hlo htn,
      execution_eq_control r T h e d z0 hmin0 hlo htT.le]
    simpa using hd.congr_of_eventuallyEq heq

/-- Recovery executions are unique for the same rate, timing and error sequences. -/
theorem execution_unique {r T : ℝ} (hr : r ≠ 0) (hT : 0 ≤ T)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f g : ℝ → State} (hf : IsRecoveryExecution r T h e d z0 f)
    (hg : IsRecoveryExecution r T h e d z0 g) : EqOn f g (Ici 0) := by
  intro t ht
  by_cases hbefore : t ≤ T
  · exact (backup_eq hr h e d z0 hf ⟨ht, hbefore⟩).trans
      (backup_eq hr h e d z0 hg ⟨ht, hbefore⟩).symm
  · have hs : 0 ≤ t-T := by linarith
    have hh := (after_handoff_eq hr hT h e d z0 hmin0 hlo hf hs).trans
      (after_handoff_eq hr hT h e d z0 hmin0 hlo hg hs).symm
    simpa using hh

end LeanControls.RecoveryHandoff
#print axioms LeanControls.RecoveryHandoff.backup_eq
#print axioms LeanControls.RecoveryHandoff.shifted_isExecution
#print axioms LeanControls.RecoveryHandoff.after_handoff_eq
#print axioms LeanControls.RecoveryHandoff.travel_limit

#print axioms LeanControls.RecoveryHandoff.execution_eq_backup

#print axioms LeanControls.RecoveryHandoff.execution_eq_control

#print axioms LeanControls.RecoveryHandoff.execution_continuousOn

#print axioms LeanControls.RecoveryHandoff.constructed_isRecoveryExecution

#print axioms LeanControls.RecoveryHandoff.execution_unique
