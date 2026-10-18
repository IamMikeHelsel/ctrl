module
public import LeanControls.ExecutionUniqueness

/-! Continue any continuous state prefix with the checked sampled controller.
The prefix need not follow any ODE in this module. Physical realization of that
prefix is a separate obligation. The tail uses one fixed actuator rate and its
own sampled states, with held pre-clamp and post-clamp command errors. -/
@[expose] public section
noncomputable section
namespace LeanControls.GeneralHandoff
open Set SamplingClock
open UncertainLag (State vectorField input)

/-- Continuity on all nonnegative times and a sampled ODE only after T.
No differential equation, reset, safety property, or chosen trajectory equality
is assumed for the prefix. The first tail sample is the actual state f(T). -/
structure IsContinuation (r T : ℝ) (h e d : ℕ → ℝ) (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Ici 0)
  ode : ∀ n, ∀ t ∈ Ioo (T + sampleTime h n) (T + sampleTime h (n+1)),
    ∀ i : Fin 3, HasDerivAt (fun s => f s i)
      (vectorField r
        (RobustPD.saturate 1 (input (f (T + sampleTime h n)) + e n) + d n)
        (f t) i) t

/-- Translation gives the existing execution contract with initial state f(T).
The actual sampled feedback is preserved by the translation. -/
theorem shifted_isExecution {r T : ℝ} (hT : 0 ≤ T) (h e d : ℕ → ℝ)
    {f : ℝ → State} (hf : IsContinuation r T h e d f) :
    ExecutionUniqueness.IsExecution r h e d (f T) (fun s => f (T+s)) := by
  refine ⟨hf.continuous.comp (continuous_const.add continuous_id).continuousOn
    (fun s hs => add_nonneg hT hs), by simp, ?_⟩
  intro n s hs i
  have ht : T+s ∈ Ioo (T+sampleTime h n) (T+sampleTime h (n+1)) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa using! (hf.ode n (T+s) ht i).comp s ((hasDerivAt_id s).const_add T)

/-- Every continuation's tail is the unique analytic sampled execution from
its actual handoff state. No dynamics of the preceding prefix are required. -/
theorem tail_eq_state {r T : ℝ} (hr : r ≠ 0) (hT : 0 ≤ T)
    (h e d : ℕ → ℝ) {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsContinuation r T h e d f) {s : ℝ} (hs : 0 ≤ s) :
    f (T+s) = UncertainTravel.state r h e d (f T) s :=
  ExecutionUniqueness.execution_eq_state r hr h e d (f T) hmin0 hlo
    (shifted_isExecution hT h e d hf) hs

/-- Safe prefix plus terminal invariant implies all-time travel safety. These
two prefix facts are explicit caller obligations, independent of the tail ODE. -/
theorem actual_all_time_safe {r T : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hT : 0 ≤ T) (h e d : ℕ → ℝ) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n|+|d n| ≤ 1/90)
    {f : ℝ → State} (hf : IsContinuation r T h e d f)
    (hprefix : ∀ t ∈ Icc 0 T, |f t 0| ≤ 2)
    (hterminal : UncertainTravel.V (f T) ≤ 12) {t : ℝ} (ht : 0 ≤ t) :
    |f t 0| ≤ 2 := by
  by_cases hbefore : t ≤ T
  · exact hprefix t ⟨ht,hbefore⟩
  · have hs : 0 ≤ t-T := by linarith
    have heq := tail_eq_state (ne_of_gt (by linarith : 0 < r)) hT h e d hmin0 hlo hf hs
    have hadd : T+(t-T) = t := by ring
    rw [hadd] at heq
    rw [heq]
    exact UncertainTravel.travel_limit hrlo hrhi h e d (f T) hmin0 hlo hhi hbudget hterminal hs

/-- Splice an arbitrary prefix to the sampled controller at its own terminal
state. Values at or before T use p; the tail starts from exactly p(T). -/
def continuation (r T : ℝ) (h e d : ℕ → ℝ) (p : ℝ → State) (t : ℝ) : State :=
  if t ≤ T then p t else UncertainTravel.state r h e d (p T) (t-T)

theorem continuation_eq_prefix (r T : ℝ) (h e d : ℕ → ℝ) (p : ℝ → State)
    {t : ℝ} (ht : t ≤ T) : continuation r T h e d p t = p t := by
  simp [continuation,ht]

/-- This includes t=T: the two branches agree in position, velocity and
acceleration, so the handoff has no state reset. -/
theorem continuation_eq_tail (r T : ℝ) (h e d : ℕ → ℝ) (p : ℝ → State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {t : ℝ} (ht : T ≤ t) : continuation r T h e d p t =
      UncertainTravel.state r h e d (p T) (t-T) := by
  have hz := UncertainTravel.state_at_sample r h e d (p T) hmin0 hlo 0
  simp only [sampleTime_zero, UncertainTravel.samples_zero] at hz
  rcases eq_or_lt_of_le ht with heq | hlt
  · rw [← heq]
    simp [continuation,hz]
  · simp [continuation,not_le.mpr hlt]

theorem continuation_continuousOn {r T : ℝ} (hr : r ≠ 0)
    (h e d : ℕ → ℝ) (p : ℝ → State) (hp : ContinuousOn p (Icc 0 T))
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    ContinuousOn (continuation r T h e d p) (Ici 0) := by
  have hleft : ContinuousOn (continuation r T h e d p) (Icc 0 T) :=
    hp.congr (fun t ht => continuation_eq_prefix r T h e d p ht.2)
  have hc := UncertainExecution.state_continuousOn_nonnegative r hr h e d (p T) hmin0 hlo
  have hright : ContinuousOn (continuation r T h e d p) (Ici T) :=
    (hc.comp (continuous_id.sub continuous_const).continuousOn
      (fun t ht => sub_nonneg.mpr ht)).congr
      (fun t ht => continuation_eq_tail r T h e d p hmin0 hlo ht)
  exact (hleft.union_of_isClosed hright isClosed_Icc isClosed_Ici).mono (by
    intro t ht
    by_cases hbefore : t ≤ T
    · exact Or.inl ⟨ht,hbefore⟩
    · exact Or.inr (le_of_not_ge hbefore))

/-- An explicit witness of the tail ODE contract. Only continuity is required
of the prefix; no prefix safety, terminal-energy or prefix-ODE premise appears. -/
theorem constructed_isContinuation {r T : ℝ} (hr : r ≠ 0)
    (h e d : ℕ → ℝ) (p : ℝ → State) (hp : ContinuousOn p (Icc 0 T))
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    IsContinuation r T h e d (continuation r T h e d p) := by
  refine ⟨continuation_continuousOn hr h e d p hp hmin0 hlo, ?_⟩
  intro n t ht i
  have hn0 : 0 ≤ sampleTime h n :=
    (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
  have htn : T ≤ T+sampleTime h n := by linarith
  have htT : T < t := by linarith [ht.1]
  have base := ExecutionUniqueness.constructed_isExecution r hr h e d (p T) hmin0 hlo
  have hlocal : t-T ∈ Ioo (sampleTime h n) (sampleTime h (n+1)) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := (base.ode n (t-T) hlocal i).comp t ((hasDerivAt_id t).sub_const T)
  have heq : (fun s => continuation r T h e d p s i) =ᶠ[nhds t]
      (fun s => UncertainTravel.state r h e d (p T) (s-T) i) := by
    filter_upwards [Ioi_mem_nhds htT] with s hs
    exact congrFun (continuation_eq_tail r T h e d p hmin0 hlo hs.le) i
  rw [continuation_eq_tail r T h e d p hmin0 hlo htn,
    continuation_eq_tail r T h e d p hmin0 hlo htT.le]
  simpa using hd.congr_of_eventuallyEq heq

/-- Every continuous prefix admits a continuation satisfying the tail ODE.
The prefix agreement includes the handoff endpoint. It does not certify that
the prefix follows any physical differential equation. -/
theorem exists_continuation {r T : ℝ} (hr : r ≠ 0)
    (h e d : ℕ → ℝ) (p : ℝ → State) (hp : ContinuousOn p (Icc 0 T))
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    ∃ f : ℝ → State, IsContinuation r T h e d f ∧ EqOn f p (Icc 0 T) := by
  exact ⟨continuation r T h e d p,
    constructed_isContinuation hr h e d p hp hmin0 hlo,
    fun t ht => continuation_eq_prefix r T h e d p ht.2⟩

end LeanControls.GeneralHandoff
#print axioms LeanControls.GeneralHandoff.shifted_isExecution
#print axioms LeanControls.GeneralHandoff.tail_eq_state
#print axioms LeanControls.GeneralHandoff.actual_all_time_safe
#print axioms LeanControls.GeneralHandoff.continuation_eq_prefix
#print axioms LeanControls.GeneralHandoff.continuation_eq_tail
#print axioms LeanControls.GeneralHandoff.continuation_continuousOn
#print axioms LeanControls.GeneralHandoff.constructed_isContinuation
#print axioms LeanControls.GeneralHandoff.exists_continuation
