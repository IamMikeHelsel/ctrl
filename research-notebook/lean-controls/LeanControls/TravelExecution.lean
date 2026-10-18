module
public import LeanControls.TravelSafety
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The assembled travel-safety trajectory follows each exact held segment,
joins continuously at sample boundaries, and satisfies the plant ODE in the
interior of each sampling interval. Positive dwell time is the only timing
condition needed for these execution semantics. -/
@[expose] public section
noncomputable section
namespace LeanControls.TravelExecution
open SamplingClock TravelSafety SaturatedLag
open Set Filter
open scoped Topology

theorem state_on_segment (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hshi : s < h n) :
    state h w z0 (sampleTime h n + s) = segment s (samples h w z0 n) (w n) := by
  have hn0 : 0 ≤ sampleTime h n :=
    (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
  have hi : segmentIndex h (sampleTime h n + s) = n := by
    apply segment_unique h hmin0 hlo (segmentIndex_spec h hmin0 hlo (by linarith))
    rw [sampleTime_succ]
    constructor <;> linarith
  simp [state, hi]

/-- At the right endpoint the next sample equals the completed held segment. -/
theorem state_on_closed_segment (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hshi : s ≤ h n) :
    state h w z0 (sampleTime h n + s) = segment s (samples h w z0 n) (w n) := by
  rcases lt_or_eq_of_le hshi with hs | hs
  · exact state_on_segment h w z0 hmin0 hlo n hs0 hs
  · rw [hs, ← sampleTime_succ, state_at_sample h w z0 hmin0 hlo, samples_succ]

theorem state_on_interval (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (sampleTime h n) (sampleTime h (n + 1))) :
    state h w z0 t = segment (t - sampleTime h n) (samples h w z0 n) (w n) := by
  have hh := state_on_closed_segment h w z0 hmin0 hlo n
    (s := t - sampleTime h n) (by linarith [ht.1])
    (by rw [sampleTime_succ] at ht; linarith [ht.2])
  simpa using hh

theorem segment_continuous (z : State) (w : ℝ) : Continuous (fun t => segment t z w) := by
  apply continuous_pi
  intro i
  exact continuous_iff_continuousAt.mpr (fun t => (segment_ode t z w i).continuousAt)

theorem state_continuousOn_interval (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    ContinuousOn (state h w z0) (Icc (sampleTime h n) (sampleTime h (n + 1))) := by
  apply ((segment_continuous (samples h w z0 n) (w n)).comp
    (continuous_id.sub continuous_const)).continuousOn.congr
  intro t ht
  exact state_on_interval h w z0 hmin0 hlo n ht

theorem state_continuousAt_positive (h w : ℕ → ℝ) (z0 : State) {hmin t : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (ht : 0 < t) :
    ContinuousAt (state h w z0) t := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_segment h hmin0 hlo ht.le
  rcases lt_or_eq_of_le hnlo with hnlt | hneq
  · exact (state_continuousOn_interval h w z0 hmin0 hlo n).continuousAt
      (Icc_mem_nhds hnlt hnhi)
  · have hn : n ≠ 0 := by
      intro hz
      simp only [hz, sampleTime_zero] at hneq
      linarith
    have hprev : n - 1 + 1 = n := by omega
    have hprevlt : sampleTime h (n - 1) < t := by
      rw [← hneq]
      exact sampleTime_strictMono h hmin0 hlo (by omega)
    have hc := (state_continuousOn_interval h w z0 hmin0 hlo (n - 1)).union_of_isClosed
      (state_continuousOn_interval h w z0 hmin0 hlo n) isClosed_Icc isClosed_Icc
    apply hc.continuousAt
    apply Filter.mem_of_superset (Icc_mem_nhds hprevlt hnhi)
    intro r hr
    by_cases hh : r ≤ sampleTime h n
    · exact Or.inl ⟨hr.1, by simpa [hprev] using hh⟩
    · exact Or.inr ⟨(lt_of_not_ge hh).le, hr.2⟩

/-- Every coordinate, including acceleration, is continuous across all sample
boundaries. Its derivative may jump when the held command or disturbance changes. -/
theorem state_continuousOn_nonnegative (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    ContinuousOn (state h w z0) (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le ht with heq | htpos
  · subst t
    have hc := state_continuousOn_interval h w z0 hmin0 hlo 0
    simp only [sampleTime_zero, sampleTime_succ, zero_add] at hc
    exact (continuousWithinAt_Icc_iff_Ici (hmin0.trans_le (hlo 0))).mp
      (hc 0 ⟨le_rfl, (hmin0.trans_le (hlo 0)).le⟩)
  · exact (state_continuousAt_positive h w z0 hmin0 hlo htpos).continuousWithinAt

/-- The actual assembled execution satisfies the held-input ODE away from
sample boundaries, with exactly the sampled clipped command and disturbance. -/
theorem state_ode_interior (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {t : ℝ}
    (htlo : sampleTime h n < t) (hthi : t < sampleTime h (n + 1)) (i : Fin 3) :
    HasDerivAt (fun r => state h w z0 r i)
      (ActuatorLag.vectorField
        (RobustPD.saturate 1 (input (samples h w z0 n)) + w n) (state h w z0 t) i) t := by
  have heq : (fun r => state h w z0 r i) =ᶠ[𝓝 t]
      (fun r => segment (r - sampleTime h n) (samples h w z0 n) (w n) i) := by
    filter_upwards [Ioo_mem_nhds htlo hthi] with r hr
    exact congrFun (state_on_interval h w z0 hmin0 hlo n ⟨hr.1.le, hr.2.le⟩) i
  have hd := (segment_ode (t - sampleTime h n) (samples h w z0 n) (w n) i).comp t
    ((hasDerivAt_id t).sub_const (sampleTime h n))
  have hst := state_on_interval h w z0 hmin0 hlo n ⟨htlo.le, hthi.le⟩
  rw [hst]
  simpa using hd.congr_of_eventuallyEq heq

end LeanControls.TravelExecution
