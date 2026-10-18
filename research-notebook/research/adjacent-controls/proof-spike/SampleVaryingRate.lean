module
public import LeanControls.UncertainTravel

/-! Isolated reuse spike. The actuator rate is allowed to change at updates,
while remaining constant during each hold. This file does not change the frozen
project or claim arbitrary within-hold rate uncertainty. -/
@[expose] public section
noncomputable section
namespace LeanControls.Adjacent.SampleVaryingRate
open SamplingClock
open UncertainLag (State)
open UncertainTravel (segment V)

def samples (r h e d : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n+1 => segment (r n) (h n) (samples r h e d z0 n) (e n) (d n)

theorem samples_zero (r h e d : ℕ → ℝ) (z0 : State) :
    samples r h e d z0 0 = z0 := rfl

theorem samples_succ (r h e d : ℕ → ℝ) (z0 : State) (n : ℕ) :
    samples r h e d z0 (n+1) =
      segment (r n) (h n) (samples r h e d z0 n) (e n) (d n) := rfl

/-- No bound on successive rate differences or number of switches is needed.
The existing common energy proves this by induction over actual held segments. -/
theorem samples_invariant (r h e d : ℕ → ℝ) (z0 : State)
    (hrlo : ∀ n, 9/10 ≤ r n) (hrhi : ∀ n, r n ≤ 11/10)
    (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12) :
    ∀ n, V (samples r h e d z0 n) ≤ 12 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    exact UncertainTravel.segment_invariant (hrlo n) (hrhi n)
      (hlo n) (hhi n) (hbudget n) ih

def state (r h e d : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  let n := segmentIndex h t
  segment (r n) (t-sampleTime h n) (samples r h e d z0 n) (e n) (d n)

theorem state_at_sample (r h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state r h e d z0 (sampleTime h n) = samples r h e d z0 n := by
  simp [state, segmentIndex_at_sample h hmin0 hlo n, UncertainTravel.segment_zero]

/-- Every real time is covered even when the rate sequence switches forever.
Non-Zeno sampling is assumed through a positive uniform dwell lower bound. -/
theorem state_invariant (r h e d : ℕ → ℝ) (z0 : State)
    (hrlo : ∀ n, 9/10 ≤ r n) (hrhi : ∀ n, r n ≤ 11/10)
    {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : V (state r h e d z0 t) ≤ 12 := by
  obtain ⟨htlo, hthi⟩ := segmentIndex_spec h hmin0 hlo ht
  rw [sampleTime_succ] at hthi
  apply UncertainTravel.segment_invariant (hrlo _) (hrhi _) (sub_nonneg.mpr htlo)
    (by linarith [hhi (segmentIndex h t)]) (hbudget _) 
  exact samples_invariant r h e d z0 hrlo hrhi
    (fun n => hmin0.le.trans (hlo n)) hhi hbudget hz _

theorem travel_limit (r h e d : ℕ → ℝ) (z0 : State)
    (hrlo : ∀ n, 9/10 ≤ r n) (hrhi : ∀ n, r n ≤ 11/10)
    {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : |state r h e d z0 t 0| ≤ 2 :=
  TravelGeometry.position_safe
    (state_invariant r h e d z0 hrlo hrhi hmin0 hlo hhi hbudget hz ht)

/-- The closed segment ends at the next actual sample, regardless of rate jump. -/
theorem segment_endpoint (r h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state r h e d z0 (sampleTime h (n+1)) =
      segment (r n) (h n) (samples r h e d z0 n) (e n) (d n) := by
  rw [state_at_sample r h e d z0 hmin0 hlo, samples_succ]

end LeanControls.Adjacent.SampleVaryingRate
#print axioms LeanControls.Adjacent.SampleVaryingRate.samples_zero
#print axioms LeanControls.Adjacent.SampleVaryingRate.samples_succ
#print axioms LeanControls.Adjacent.SampleVaryingRate.samples_invariant
#print axioms LeanControls.Adjacent.SampleVaryingRate.state_at_sample
#print axioms LeanControls.Adjacent.SampleVaryingRate.state_invariant
#print axioms LeanControls.Adjacent.SampleVaryingRate.travel_limit
#print axioms LeanControls.Adjacent.SampleVaryingRate.segment_endpoint
