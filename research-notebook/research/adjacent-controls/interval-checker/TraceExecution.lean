module
public import IntervalChecker
public import LeanControls.ExecutionUniqueness
@[expose] public section
noncomputable section
namespace LeanControls.TraceExecution
open IntervalChecker UncertainLag

theorem stateTrace_eq_samples (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) :
    stateTrace (fun _ => r) h e d z0 n = UncertainTravel.samples r h e d z0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stateTrace, UncertainTravel.samples_succ, ih,
      UncertainTravel.segment, heldSegment]

/-- A checked finite trace encloses samples of any actual continuous ODE
execution. This theorem does not claim safety between those samples. -/
theorem actual_samples_enclosed {N : ℕ} (r : ℝ) (hr : r ≠ 0)
    (h e d : ℕ → ℝ) (K : ℕ → Coefficients) (ei di : ℕ → Interval) (X : ℕ → Box)
    {z0 : State} {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : ExecutionUniqueness.IsExecution r h e d z0 f)
    (h0 : BoxMem (X 0) z0) (hk : ∀ n<N, CoeffMem (K n) r (h n))
    (he : ∀ n<N, Mem (ei n) (e n)) (hd : ∀ n<N, Mem (di n) (d n))
    (hstep : ∀ n<N, BoxSubset (sampledBox (K n) (X n) (ei n) (di n)) (X (n+1))) :
    ∀ n≤N, BoxMem (X n) (f (SamplingClock.sampleTime h n)) := by
  intro n hn
  rw [ExecutionUniqueness.samples_eq_of_execution r hr h e d z0 hmin0 hlo hf n]
  rw [← stateTrace_eq_samples]
  exact certificate_trace_sound (fun _ => r) h e d K ei di X h0 hk he hd hstep n hn

end LeanControls.TraceExecution
#print axioms LeanControls.TraceExecution.stateTrace_eq_samples
#print axioms LeanControls.TraceExecution.actual_samples_enclosed
