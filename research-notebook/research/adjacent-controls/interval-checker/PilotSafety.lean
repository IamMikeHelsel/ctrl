module
public import IntervalPilotActual
public import TraceExecution
public import TerminalBase
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
@[expose] public section
noncomputable section
namespace LeanControls.PilotSafety
open IntervalChecker IntervalPilot UncertainLag

theorem terminal_box_energy {z : State} (hz : BoxMem (boxes 25) z) :
    UncertainTravel.V z ≤ 12 := by
  have hx := hz 0
  have hv := hz 1
  have ha := hz 2
  change ((24084868611855/17592186044416:ℚ):ℝ) ≤ z 0 ∧
    z 0 ≤ ((3052240866897/2199023255552:ℚ):ℝ) at hx
  change ((-42345062883/4398046511104:ℚ):ℝ) ≤ z 1 ∧
    z 1 ≤ ((132695820663/8796093022208:ℚ):ℝ) at hv
  change ((-2565659320477/4398046511104:ℚ):ℝ) ≤ z 2 ∧
    z 2 ≤ ((-9351761715967/17592186044416:ℚ):ℝ) at ha
  clear hz
  change BernsteinCertificate.energy Generated.TravelQuarterLower.P z ≤ 12
  rw [RecoveryTerminal.energy_ldl]
  dyadic_interval (native := false) [prec := 60]

theorem terminal_sample_energy {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z) :
    UncertainTravel.V (UncertainTravel.samples r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z 25) ≤ 12 := by
  have h := IntervalPilotActual.endpoints hrlo hrhi hz 25 (by omega)
  rw [TraceExecution.stateTrace_eq_samples] at h
  exact terminal_box_energy h

theorem sample_time (n : ℕ) :
    SamplingClock.sampleTime (fun _ : ℕ => (1/20:ℝ)) n = (n:ℝ)/20 := by
  induction n with
  | zero => simp [SamplingClock.sampleTime]
  | succ n ih =>
    rw [SamplingClock.sampleTime_succ, ih]
    push_cast
    ring

/-- Entry at t=1.25 for any actual continuous execution, for one initial
subbox and one rate cell. Errors are zero and every hold is 0.05. -/
theorem actual_terminal_entry {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z)
    {f : ℝ → State}
    (hf : ExecutionUniqueness.IsExecution r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z f) : UncertainTravel.V (f (5/4)) ≤ 12 := by
  have h := ExecutionUniqueness.samples_eq_of_execution r
    (ne_of_gt (by linarith : 0 < r)) (fun _=>1/20) (fun _=>0) (fun _=>0) z
    (hmin := 1/20) (by norm_num) (fun _=>le_rfl) hf 25
  rw [sample_time] at h
  norm_num at h
  rw [h]
  exact terminal_sample_energy hrlo hrhi hz

theorem exists_actual_entry {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z) :
    ∃ f : ℝ → State,
      ExecutionUniqueness.IsExecution r (fun _=>1/20) (fun _=>0) (fun _=>0) z f ∧
      UncertainTravel.V (f (5/4)) ≤ 12 := by
  let f := UncertainTravel.state r (fun _=>1/20) (fun _=>0) (fun _=>0) z
  have hf : ExecutionUniqueness.IsExecution r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z f :=
    ExecutionUniqueness.constructed_isExecution r (ne_of_gt (by linarith))
      (fun _=>1/20) (fun _=>0) (fun _=>0) z (hmin := 1/20)
      (by norm_num) (fun _=>le_rfl)
  exact ⟨f, hf, actual_terminal_entry hrlo hrhi hz hf⟩

end LeanControls.PilotSafety
#print axioms LeanControls.PilotSafety.terminal_box_energy
#print axioms LeanControls.PilotSafety.terminal_sample_energy
#print axioms LeanControls.PilotSafety.sample_time
#print axioms LeanControls.PilotSafety.actual_terminal_entry
#print axioms LeanControls.PilotSafety.exists_actual_entry
