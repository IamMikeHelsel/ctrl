module
public import BetweenSample
public import PilotSafety
@[expose] public section
noncomputable section
namespace LeanControls.PilotPath
open IntervalChecker IntervalPilot UncertainLag

def coarse : Box := ![⟨9/10,3/2⟩,⟨-1,1⟩,⟨-1,1⟩]

/-- Rational endpoint certificates imply one common coarse state envelope. -/
theorem boxes_coarse (n : ℕ) (hn : n ≤ 25) : BoxSubset (boxes n) coarse := by
  interval_cases n <;> intro i <;> fin_cases i <;>
    norm_num [IntervalChecker.Subset, boxes, coarse]

theorem coarse_bounds {z : State} (hz : BoxMem coarse z) :
    |z 0| ≤ 3/2 ∧ |z 1| ≤ 1 ∧ |z 2| ≤ 1 := by
  have hx := hz 0
  have hv := hz 1
  have ha := hz 2
  norm_num [Mem,coarse] at hx hv ha
  exact ⟨abs_le.mpr ⟨by linarith, hx.2⟩, abs_le.mpr hv, abs_le.mpr ha⟩

/-- Every real elapsed time in each of the25 checked holds is travel-safe.
This pilot has no pre-clamp or post-clamp errors during the finite prefix. -/
theorem segment_safe {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z)
    {n : ℕ} (hn : n < 25) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/20) :
    |UncertainTravel.segment r s (UncertainTravel.samples r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z n) 0 0 0| ≤ 2 := by
  have hb := IntervalPilotActual.endpoints hrlo hrhi hz n (by omega)
  rw [TraceExecution.stateTrace_eq_samples] at hb
  have hcoarse : BoxMem coarse (UncertainTravel.samples r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z n) :=
    fun i => subset_mem (boxes_coarse n (by omega) i) (hb i)
  obtain ⟨hx,hv,ha⟩ := coarse_bounds hcoarse
  have hrs : r*s ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 73/80-r by linarith) hs0]
  have hu := SaturationSector.clamp_abs_le (show (0:ℝ) ≤ 1 by norm_num)
    (input (UncertainTravel.samples r (fun _=>1/20) (fun _=>0) (fun _=>0) z n))
  simpa [UncertainTravel.segment,heldSegment] using
    BetweenSample.short_hold_safe (by linarith : 0 < r) hs0 hs1 hrs hx hv ha hu

/-- Transfer the closed-segment result to any continuous solution of the
actual sampled ODE. It includes both sample boundaries, without reset. -/
theorem actual_segment_safe {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z)
    {f : ℝ → State} (hf : ExecutionUniqueness.IsExecution r (fun _=>1/20)
      (fun _=>0) (fun _=>0) z f) {n : ℕ} (hn : n < 25)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/20) :
    |f (SamplingClock.sampleTime (fun _ : ℕ => (1/20:ℝ)) n+s) 0| ≤ 2 := by
  have hr : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
  have hn0 : 0 ≤ SamplingClock.sampleTime (fun _ : ℕ => (1/20:ℝ)) n := by
    rw [PilotSafety.sample_time]
    positivity
  rw [ExecutionUniqueness.execution_eq_state r hr (fun _=>1/20) (fun _=>0) (fun _=>0) z
    (hmin := 1/20) (by norm_num) (fun _=>le_rfl) hf (add_nonneg hn0 hs0)]
  rw [UncertainExecution.state_on_closed_segment r hr (fun _=>1/20) (fun _=>0)
    (fun _=>0) z (hmin := 1/20) (by norm_num) (fun _=>le_rfl) n hs0 hs1]
  exact segment_safe hrlo hrhi hz hn hs0 hs1

end LeanControls.PilotPath
#print axioms LeanControls.PilotPath.boxes_coarse
#print axioms LeanControls.PilotPath.coarse_bounds
#print axioms LeanControls.PilotPath.segment_safe
#print axioms LeanControls.PilotPath.actual_segment_safe
