module
public import FiniteHandoff
public import PilotPath
public import PilotSafety
@[expose] public section
noncomputable section
namespace LeanControls.PilotContinuation
open UncertainLag UncertainTravel IntervalChecker IntervalPilot

/-- Only the first25 holds and errors are fixed. The tail may vary within
its robust timing/error contract. The fixed unknown rate is preserved. -/
theorem actual_safe {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z)
    (h e d : ℕ → ℝ) {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    (hp : ∀ n<25, h n = 1/20) (ep : ∀ n<25, e n = 0) (dp : ∀ n<25, d n = 0)
    (htail : ∀ n, 25 ≤ n → h n ≤ 1/5)
    (btail : ∀ n, 25 ≤ n → |e n| + |d n| ≤ 1/90)
    {f : ℝ → State} (hf : ExecutionUniqueness.IsExecution r h e d z f)
    {t : ℝ} (ht : 0 ≤ t) : |f t 0| ≤ 2 := by
  have heq := FiniteHandoff.samples_congr_prefix r h e d (fun _=>1/20)
    (fun _=>0) (fun _=>0) z hp ep dp
  apply FiniteHandoff.actual_all_time_safe hrlo (by linarith) h e d z hmin0 hlo
    htail btail ?_ ?_ hf ht
  · intro n hn s hs0 hs1
    rw [heq n (by omega), ep n hn, dp n hn]
    rw [hp n hn] at hs1
    exact PilotPath.segment_safe hrlo hrhi hz hn hs0 hs1
  · rw [heq 25 le_rfl]
    exact PilotSafety.terminal_sample_energy hrlo hrhi hz

theorem exists_safe {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 73/80) (hz : BoxMem (boxes 0) z)
    (h e d : ℕ → ℝ) {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    (hp : ∀ n<25, h n = 1/20) (ep : ∀ n<25, e n = 0) (dp : ∀ n<25, d n = 0)
    (htail : ∀ n, 25 ≤ n → h n ≤ 1/5)
    (btail : ∀ n, 25 ≤ n → |e n| + |d n| ≤ 1/90) :
    ∃ f : ℝ → State, ExecutionUniqueness.IsExecution r h e d z f ∧
      ∀ t, 0 ≤ t → |f t 0| ≤ 2 := by
  have hf := ExecutionUniqueness.constructed_isExecution r (ne_of_gt (by linarith)) h e d z hmin0 hlo
  exact ⟨_, hf, fun t ht => actual_safe hrlo hrhi hz h e d hmin0 hlo hp ep dp htail btail hf ht⟩
end LeanControls.PilotContinuation
#print axioms LeanControls.PilotContinuation.actual_safe
#print axioms LeanControls.PilotContinuation.exists_safe
