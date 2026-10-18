import RecoveryPath
import RecoveryHandoff
import TerminalCells
noncomputable section
namespace LeanControls.RecoveryBox
open Set SamplingClock
open UncertainLag (State heldSegment)

/-- Entry of the entire initial box, including its boundary, for every fixed
rate in the uncertainty interval. No terminal-set assumption is required. -/
theorem terminal_entry {r : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (hz : RecoveryPath.InitialBox z) :
    UncertainTravel.V (heldSegment r (5/4) z (-1)) ≤ 12 := by
  rcases hz with ⟨hxlo, hxhi, hvlo, hvhi, halo, hahi⟩
  apply RecoveryTerminal.terminal_energy hrlo hrhi
  · norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact ⟨hxlo, hxhi⟩
  · norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact ⟨hvlo, hvhi⟩
  · norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one]
    exact ⟨by linarith, hahi⟩

/-- The full recovery-and-handoff theorem for any continuous actual ODE
execution. Backup is exact -1 for 5/4 time units; sampled errors begin at handoff.
All trajectory coordinates, including acceleration, are continuous at handoff. -/
theorem travel_limit {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) {z : State} (hz : RecoveryPath.InitialBox z) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90)
    {f : ℝ → State} (hf : RecoveryHandoff.IsRecoveryExecution r (5/4) h e d z f)
    {t : ℝ} (ht : 0 ≤ t) : |f t 0| ≤ 2 := by
  exact RecoveryHandoff.travel_limit hrlo hrhi (by norm_num) h e d z hmin0 hlo hhi
    hbudget (fun s hs => RecoveryPath.backup_travel hrlo hrhi hz hs.1 hs.2)
    (terminal_entry hrlo hrhi hz) hf ht

/-- The actual terminal state has entered the old invariant region; no reset. -/
theorem actual_terminal_entry {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) {z : State} (hz : RecoveryPath.InitialBox z)
    {f : ℝ → State} (hf : RecoveryHandoff.IsRecoveryExecution r (5/4) h e d z f) :
    UncertainTravel.V (f (5/4)) ≤ 12 := by
  rw [RecoveryHandoff.backup_eq (ne_of_gt (by linarith : 0 < r)) h e d z hf
    (show (5/4:ℝ) ∈ Icc 0 (5/4) by norm_num)]
  exact terminal_entry hrlo hrhi hz

/-- This is a real extension of the certified starting states, not a restriction
of the previous ellipsoid. It does not imply the old controller is unsafe here. -/
theorem initial_outside {z : State} (hz : RecoveryPath.InitialBox z) :
    12 < UncertainTravel.V z := RecoveryPath.initial_outside hz

/-- An actual safe execution exists for every state and timing/error sequence
in the theorem. This rules out a vacuous universal safety specification. -/
theorem exists_safe_execution {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) {z : State} (hz : RecoveryPath.InitialBox z) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) :
    ∃ f : ℝ → State, RecoveryHandoff.IsRecoveryExecution r (5/4) h e d z f ∧
      (∀ t, 0 ≤ t → |f t 0| ≤ 2) := by
  let f := RecoveryHandoff.execution r (5/4) h e d z
  have hf : RecoveryHandoff.IsRecoveryExecution r (5/4) h e d z f :=
    RecoveryHandoff.constructed_isRecoveryExecution
      (ne_of_gt (by linarith : 0 < r)) (by norm_num) h e d z hmin0 hlo
  exact ⟨f, hf, fun _ ht => travel_limit hrlo hrhi h e d hz hmin0 hlo hhi hbudget hf ht⟩

end LeanControls.RecoveryBox
#print axioms LeanControls.RecoveryBox.terminal_entry
#print axioms LeanControls.RecoveryBox.travel_limit
#print axioms LeanControls.RecoveryBox.actual_terminal_entry
#print axioms LeanControls.RecoveryBox.initial_outside
#print axioms LeanControls.RecoveryBox.exists_safe_execution
