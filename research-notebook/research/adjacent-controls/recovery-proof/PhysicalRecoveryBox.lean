import RecoveryBox
import PhysicalRecovery

/-! Concrete physical recovery from a box outside the original invariant.
No backup-path or terminal-energy condition is left as a theorem hypothesis.
Physical calibration and execution conformance remain external obligations. -/
noncomputable section
namespace LeanControls.PhysicalRecoveryBox
open UncertainLag (State)
open PhysicalTravel (normalizeState)

/-- Physical travel safety from the concrete normalized initial box. The plant
holds -U until 5*tau0/4, then starts its own sampled nominal-tau0 controller.
Errors are zero during backup and obey the combined budget only after handoff. -/
theorem travel_limit {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hrlo : 9/10 ≤ tau0/tau) (hrhi : tau0/tau ≤ 11/10)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) {z : State}
    (hz : RecoveryPath.InitialBox (normalizeState tau0 U z))
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau0/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U/90)
    {f : ℝ → State} (hf : PhysicalRecovery.IsRecoveryExecution tau0 tau U (5/4) h e d z f)
    {s : ℝ} (hs : 0 ≤ s) : |f s 0| ≤ 2*U*tau0^2 := by
  exact PhysicalRecovery.travel_limit htau0 htau hU hrlo hrhi (by norm_num)
    hmin0 h e d z hlo hhi hbudget
    (fun t ht => RecoveryPath.backup_travel hrlo hrhi hz ht.1 ht.2)
    (RecoveryBox.terminal_entry hrlo hrhi hz) hf hs

/-- The actual physical terminal state enters the normalized invariant, with
all coordinates carried through the switch and no reset. -/
theorem actual_terminal_entry {tau0 tau U : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hrlo : 9/10 ≤ tau0/tau) (hrhi : tau0/tau ≤ 11/10)
    (h e d : ℕ → ℝ) {z : State}
    (hz : RecoveryPath.InitialBox (normalizeState tau0 U z))
    {f : ℝ → State} (hf : PhysicalRecovery.IsRecoveryExecution tau0 tau U (5/4) h e d z f) :
    UncertainTravel.V (normalizeState tau0 U (f (tau0*(5/4)))) ≤ 12 := by
  exact RecoveryBox.actual_terminal_entry hrlo hrhi _ _ _ hz
    (PhysicalRecovery.normalize_isRecoveryExecution htau0 htau hU h e d z hf)

/-- A continuous physical execution satisfying the actual ODE and the concrete
all-time travel bound exists under these same assumptions. -/
theorem exists_safe_execution {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hrlo : 9/10 ≤ tau0/tau) (hrhi : tau0/tau ≤ 11/10)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) {z : State}
    (hz : RecoveryPath.InitialBox (normalizeState tau0 U z))
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau0/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U/90) :
    ∃ f : ℝ → State, PhysicalRecovery.IsRecoveryExecution tau0 tau U (5/4) h e d z f ∧
      (∀ s, 0 ≤ s → |f s 0| ≤ 2*U*tau0^2) := by
  let f := PhysicalRecovery.execution tau0 tau U (5/4) h e d z
  have hf : PhysicalRecovery.IsRecoveryExecution tau0 tau U (5/4) h e d z f :=
    PhysicalRecovery.constructed_isRecoveryExecution htau0 htau hU (by norm_num)
      hmin0 h e d z hlo
  exact ⟨f, hf, fun _ hs => travel_limit htau0 htau hU hrlo hrhi hmin0
    h e d hz hlo hhi hbudget hf hs⟩

end LeanControls.PhysicalRecoveryBox
#print axioms LeanControls.PhysicalRecoveryBox.travel_limit
#print axioms LeanControls.PhysicalRecoveryBox.actual_terminal_entry
#print axioms LeanControls.PhysicalRecoveryBox.exists_safe_execution
