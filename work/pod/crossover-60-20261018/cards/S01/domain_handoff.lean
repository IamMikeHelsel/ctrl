import domain_prefix

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
open LeanControls.ConstructedHandoff LeanControls.DetectorBridge LeanControls.DetectorSampling

def globalTrajectory (f : ℝ → State) (m : ℕ → State) (k : ℕ)
    (R δ : ℕ → ℝ) (ε : ℕ → State) : ℝ → State :=
  join f (globalState (m k) (pending f (grid k)) R δ ε) (grid k)

theorem global_hold_prefix (f : ℝ → State) (m : ℕ → State) (k N : ℕ)
    (R δ : ℕ → ℝ) (ε : ℕ → State) (hN : 1 ≤ N) {s : ℝ} (hs : s ≤ grid N) :
    globalState (m k) (pending f (grid k)) R δ ε s=hold f m k N R δ ε s := by
  unfold hold
  apply globalState_prefix
  simpa [Nat.sub_add_cancel hN] using hs

theorem global_trajectory_prefix (f : ℝ → State) (m : ℕ → State) (k N : ℕ)
    (R δ : ℕ → ℝ) (ε : ℕ → State) (hN : 1 ≤ N) {t : ℝ}
    (ht : t ≤ grid k+grid N) :
    globalTrajectory f m k R δ ε t=trajectory f m k N R δ ε t := by
  unfold globalTrajectory trajectory join
  split_ifs
  · rfl
  · exact global_hold_prefix f m k N R δ ε hN (by linarith)

theorem global_newReadings_prefix (f : ℝ → State) (m : ℕ → State) (k N j : ℕ)
    (R δ : ℕ → ℝ) (ε : ℕ → State) (hN : 1 ≤ N) (hj : j ≤ k+N) :
    newReadings m (globalState (m k) (pending f (grid k)) R δ ε) k ε j =
    newReadings m (hold f m k N R δ ε) k ε j := by
  unfold newReadings
  split_ifs
  · rfl
  · unfold LeanControls.ConstructiveHold.measure
    split_ifs
    · rfl
    · rw [global_hold_prefix f m k N R δ ε hN
        (grid_strict.monotone (show j-k ≤ N by omega))]

/-- Full braking/decision/pending/hold path with the unchanged numerical ceiling,
 obtained from the actual source's assemblies, with one fixed detector index. -/
theorem global_handoff_ceiling {f : ℝ → State} {rL qL rB qB : ℝ → ℝ}
    {m : ℕ → State} (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    {k : ℕ} (hk : k ≤ 1058) (hf : First m k)
    {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
    (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
    (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20) :
    ∀ t, 0 ≤ t → globalTrajectory f m k R δ ε t 0 ≤ 3013722449/20100000000 := by
  intro t ht
  let N := coveringStage (t-grid k)+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hcover : t ≤ grid k+grid N := by
    have hc := coveringStage_covers (t-grid k)
    have hh := grid_strict.monotone (show coveringStage (t-grid k)+1 ≤ N by dsimp [N]; omega)
    linarith
  rw [global_trajectory_prefix f m k N R δ ε (by omega) hcover]
  exact (assemble ex hm hk hf hN hr hd he).safety t ⟨ht,hcover⟩

#print axioms global_hold_prefix
#print axioms global_trajectory_prefix
#print axioms global_newReadings_prefix
#print axioms global_handoff_ceiling
end S01SourceBridge
