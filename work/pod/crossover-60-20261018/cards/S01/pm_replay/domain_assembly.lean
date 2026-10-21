import domain_handoff
import domain_global

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
open LeanControls.ConstructedHandoff LeanControls.DetectorBridge LeanControls.DetectorSampling

section SourceAssumptions
variable {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State}
variable (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
variable {k : ℕ} (hk : k ≤ 1058) (hf : First m k)
variable {R δ : ℕ → ℝ} {ε : ℕ → State}
variable (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
variable (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
variable (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20)

include ex hm hk hf hr hd he

theorem global_old_pending_prefix : ∀ t ∈ Icc 0 (grid k+h),
    globalTrajectory f m k R δ ε t=f t := by
  intro t ht
  have hh : t ≤ grid k+grid 2 := by norm_num [grid,h] at *; linarith [ht.2]
  rw [global_trajectory_prefix f m k 2 R δ ε (by norm_num) hh]
  exact (assemble ex hm hk hf (by norm_num : 2≤2) hr hd he).prefix_eq t ht

theorem global_sensor_boxes (j : ℕ) :
    SensorBox (globalTrajectory f m k R δ ε (grid j))
      (newReadings m (globalState (m k) (pending f (grid k)) R δ ε) k ε j) := by
  let N := j+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hj : j ≤ k+N := by dsimp [N]; omega
  have ht : grid j ≤ grid k+grid N := by
    rw [(translated_clocks k N).1]
    exact grid_strict.monotone hj
  rw [global_trajectory_prefix f m k N R δ ε (by omega) ht,
    global_newReadings_prefix f m k N j R δ ε (by omega) hj]
  exact actual_readings (assemble ex hm hk hf hN hr hd he) hm he j hj

end SourceAssumptions

/-- The original first guard is selected once, before any horizon is chosen. -/
theorem exists_coherent_global_handoff {f : ℝ → State} {rL qL rB qB : ℝ → ℝ}
    {m : ℕ → State} (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
    (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
    (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20) :
    ∃ k, First m k ∧
      (∀ N, 2 ≤ N → Assembly f rL qL rB qB m k N R δ ε) ∧
      First (newReadings m (globalState (m k) (pending f (grid k)) R δ ε) k ε) k ∧
      (∀ t ∈ Icc 0 (grid k+h), globalTrajectory f m k R δ ε t=f t) ∧
      (∀ j, SensorBox (globalTrajectory f m k R δ ε (grid j))
        (newReadings m (globalState (m k) (pending f (grid k)) R δ ε) k ε j)) ∧
      ∀ t, 0 ≤ t → globalTrajectory f m k R δ ε t 0 ≤ 3013722449/20100000000 := by
  obtain ⟨k,hk,hg,hfirst,_⟩ := finite_first_guard ex hm
  have hf : First m k := ⟨hg,hfirst⟩
  refine ⟨k,hf,?_,new_readings_first hf,?_,?_,?_,⟩
  · intro N hN
    exact assemble ex hm hk hf hN hr hd he
  · exact global_old_pending_prefix ex hm hk hf hr hd he
  · exact global_sensor_boxes ex hm hk hf hr hd he
  · exact global_handoff_ceiling ex hm hk hf hr hd he

#print axioms global_old_pending_prefix
#print axioms global_sensor_boxes
#print axioms exists_coherent_global_handoff
end S01SourceBridge
