import domain_assembly

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set Filter LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
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

theorem global_trajectory_continuous (H : ℝ) :
    ContinuousOn (globalTrajectory f m k R δ ε) (Icc 0 H) := by
  let N := coveringStage (H-grid k)+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hcover : H ≤ grid k+grid N := by
    have hh := coveringStage_covers (H-grid k)
    have hn := grid_strict.monotone (show coveringStage (H-grid k)+1 ≤ N by dsimp [N]; omega)
    linarith
  have hc := (assemble ex hm hk hf hN hr hd he).continuous.mono
    (Icc_subset_Icc_right hcover)
  apply hc.congr
  intro t ht
  exact global_trajectory_prefix f m k N R δ ε (by omega) (ht.2.trans hcover)

theorem global_join_value :
    f (grid k)=globalState (m k) (pending f (grid k)) R δ ε 0 := by
  rw [global_hold_prefix f m k 2 R δ ε (by norm_num) (by norm_num [grid])]
  exact assembly_join_value (assemble ex hm hk hf (by norm_num : 2≤2) hr hd he)

theorem global_absolute_right {s : ℝ} (hs : 0 ≤ s) (i : Fin 3) :
    HasDerivWithinAt (fun t => globalTrajectory f m k R δ ε t i)
      (rhs (field (prefixRate rB (grid k)) R true s)
        (ClearanceAdmission.actualCommand h (ClearanceAdmission.center (m k))
          (readings (m k) ε (globalState (m k) (pending f (grid k)) R δ ε)) true s)
        (field (prefixError qB (grid k)) δ true s)
        (globalState (m k) (pending f (grid k)) R δ ε s) i)
      (Ici (grid k+s)) (grid k+s) := by
  have ep := global_execution (pending_execution ex hm hk hf.1) hr hd he (s+1) (by linarith)
  exact join_right_deriv (global_join_value ex hm hk hf hr hd he) hs
    (ep.right_ode s ⟨hs,by linarith⟩ i)

theorem global_absolute_left {s : ℝ} (hs : 0 < s) (i : Fin 3) :
    HasDerivWithinAt (fun t => globalTrajectory f m k R δ ε t i)
      (rhs (field (prefixRate rB (grid k)) R false s)
        (ClearanceAdmission.actualCommand h (ClearanceAdmission.center (m k))
          (readings (m k) ε (globalState (m k) (pending f (grid k)) R δ ε)) false s)
        (field (prefixError qB (grid k)) δ false s)
        (globalState (m k) (pending f (grid k)) R δ ε s) i)
      (Iic (grid k+s)) (grid k+s) := by
  have ep := global_execution (pending_execution ex hm hk hf.1) hr hd he (s+1) (by linarith)
  exact join_left_deriv (global_join_value ex hm hk hf hr hd he) hs
    (ep.left_ode s ⟨hs,by linarith⟩ i)
end SourceAssumptions

/-- One first guard binds the ongoing source Execution, schedule, and joined path. -/
theorem exists_infinite_execution {f : ℝ → State} {rL qL rB qB : ℝ → ℝ}
    {m : ℕ → State} (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
    (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
    (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20) :
    ∃ k, First m k ∧
      (∀ H, 0 ≤ H → ClearanceAdmission.Execution H h (m k)
        (globalState (m k) (pending f (grid k)) R δ ε)
        (field (prefixRate rB (grid k)) R) (field (prefixError qB (grid k)) δ)
        stamp (readings (m k) ε (globalState (m k) (pending f (grid k)) R δ ε))) ∧
      (∀ H, ClearanceAdmission.IsSchedule H h
        (schedule (m k) ε (globalState (m k) (pending f (grid k)) R δ ε))
        stamp (readings (m k) ε (globalState (m k) (pending f (grid k)) R δ ε))) ∧
      (∀ H, ContinuousOn (globalTrajectory f m k R δ ε) (Icc 0 H)) ∧
      (∀ t ∈ Icc 0 (grid k+h), globalTrajectory f m k R δ ε t=f t) ∧
      ∀ t, 0 ≤ t → globalTrajectory f m k R δ ε t 0 ≤ 3013722449/20100000000 := by
  obtain ⟨k,hk,hg,hfirst,_⟩ := finite_first_guard ex hm
  have hf : First m k := ⟨hg,hfirst⟩
  refine ⟨k,hf,?_,?_,?_,?_,?_,⟩
  · exact global_execution (pending_execution ex hm hk hf.1) hr hd he
  · exact global_schedule (m k) (pending f (grid k)) R δ ε
  · exact global_trajectory_continuous ex hm hk hf hr hd he
  · exact global_old_pending_prefix ex hm hk hf hr hd he
  · exact global_handoff_ceiling ex hm hk hf hr hd he

#print axioms global_trajectory_continuous
#print axioms global_join_value
#print axioms global_absolute_right
#print axioms global_absolute_left
#print axioms exists_infinite_execution
end S01SourceBridge
