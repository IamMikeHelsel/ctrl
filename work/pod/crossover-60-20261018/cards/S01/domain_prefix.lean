import HandoffAssembly

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold

/-- Actual source recursion, stable on every already-built closed prefix. -/
theorem state_later_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n k : ℕ) {t : ℝ} (ht : t ≤ grid (n+1)) :
    state m g R δ ε (n+k) t = state m g R δ ε n t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n+(k+1)=(n+k)+1 by omega]
    rw [state_step_before m g R δ ε (n+k)
      (ht.trans (grid_strict.monotone (by omega)))]
    exact ih

theorem actual_readings_later_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n k : ℕ) (b : Bool) {t : ℝ}
    (ht : t ∈ Icc 0 (grid (n+1))) :
    readings m ε (state m g R δ ε (n+k)) b t =
      readings m ε (state m g R δ ε n) b t := by
  unfold readings LeanControls.ConstructiveHold.measure
  split_ifs
  · rfl
  · have hsample : grid (index b t) ≤ grid (n+1) := by
      exact ((DelayedEntry.Witness.stamp_age ht.1 b).2.1).trans ht.2
    rw [state_later_prefix m g R δ ε n k hsample]

theorem command_later_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n k : ℕ) (b : Bool) {t : ℝ}
    (ht : t ∈ Icc 0 (grid (n+1))) :
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
      (readings m ε (state m g R δ ε (n+k))) b t =
    ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
      (readings m ε (state m g R δ ε n)) b t := by
  unfold ClearanceAdmission.actualCommand
  rw [actual_readings_later_prefix m g R δ ε n k b ht]

/-- Clock data are definitionally shared; only measurement field depends on state. -/
theorem schedule_clock_independent (m : State) (ε : ℕ → State)
    (f g : ℝ → State) :
    (schedule m ε f).sample=(schedule m ε g).sample ∧
    (schedule m ε f).dispatch=(schedule m ε g).dispatch ∧
    (schedule m ε f).index=(schedule m ε g).index := ⟨rfl,rfl,rfl⟩

/-- Horizon choice only selects a stable finite formula; it does not choose new controls. -/
def coveringStage (t : ℝ) : ℕ := Classical.choose (exists_nat_gt (2000*t))

theorem coveringStage_covers (t : ℝ) : t < grid (coveringStage t+1) := by
  have ht := Classical.choose_spec (exists_nat_gt (2000*t))
  change 2000*t < (coveringStage t : ℝ) at ht
  simp only [grid,Nat.cast_add,Nat.cast_one]
  linarith

def globalState (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State)
    (t : ℝ) : State := state m g R δ ε (coveringStage t) t

theorem state_agree_covered (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n k : ℕ) {t : ℝ}
    (hn : t ≤ grid (n+1)) (hk : t ≤ grid (k+1)) :
    state m g R δ ε n t = state m g R δ ε k t := by
  rcases le_total n k with hnk | hkn
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact (state_later_prefix m g R δ ε n j hn).symm
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkn
    exact state_later_prefix m g R δ ε k j hk

theorem globalState_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n : ℕ) {t : ℝ} (ht : t ≤ grid (n+1)) :
    globalState m g R δ ε t=state m g R δ ε n t :=
  state_agree_covered m g R δ ε (coveringStage t) n (coveringStage_covers t).le ht

theorem global_readings_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (n : ℕ) (b : Bool) {t : ℝ}
    (ht : t ∈ Icc 0 (grid (n+1))) :
    readings m ε (globalState m g R δ ε) b t =
      readings m ε (state m g R δ ε n) b t := by
  unfold readings LeanControls.ConstructiveHold.measure
  split_ifs
  · rfl
  · have hsample : grid (index b t) ≤ grid (n+1) :=
      ((DelayedEntry.Witness.stamp_age ht.1 b).2.1).trans ht.2
    rw [globalState_prefix m g R δ ε n hsample]

/-- Same fixed infinite streams as the finite source theorem, with no new ceiling. -/
theorem global_hold_ceiling {m : State} {g : ℝ → State}
    {rp dp : Bool → ℝ → ℝ} {R δ : ℕ → ℝ} {ε : ℕ → State}
    (pre : ClearanceAdmission.Execution h h m g rp dp (fun _ _ => 0) (fun _ _ => m))
    (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
    (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
    (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20)
    (hg : ClearanceAdmission.Guard m) :
    ∀ t, 0 ≤ t → globalState m g R δ ε t 0 ≤ 3/20-1277551/20100000000 := by
  intro t ht
  exact (finite_clearance pre hr hd he (coveringStage t) hg).2.2.2.2
    t ⟨ht,(coveringStage_covers t).le⟩

#print axioms coveringStage_covers
#print axioms state_agree_covered
#print axioms globalState_prefix
#print axioms global_readings_prefix
#print axioms global_hold_ceiling
#print axioms state_later_prefix
#print axioms actual_readings_later_prefix
#print axioms command_later_prefix
#print axioms schedule_clock_independent
end S01SourceBridge
