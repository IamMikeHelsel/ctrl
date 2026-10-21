import domain_prefix

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set Filter LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold

/-- The diagonal path is one genuine source Execution on every compact horizon.
A strictly larger constructed horizon supplies the neighborhood at its final time. -/
theorem global_execution {m : State} {g : ℝ → State}
    {rp dp : Bool → ℝ → ℝ} {R δ : ℕ → ℝ} {ε : ℕ → State}
    (pre : ClearanceAdmission.Execution h h m g rp dp (fun _ _ => 0) (fun _ _ => m))
    (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
    (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
    (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20)
    (H : ℝ) (hH : 0 ≤ H) :
    ClearanceAdmission.Execution H h m (globalState m g R δ ε)
      (field rp R) (field dp δ) stamp (readings m ε (globalState m g R δ ε)) := by
  let n := coveringStage (H+1)
  have hlarge : H < grid (n+1) := by
    have hh := coveringStage_covers (H+1)
    change H+1 < grid (n+1) at hh
    linarith
  have finite := state_execution pre hr hd he n
  apply make_execution pre hr hd he
  · rw [globalState_prefix m g R δ ε 0 (by norm_num [grid])]
    rfl
  · have hc := finite.continuous.mono (Icc_subset_Icc_right hlarge.le)
    apply hc.congr
    intro t ht
    exact globalState_prefix m g R δ ε n (ht.2.trans hlarge.le)
  · intro t ht i
    have htlarge : t < grid (n+1) := ht.2.trans hlarge
    have hcmd : ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
        (readings m ε (globalState m g R δ ε)) true t =
        ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
        (readings m ε (state m g R δ ε n)) true t := by
      unfold ClearanceAdmission.actualCommand
      rw [global_readings_prefix m g R δ ε n true ⟨ht.1,htlarge.le⟩]
    rw [hcmd, globalState_prefix m g R δ ε n htlarge.le]
    apply (finite.right_ode t ⟨ht.1,htlarge⟩ i).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlarge)] with s hs
      exact congrArg (fun z => z i) (globalState_prefix m g R δ ε n hs.le)
    · exact congrArg (fun z => z i) (globalState_prefix m g R δ ε n htlarge.le)
  · intro t ht i
    have htlarge : t < grid (n+1) := ht.2.trans_lt hlarge
    have hcmd : ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
        (readings m ε (globalState m g R δ ε)) false t =
        ClearanceAdmission.actualCommand h (ClearanceAdmission.center m)
        (readings m ε (state m g R δ ε n)) false t := by
      unfold ClearanceAdmission.actualCommand
      rw [global_readings_prefix m g R δ ε n false ⟨ht.1.le,htlarge.le⟩]
    rw [hcmd, globalState_prefix m g R δ ε n htlarge.le]
    apply (finite.left_ode t ⟨ht.1,htlarge.le⟩ i).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlarge)] with s hs
      exact congrArg (fun z => z i) (globalState_prefix m g R δ ε n hs.le)
    · exact congrArg (fun z => z i) (globalState_prefix m g R δ ε n htlarge.le)

/-- Actual schedule theorem already includes local finiteness of dispatches. -/
theorem global_schedule (m : State) (g : ℝ → State) (R δ : ℕ → ℝ)
    (ε : ℕ → State) (H : ℝ) :
    ClearanceAdmission.IsSchedule H h (schedule m ε (globalState m g R δ ε))
      stamp (readings m ε (globalState m g R δ ε)) :=
  actual_schedule H m ε (globalState m g R δ ε)

#print axioms global_execution
#print axioms global_schedule
end S01SourceBridge
