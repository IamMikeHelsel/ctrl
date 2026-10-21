import domain_clock
import HandoffWitness
noncomputable section
set_option autoImplicit false
namespace S02TieWitness
open Set LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
open LeanControls.ConstructedHandoff LeanControls.DetectorBridge LeanControls.DetectorSampling
open LeanControls.ConstructedHandoff.Witness S02Clock

def tiedLatency (n : ℕ) : ℝ := if n=632 then h else 0

theorem bounded_latency (n : ℕ) : 0≤tiedLatency n ∧ tiedLatency n≤h := by
  unfold tiedLatency
  split_ifs <;> norm_num

theorem actual_packet633_velocity :
    newReadings oldReads localHold 632 noise 633 1=19/1250 := by
  have hp := state_prefix (oldReads 632) (pending early (grid 632)) rates errors noise 3 (t:=h) le_rfl
  have hv : localHold h 1=51/5000 := by
    change state (oldReads 632) (pending early (grid 632)) rates errors noise 3 h 1=_
    rw [hp]
    norm_num [pending,early,DetectorReview.earlyState,UncertainLag.heldSolution,grid]
  have hg : grid 1=h := by norm_num [grid]
  norm_num [newReadings,ConstructiveHold.measure,hg,noise,ConstructiveHold.Witness.noise,hv]

theorem actual_packet633_fails_guard :
    ¬ClearancePolicy.Guard (newReadings oldReads localHold 632 noise 633) := by
  intro hg
  have hv := (abs_le.mp hg.2.1).2
  rw [actual_packet633_velocity] at hv
  norm_num at hv

/-- Latest-index-only coalescing of this tied batch discards the genuine first
qualifying packet. The assertion is about first-index preservation, not an
unsafe resulting trajectory or a claim that633 is a counterfactual reading. -/
theorem actual_tied_batch :
    First (newReadings oldReads localHold 632 noise) 632 ∧
    ¬ClearancePolicy.Guard (newReadings oldReads localHold 632 noise 633) ∧
    arrival tiedLatency 632=arrival tiedLatency 633 ∧
    release tiedLatency 632<release tiedLatency 633 := by
  refine ⟨first_decision_retained,actual_packet633_fails_guard,?_,?_⟩
  · norm_num [arrival,tiedLatency,grid]
  · exact release_strict tiedLatency (fun n => (bounded_latency n).2) (by norm_num)

#print axioms bounded_latency
#print axioms actual_packet633_velocity
#print axioms actual_packet633_fails_guard
#print axioms actual_tied_batch
end S02TieWitness
