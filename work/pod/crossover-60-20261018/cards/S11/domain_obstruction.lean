module
public import HandoffWitness
@[expose] public section
noncomputable section
namespace S11Obstruction
open LeanControls LeanControls.DigitalHold LeanControls.WeightedEntry LeanControls.ClearancePolicy
open LeanControls.ConstructedHandoff.Witness

theorem actual_reading :
    oldReads 632 = ![10051/156250,27/2500,-6/5] := by
  funext i
  fin_cases i <;> norm_num [oldReads,early,DetectorReview.earlyState,
    UncertainLag.heldSolution,DetectorSampling.sample]

theorem actual_reading_no_nonnegative_box (K c : ℝ) (hK : 0 ≤ K)
    (hc : (51/50)*K ≤ c) :
    ¬ (∀ i, |offsets (oldReads 632) i-c|+error i ≤ weight i*K) := by
  intro h
  have hh := h 2
  rw [actual_reading] at hh
  norm_num [offsets,error,weight] at hh
  have ha := neg_abs_le (10051/156250+(27/2500)/2+(-6/5)/16-c)
  norm_num at ha
  linarith

#print axioms actual_reading
#print axioms actual_reading_no_nonnegative_box
end S11Obstruction
