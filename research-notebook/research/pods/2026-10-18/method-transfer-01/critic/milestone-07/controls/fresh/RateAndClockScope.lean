import DelayedWitness
namespace CriticC4
open LeanControls DigitalHold WeightedEntry

/-- A rate floor alone does not support the C4 aggregate face certificate.
This tuple is not asserted to occur on an actual sampled trajectory. -/
theorem floor_only_face_outward :
    8 ≤ (16:ℝ) ∧
    0 < transformedRHS 16 DelayedEntry.residual
      ![-(51/50)*target,(101/100)*target,target] 2 := by
  norm_num [transformedRHS,DelayedEntry.residual,target]

/-- At the second dispatch, incoming and outgoing stamps differ. -/
theorem second_dispatch_stamps :
    DelayedEntry.Witness.stamp false (1/1000)=0 ∧
    DelayedEntry.Witness.stamp true (1/1000)=1/2000 := by
  norm_num [DelayedEntry.Witness.stamp,DelayedEntry.Witness.index,
    DelayedEntry.Witness.delay]

/-- The incoming reading's age is latency plus period, not only latency. -/
theorem second_dispatch_total_age :
    (1:ℝ)/1000-DelayedEntry.Witness.stamp false (1/1000)=1/1000 ∧
    (1:ℝ)/1000-DelayedEntry.Witness.stamp true (1/1000)=1/2000 := by
  rw [second_dispatch_stamps.1,second_dispatch_stamps.2]
  norm_num
end CriticC4
