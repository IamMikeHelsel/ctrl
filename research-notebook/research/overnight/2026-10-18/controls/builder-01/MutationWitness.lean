module
public import Settling
@[expose] public section
noncomputable section
namespace LeanControls.SettlingMutationWitness
open UncertainLag (State)
open RobustHold Settling

theorem faster_decay_face_is_false :
    ¬ transformedRHS 8 0 (![1,9/10,4/5] : State) 0 ≤ -(1/2)*weight 0 := by
  norm_num [transformedRHS,weight]

theorem zero_floor_face_is_false :
    ¬ transformedRHS 8 1 (![0,0,0] : State) 2 ≤ 0 := by
  norm_num [transformedRHS]

end LeanControls.SettlingMutationWitness
