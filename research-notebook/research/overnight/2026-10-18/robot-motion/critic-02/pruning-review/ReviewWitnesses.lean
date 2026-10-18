import HistoryPruning
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission
noncomputable section
namespace IndependentPruningReview
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem exact_boundary_signed :
    qRetained 1 4 [(0,-2),(10,7),(0,3),(1,-4)] = [(10,7),(1,-4)] ∧
    qCompletedOffset 1 4 [(0,-2),(10,7),(0,3),(1,-4)] = 1 := by decide +kernel

theorem just_before_boundary : qRetained 1 (3999/1000) [(0,-2),(0,3)] = [(0,-2),(0,3)] := by decide +kernel

theorem past_motion_zero : position 0 1 [(0,1)] 0 = 0 := by
  norm_num [position,response,F0,P]
theorem pruned_past_offset_one : position 1 1 [] 0 = 1 := by
  norm_num [position,response]
theorem active_motion_partial : position 0 1 [(0,1)] 1 = 1/24 := by
  norm_num [position,response,F0,P]

theorem zero_width_both_guards_false :
    check 0 1 0 [(0,1)] = false ∧ check 0 1 0 (qRetained 0 0 [(0,1)]) = false ∧
    checkAcceleration 0 1 0 [(0,1)] = false ∧
    checkAcceleration 0 1 0 (qRetained 0 0 [(0,1)]) = false := by decide +kernel

theorem negative_width_both_guards_false :
    check (-1) 1 0 [(0,1)] = false ∧
    check (-1) 1 0 (qRetained (-1) 0 [(0,1)]) = false ∧
    checkAcceleration (-1) 1 0 [(0,1)] = false ∧
    checkAcceleration (-1) 1 0 (qRetained (-1) 0 [(0,1)]) = false := by decide +kernel

theorem zero_width_jet_equality_fails : position 0 0 [(0,1)] 0 = 0 ∧ position 1 0 [] 0 = 1 := by
  norm_num [position,response,F0,P]

theorem admitted_old_tail_erased :
    checkAcceleration 1 0 4 [(0,100),(0,-99)] = true ∧
    qRetained 1 4 [(0,100),(0,-99)] = [] ∧
    qCompletedOffset 1 4 [(0,100),(0,-99)] = 1 := by decide +kernel

theorem future_equality_includes_endpoint :
    referenceJet 0 1 (realEvents [(0,-2),(10,7),(0,3),(1,-4)]) 4 =
    referenceJet 1 1 (realEvents [(10,7),(1,-4)]) 4 := by
  have h := rational_future_jet_eq (h:=1) (c:=4) (by norm_num) 0
    [(0,-2),(10,7),(0,3),(1,-4)] (t:=4) (by norm_num)
  have he := exact_boundary_signed
  rw [he.1,he.2] at h
  norm_num at h ⊢
  exact h

end IndependentPruningReview
