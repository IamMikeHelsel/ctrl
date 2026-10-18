import FutureCommitFixtures
namespace MotionReview
open RobotMotion RobotMotion.FutureCommit RobotMotion.AccelerationAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Generic replay of an already committed result always rejects, irrespective
-- of the second call's task or timing. This uses a reachable next state.
theorem duplicate_is_rejected {p : Pending} {b : Base} {t : Task} {tm : Timing}
    (h : commitOK p b t tm = true) (t2 : Task) (tm2 : Timing) :
    commitOK p (commit p b t tm) t2 tm2 = false := by
  simp [commitOK, committed_base_invalidates_pending h]

theorem duplicate_retains_result {p : Pending} {b : Base} {t : Task} {tm : Timing}
    (h : commitOK p b t tm = true) (t2 : Task) (tm2 : Timing) :
    commit p (commit p b t tm) t2 tm2 = commit p b t tm :=
  rejected_retains_live (duplicate_is_rejected h t2 tm2)

-- Truthful clock endpoints: exact equality is permitted; each broken ordering
-- rejects. These are supplied rational values, not clock measurements.
theorem exact_dispatch_boundary :
    commitOK pendingReturn movingBase returnTask ⟨57/100,61/100,1/100⟩ = true := by decide +kernel
theorem exact_zero_dispatch_boundary :
    commitOK pendingReturn movingBase returnTask ⟨57/100,31/50,0⟩ = true := by decide +kernel
theorem dispatch_overrun :
    commitOK pendingReturn movingBase returnTask ⟨57/100,61/100,11/1000⟩ = false := by decide +kernel
theorem completion_after_commit :
    commitOK pendingReturn movingBase returnTask ⟨3/5,57/100,1/100⟩ = false := by decide +kernel
theorem completion_before_request :
    commitOK pendingReturn movingBase returnTask ⟨1/2,57/100,1/100⟩ = false := by decide +kernel
theorem negative_dispatch :
    commitOK pendingReturn movingBase returnTask ⟨57/100,57/100,-1/100⟩ = false := by decide +kernel

def movedExecution : Pending := {pendingReturn with execution := 13/25}
def missingCandidate : Pending := {pendingReturn with candidates := [13/25]}
def changedWidth : Base := {movingBase with width := 1/4}
def changedLimits : Task := {returnTask with speed := 1/100}
def changedDeadline : Task := {returnTask with deadline := 13/10}
def noDelta : Pending := {pendingReturn with execution := 13/25, delta := 0}

theorem moved_execution_rejected :
    certificateOK movedExecution = false := by decide +kernel
theorem omitted_selected_candidate_rejected :
    certificateOK missingCandidate = false := by decide +kernel
theorem width_change_same_version_rejected :
    commitOK pendingReturn changedWidth returnTask onTime = false := by decide +kernel
theorem limit_change_same_version_rejected :
    commitOK pendingReturn movingBase changedLimits onTime = false := by decide +kernel
theorem deadline_change_same_version_rejected :
    commitOK pendingReturn movingBase changedDeadline onTime = false := by decide +kernel
theorem wrong_delta_rejected : certificateOK noDelta = false := by decide +kernel

-- If delta were not checked against the goal, a no-op is geometrically valid
-- and is in time, yet it still goes to the old +20 mm goal.
theorem no_delta_mutant_selects :
    RobotMotion.VelocityAdmission.chooseVelocityExecution movingBase.width
      returnTask.speed returnTask.accel returnTask.jerkLimit returnTask.request
      returnTask.deadline movingBase.events 0 [13/25,31/50] = some (13/25) := by decide +kernel

theorem no_delta_mutant_time :
    timeOK noDelta ⟨13/25,13/25,0⟩ = true := by decide +kernel

noncomputable section

theorem actual_result_speed_bound (s : ℝ) (hs : (13/25:ℝ) ≤ s) :
    |velocity ((commit pendingReturn movingBase returnTask onTime).width:ℝ)
      (realEvents (commit pendingReturn movingBase returnTask onTime).events) s| ≤ 1/10 := by
  have h := ontime_actual_reference_contract.1 s (by simpa [returnTask] using hs)
  simpa [returnTask] using h

theorem actual_result_deadline (s : ℝ) (hs : (17/10:ℝ) ≤ s) :
    position 0 (1/5) (realEvents (commit pendingReturn movingBase returnTask onTime).events) s = 0 ∧
    velocity (1/5) (realEvents (commit pendingReturn movingBase returnTask onTime).events) s = 0 ∧
    acceleration (1/5) (realEvents (commit pendingReturn movingBase returnTask onTime).events) s = 0 ∧
    jerk (1/5) (realEvents (commit pendingReturn movingBase returnTask onTime).events) s = 0 := by
  have h := ontime_actual_reference_contract.2.2.2.2 s (by simpa [returnTask] using hs)
  rw [accepted_appends_exact accepts_on_time] at h ⊢
  simpa [appendPending,movingBase,returnTask] using h

-- The candidate binding matters for the actual acceleration, not only metadata.
theorem moved_execution_real_failure :
    acceleration (1/5) (realEvents (appendPending movedExecution movingBase).events) (77/100) = -21/32 ∧
    |acceleration (1/5) (realEvents (appendPending movedExecution movingBase).events) (77/100)| > 1/2 := by
  norm_num [appendPending,movedExecution,pendingReturn,movingBase,realEvents,realEvent,acceleration,response,F2,P]

theorem no_delta_real_goal_failure :
    position 0 (1/5) (realEvents (appendPending noDelta movingBase).events) (17/10) = 1/50 ∧
    position 0 (1/5) (realEvents (appendPending noDelta movingBase).events) (17/10) ≠ (returnTask.goal:ℝ) := by
  norm_num [appendPending,noDelta,pendingReturn,movingBase,returnTask,realEvents,realEvent,position,response,F0,P]

theorem reachable_duplicate_real_failure :
    position 0 (1/5)
      (realEvents (appendPending pendingReturn (commit pendingReturn movingBase returnTask onTime)).events)
      (17/10) = -1/50 := by
  rw [first_commit_matches_once]
  exact duplicate_real_deadline_failure.1

end
end MotionReview
