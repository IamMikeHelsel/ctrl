import FutureCommit

namespace RobotMotion.FutureCommit
open AccelerationAdmission VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def movingBase : Base := ⟨[(11/50,1/50)],0,1/5,7⟩
def returnTask : Task := ⟨0,13/25,17/10,1/10,1/2,15/2,10⟩
def pendingReturn : Pending := ⟨movingBase,returnTask,31/50,-1/50,[13/25,31/50]⟩
def onTime : Timing := ⟨57/100,57/100,1/100⟩
def tooLate : Timing := ⟨7/10,7/10,1/100⟩
def delayedCommit : Timing := ⟨57/100,7/10,1/100⟩
def changedBase : Base :=
  {movingBase with events := movingBase.events ++ [(14/25,1/1000)], version := 8}
def changedTask : Task := {returnTask with goal := 1/200, version := 11}
def tightTask : Task := {returnTask with deadline := 13/10}
def tightPending : Pending := {pendingReturn with task := tightTask}

/-- Three intentionally unsound mutants, each deleting one check category. -/
def noTimeCheck (p : Pending) (b : Base) (task : Task) : Bool :=
  certificateOK p && baseOK p b && taskOK p task

def noBaseCheck (p : Pending) (task : Task) (tm : Timing) : Bool :=
  certificateOK p && taskOK p task && timeOK p tm

def noTaskCheck (p : Pending) (b : Base) (tm : Timing) : Bool :=
  certificateOK p && baseOK p b && timeOK p tm

theorem pending_certificate_valid : certificateOK pendingReturn = true := by decide +kernel
theorem moving_positive_delay :
    returnTask.request < onTime.completion ∧
    onTime.completion-returnTask.request = 1/20 ∧
    onTime.commitTime + onTime.dispatch < pendingReturn.execution := by decide +kernel

theorem accepts_on_time : commitOK pendingReturn movingBase returnTask onTime = true := by decide +kernel
theorem rejects_late : commitOK pendingReturn movingBase returnTask tooLate = false := by decide +kernel
theorem rejects_delayed_commit :
    commitOK pendingReturn movingBase returnTask delayedCommit = false := by decide +kernel
theorem rejects_changed_base : commitOK pendingReturn changedBase returnTask onTime = false := by decide +kernel
theorem rejects_changed_task : commitOK pendingReturn movingBase changedTask onTime = false := by decide +kernel
theorem rejects_reused_history_version :
    commitOK pendingReturn {changedBase with version := movingBase.version} returnTask onTime = false := by decide +kernel
theorem rejects_reused_task_version :
    commitOK pendingReturn movingBase {changedTask with version := returnTask.version} onTime = false := by decide +kernel
theorem rejects_changed_offset :
    commitOK pendingReturn {movingBase with offset := 1/1000} returnTask onTime = false := by decide +kernel
theorem tight_candidate_list_fails :
    chooseVelocityExecution movingBase.width tightTask.speed tightTask.accel tightTask.jerkLimit
      tightTask.request tightTask.deadline movingBase.events pendingReturn.delta pendingReturn.candidates = none := by decide +kernel
theorem tight_commit_rejected : commitOK tightPending movingBase tightTask onTime = false := by decide +kernel

theorem late_mutant_accepts : noTimeCheck pendingReturn movingBase returnTask = true := by decide +kernel
theorem stale_base_mutant_accepts : noBaseCheck pendingReturn returnTask onTime = true := by decide +kernel
theorem stale_task_mutant_accepts : noTaskCheck pendingReturn movingBase onTime = true := by decide +kernel

/-- Integer equality alone loses the target even if the integer is reused. -/
theorem stale_base_wrong_target :
    finalTarget (appendPending pendingReturn changedBase) = 1/1000 ∧
    finalTarget (appendPending pendingReturn changedBase) ≠ returnTask.goal := by decide +kernel

theorem stale_task_wrong_target :
    finalTarget (appendPending pendingReturn movingBase) = 0 ∧
    finalTarget (appendPending pendingReturn movingBase) ≠ changedTask.goal := by decide +kernel

theorem late_rejection_retains_old :
    commit pendingReturn movingBase returnTask tooLate = movingBase := rejected_retains_live rejects_late

theorem changed_base_rejection_retains_live :
    commit pendingReturn changedBase returnTask onTime = changedBase := rejected_retains_live rejects_changed_base

noncomputable section

theorem ontime_actual_reference_contract :
    ReferenceContract movingBase returnTask
      (commit pendingReturn movingBase returnTask onTime) pendingReturn.execution :=
  (successful_commit_contract accepts_on_time).2.2.2.2.2

/-- The ongoing motion is nonzero when the delayed computation begins. -/
theorem moving_request_velocity :
    velocity (movingBase.width:ℝ) (realEvents movingBase.events) (returnTask.request:ℝ) = 23/480 ∧
    (0:ℝ) < velocity (movingBase.width:ℝ) (realEvents movingBase.events) (returnTask.request:ℝ) := by
  norm_num [movingBase,returnTask,realEvents,realEvent,velocity,response,F1,P]

/-- The successful reference is identical to the old jet throughout computation,
through the atomic commit, and through the declared future start. -/
theorem ontime_keeps_old_through_execution :
    ∀ t : ℝ, t ≤ 31/50 →
    referenceJet 0 (1/5) (realEvents (commit pendingReturn movingBase returnTask onTime).events) t =
    referenceJet 0 (1/5) (realEvents movingBase.events) t := by
  intro t ht
  exact ontime_actual_reference_contract.2.2.2.1 t ht

/-- Deleting timing permits a retroactive event. Its extra displacement at
commit is -8/375000 m. It cannot be equal to the already executed old prefix. -/
theorem late_mutant_changes_executed_position :
    position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (7/10) -
      position 0 (1/5) (realEvents movingBase.events) (7/10) = -8/375000 ∧
    position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (7/10) ≠
      position 0 (1/5) (realEvents movingBase.events) (7/10) := by
  norm_num [appendPending,pendingReturn,movingBase,realEvents,realEvent,position,response,F0,P]

/-- The wrong target is a real reference failure at the declared deadline. -/
theorem stale_base_real_deadline_failure :
    position 0 (1/5) (realEvents (appendPending pendingReturn changedBase).events) (17/10) = 1/1000 ∧
    position 0 (1/5) (realEvents (appendPending pendingReturn changedBase).events) (17/10) ≠
      (returnTask.goal:ℝ) := by
  norm_num [appendPending,pendingReturn,changedBase,movingBase,returnTask,realEvents,realEvent,position,response,F0,P]

theorem stale_task_real_deadline_failure :
    position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (17/10) = 0 ∧
    position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (17/10) ≠
      (changedTask.goal:ℝ) := by
  norm_num [appendPending,pendingReturn,movingBase,changedTask,returnTask,realEvents,realEvent,position,response,F0,P]

end
end RobotMotion.FutureCommit
