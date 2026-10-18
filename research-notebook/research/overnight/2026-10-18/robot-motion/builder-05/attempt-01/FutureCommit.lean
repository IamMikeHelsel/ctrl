import VelocityAdmission

namespace RobotMotion.FutureCommit
open AccelerationAdmission VelocityAdmission

/-- Exact retained reference data. A version is checked in addition to the data. -/
structure Base where
  events : List QEvent
  offset : ℚ
  width : ℚ
  version : Nat
  deriving DecidableEq

/-- Exact task meaning at request time. -/
structure Task where
  goal : ℚ
  request : ℚ
  deadline : ℚ
  speed : ℚ
  accel : ℚ
  jerkLimit : ℚ
  version : Nat
  deriving DecidableEq

/-- A pending result contains no current-time reinterpretation of its event. -/
structure Pending where
  base : Base
  task : Task
  execution : ℚ
  delta : ℚ
  candidates : List ℚ
  deriving DecidableEq

structure Timing where
  completion : ℚ
  commitTime : ℚ
  dispatch : ℚ
  deriving DecidableEq

def finalTarget (b : Base) : ℚ := b.offset + (b.events.map Prod.snd).sum

def certificateOK (p : Pending) : Bool :=
  decide (p.delta = p.task.goal - finalTarget p.base) &&
  decide (chooseVelocityExecution p.base.width p.task.speed p.task.accel p.task.jerkLimit
    p.task.request p.task.deadline p.base.events p.delta p.candidates = some p.execution)

def baseOK (p : Pending) (live : Base) : Bool := decide (live = p.base)
def taskOK (p : Pending) (live : Task) : Bool := decide (live = p.task)
def timeOK (p : Pending) (tm : Timing) : Bool :=
  decide (p.task.request ≤ tm.completion ∧ tm.completion ≤ tm.commitTime ∧
    0 ≤ tm.dispatch ∧ tm.commitTime + tm.dispatch ≤ p.execution)

/-- All predicates refer to one atomic read of the live state and ideal clock. -/
def commitOK (p : Pending) (live : Base) (task : Task) (tm : Timing) : Bool :=
  certificateOK p && baseOK p live && taskOK p task && timeOK p tm

def appendPending (p : Pending) (live : Base) : Base :=
  { live with events := live.events ++ [(p.execution,p.delta)], version := live.version+1 }

/-- Rejection preserves the live reference. It does not complete the pending task. -/
def commit (p : Pending) (live : Base) (task : Task) (tm : Timing) : Base :=
  if commitOK p live task tm then appendPending p live else live

lemma commitOK_iff (p : Pending) (live : Base) (task : Task) (tm : Timing) :
    commitOK p live task tm = true ↔
    (p.delta = p.task.goal - finalTarget p.base) ∧
    (chooseVelocityExecution p.base.width p.task.speed p.task.accel p.task.jerkLimit
      p.task.request p.task.deadline p.base.events p.delta p.candidates = some p.execution) ∧
    live = p.base ∧ task = p.task ∧ p.task.request ≤ tm.completion ∧
    tm.completion ≤ tm.commitTime ∧ 0 ≤ tm.dispatch ∧
    tm.commitTime + tm.dispatch ≤ p.execution := by
  simp [commitOK,certificateOK,baseOK,taskOK,timeOK,Bool.and_eq_true,and_assoc]

lemma rejected_retains_live {p : Pending} {live : Base} {task : Task} {tm : Timing}
    (h : commitOK p live task tm = false) : commit p live task tm = live := by
  simp [commit,h]

lemma accepted_appends_exact {p : Pending} {live : Base} {task : Task} {tm : Timing}
    (h : commitOK p live task tm = true) :
    commit p live task tm = appendPending p live := by simp [commit,h]

lemma realEvents_sum (es : List QEvent) :
    ((realEvents es).map Prod.snd).sum = (((es.map Prod.snd).sum : ℚ):ℝ) := by
  induction es with
  | nil => simp [realEvents]
  | cons e es ih => simpa [realEvents,realEvent] using congrArg (fun r : ℝ => (e.2:ℝ)+r) ih

noncomputable section

/-- Contract for the actual resulting retained history and the actual live task.
The bound begins at request time; the unchanged prefix covers all prior times. -/
def ReferenceContract (live : Base) (task : Task) (next : Base) (execution : ℚ) : Prop :=
  (∀ t : ℝ, (task.request:ℝ) ≤ t →
    |velocity (next.width:ℝ) (realEvents next.events) t| ≤ (task.speed:ℝ)) ∧
  (∀ t : ℝ, (task.request:ℝ) ≤ t →
    |acceleration (next.width:ℝ) (realEvents next.events) t| ≤ (task.accel:ℝ)) ∧
  (∀ t : ℝ, (task.request:ℝ) ≤ t →
    |jerk (next.width:ℝ) (realEvents next.events) t| ≤ (task.jerkLimit:ℝ)) ∧
  (∀ t : ℝ, t ≤ (execution:ℝ) →
    referenceJet (next.offset:ℝ) (next.width:ℝ) (realEvents next.events) t =
    referenceJet (live.offset:ℝ) (live.width:ℝ) (realEvents live.events) t) ∧
  (∀ t : ℝ, (task.deadline:ℝ) ≤ t →
    position (next.offset:ℝ) (next.width:ℝ) (realEvents next.events) t = (task.goal:ℝ) ∧
    velocity (next.width:ℝ) (realEvents next.events) t = 0 ∧
    acceleration (next.width:ℝ) (realEvents next.events) t = 0 ∧
    jerk (next.width:ℝ) (realEvents next.events) t = 0)

/-- Successful atomic commit transports the checked certificate to the live
history and requested goal. Equal version integers alone are never the premise. -/
theorem successful_commit_contract {p : Pending} {live : Base} {task : Task} {tm : Timing}
    (h : commitOK p live task tm = true) :
    p.execution ∈ p.candidates ∧
    tm.completion + tm.dispatch ≤ p.execution ∧
    tm.commitTime ≤ p.execution ∧
    (commit p live task tm).version = live.version + 1 ∧
    finalTarget (commit p live task tm) = task.goal ∧
    ReferenceContract live task (commit p live task tm) p.execution := by
  obtain ⟨hdelta,hselect,hlive,htask,hreq,hcomplete,hdispatch,hexec⟩ := (commitOK_iff ..).mp h
  have hmember := (chosen_velocity_is_checked hselect).1
  have hcontract := chosen_velocity_reference_contract hselect (p.base.offset:ℝ)
  have htarget : p.base.offset +
      (((realEvents (p.base.events ++ [(p.execution,p.delta)])).map Prod.snd).sum) =
      (p.task.goal:ℝ) := by
    rw [realEvents_sum]
    push_cast
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,add_zero,Prod.snd]
    have hd : (p.delta:ℝ) = (p.task.goal:ℝ) -
        ((p.base.offset:ℝ) + (((p.base.events.map Prod.snd).sum:ℚ):ℝ)) := by
      exact_mod_cast hdelta
    linarith
  rw [accepted_appends_exact h]
  subst live
  subst task
  refine ⟨hmember,by linarith,by linarith,rfl,?_,?_⟩
  · simp only [finalTarget,appendPending,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,Prod.snd,add_zero]
    dsimp [finalTarget] at hdelta
    linarith
  · obtain ⟨_,hv,ha,hj,hprefix,hrest⟩ := hcontract
    refine ⟨hv,ha,hj,hprefix,?_⟩
    intro t ht
    obtain ⟨hp,hv0,ha0,hj0⟩ := hrest t ht
    exact ⟨hp.trans htarget,hv0,ha0,hj0⟩

/-- The old reference remains unchanged during computation and dispatch slack.
This is a reference equality, not an assumption of physical state reset. -/
theorem successful_commit_preserves_executed_prefix
    {p : Pending} {live : Base} {task : Task} {tm : Timing}
    (h : commitOK p live task tm = true) {t : ℝ} (ht : t ≤ (tm.commitTime:ℝ)) :
    referenceJet ((commit p live task tm).offset:ℝ) ((commit p live task tm).width:ℝ)
      (realEvents (commit p live task tm).events) t =
    referenceJet (live.offset:ℝ) (live.width:ℝ) (realEvents live.events) t := by
  have hc := successful_commit_contract h
  exact hc.2.2.2.2.2.2.2.2.1 t (ht.trans (by exact_mod_cast hc.2.2.1))

end
end RobotMotion.FutureCommit
