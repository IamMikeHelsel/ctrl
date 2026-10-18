import Reference

namespace RobotMotion

structure AdmissionState where
  events : List QEvent
  target : ℚ
  lastAdmission : ℚ
  lastExecution : ℚ
  deriving DecidableEq

structure Proposal where
  current : ℚ
  execution : ℚ
  target : ℚ
  deriving DecidableEq

def initial (g0 : ℚ) : AdmissionState := ⟨[],g0,0,0⟩

def causal (s : AdmissionState) (p : Proposal) : Prop :=
  s.lastAdmission ≤ p.current ∧ 0 ≤ p.current ∧ p.current ≤ p.execution ∧
    s.lastExecution ≤ p.execution
instance (s : AdmissionState) (p : Proposal) : Decidable (causal s p) := by
  unfold causal; infer_instance

def candidate (s : AdmissionState) (p : Proposal) : List QEvent :=
  s.events ++ [(p.execution,p.target-s.target)]

/-- Invalid timing, rejection and a no-change target retain every commitment. -/
def admit (h J : ℚ) (s : AdmissionState) (p : Proposal) : AdmissionState :=
  if causal s p then
    if p.target = s.target then {s with lastAdmission := p.current}
    else if check h J p.current (candidate s p) then
      ⟨candidate s p,p.target,p.current,p.execution⟩
    else {s with lastAdmission := p.current}
  else s

def run (h J : ℚ) : AdmissionState → List Proposal → AdmissionState
  | s, [] => s
  | s, p::ps => run h J (admit h J s p) ps

noncomputable def Safe (h J : ℚ) (s : AdmissionState) : Prop :=
  ∀ t : ℝ, 0 ≤ t → |jerk (h:ℝ) (realEvents s.events) t| ≤ (J:ℝ)

noncomputable def Invariant (h J g0 : ℚ) (s : AdmissionState) : Prop :=
  Safe h J s ∧ s.target = g0+(s.events.map Prod.snd).sum ∧
    0 ≤ s.lastAdmission ∧ 0 ≤ s.lastExecution ∧
    (∀ e ∈ s.events, 0 ≤ e.1 ∧ e.1 ≤ s.lastExecution) ∧
    (s.events = [] ∨ ∃ e ∈ s.events, e.1 = s.lastExecution)

lemma initial_invariant {h J g0 : ℚ} (hJ : 0 ≤ J) : Invariant h J g0 (initial g0) := by
  refine ⟨?_,by simp [initial],by simp [initial],by simp [initial],?_,Or.inl rfl⟩
  · intro t ht
    simpa [initial,realEvents,jerk] using (show (0:ℝ) ≤ (J:ℝ) by exact_mod_cast hJ)
  · simp [initial]

lemma candidate_cast (s : AdmissionState) (p : Proposal) :
    realEvents (candidate s p) = realEvents s.events ++
      [((p.execution:ℝ),((p.target-s.target:ℚ):ℝ))] := by
  simp [candidate,realEvents,realEvent]

/-- Acceptance supplies the future bound, while the new event is zero on the old prefix. -/
lemma accepted_safe {h J : ℚ} (hh : 0 < h) (s : AdmissionState) (p : Proposal)
    (hold : Safe h J s) (hcausal : causal s p)
    (hcheck : check h J p.current (candidate s p) = true) :
    ∀ t : ℝ, 0 ≤ t → |jerk (h:ℝ) (realEvents (candidate s p)) t| ≤ (J:ℝ) := by
  intro t ht
  by_cases htc : t ≤ (p.current:ℝ)
  · have hp := (prefix_preservation (show (0:ℝ) < (h:ℝ) by exact_mod_cast hh)
      (show (p.current:ℝ) ≤ (p.execution:ℝ) by exact_mod_cast hcausal.2.2.1)
      0 ((p.target-s.target:ℚ):ℝ) (realEvents s.events) htc).2.2.2
    rw [candidate_cast,hp]
    exact hold t ht
  · exact (check_real_iff h J p.current (candidate s p)).mp hcheck |>.2.2 t (le_of_lt (lt_of_not_ge htc))

/-- One step preserves the global bound and telescopes against the final committed target. -/
theorem admit_invariant {h J g0 : ℚ} (hh : 0 < h)
    (s : AdmissionState) (p : Proposal) (hs : Invariant h J g0 s) :
    Invariant h J g0 (admit h J s p) := by
  rcases hs with ⟨hsafe,hgoal,hc,ht,hevents,hmax⟩
  unfold admit
  split
  next hcausal =>
    split
    next heq => exact ⟨hsafe,hgoal,hcausal.2.1,ht,hevents,hmax⟩
    next hne =>
      split
      next hcheck =>
        refine ⟨accepted_safe hh s p hsafe hcausal hcheck,?_,hcausal.2.1,
          le_trans hcausal.2.1 hcausal.2.2.1,?_,?_⟩
        · simp only [candidate,List.map_append,List.map_cons,List.map_nil,List.sum_append,
            List.sum_cons,List.sum_nil,Prod.snd,add_zero]
          linarith
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ⟨(hevents e he).1,le_trans (hevents e he).2 hcausal.2.2.2⟩
          · simp only [List.mem_singleton] at he
            subst e
            exact ⟨le_trans hcausal.2.1 hcausal.2.2.1,le_rfl⟩
        · exact Or.inr ⟨(p.execution,p.target-s.target),by simp [candidate],rfl⟩
      next hreject => exact ⟨hsafe,hgoal,hcausal.2.1,ht,hevents,hmax⟩
  next hbad => exact ⟨hsafe,hgoal,hc,ht,hevents,hmax⟩

/-- Finite induction applies to arbitrary proposal lists; invalid timing retains state. -/
theorem run_invariant {h J g0 : ℚ} (hh : 0 < h) (s : AdmissionState)
    (ps : List Proposal) (hs : Invariant h J g0 s) : Invariant h J g0 (run h J s ps) := by
  induction ps generalizing s with
  | nil => exact hs
  | cons p ps ih => exact ih (admit h J s p) (admit_invariant hh s p hs)

theorem finite_admission_safe {h J g0 : ℚ} (hh : 0 < h) (hJ : 0 ≤ J)
    (ps : List Proposal) : Safe h J (run h J (initial g0) ps) :=
  (run_invariant hh (initial g0) ps (initial_invariant hJ)).1

theorem target_telescoping {h J g0 : ℚ} (hh : 0 < h) (hJ : 0 ≤ J)
    (ps : List Proposal) :
    (run h J (initial g0) ps).target = g0+
      ((run h J (initial g0) ps).events.map Prod.snd).sum :=
  (run_invariant hh (initial g0) ps (initial_invariant hJ)).2.1

/-- No step can erase a committed future event. -/
theorem admit_extends (h J : ℚ) (s : AdmissionState) (p : Proposal) :
    ∃ extra : List QEvent, (admit h J s p).events = s.events ++ extra := by
  unfold admit
  split
  · split
    · exact ⟨[],by simp⟩
    · split
      · exact ⟨[(p.execution,p.target-s.target)],rfl⟩
      · exact ⟨[],by simp⟩
  · exact ⟨[],by simp⟩

theorem run_extends (h J : ℚ) (s : AdmissionState) (ps : List Proposal) :
    ∃ extra : List QEvent, (run h J s ps).events = s.events ++ extra := by
  induction ps generalizing s with
  | nil => exact ⟨[],by simp [run]⟩
  | cons p ps ih =>
    obtain ⟨a,ha⟩ := admit_extends h J s p
    obtain ⟨b,hb⟩ := ih (admit h J s p)
    exact ⟨a++b,by simp only [run,hb,ha,List.append_assoc]⟩

theorem rejection_retains (h J : ℚ) (s : AdmissionState) (p : Proposal)
    (hcheck : check h J p.current (candidate s p) = false) :
    (admit h J s p).events = s.events ∧ (admit h J s p).target = s.target := by
  by_cases hc : causal s p <;> simp [admit,hcheck,hc]

theorem no_change_retains (h J : ℚ) (s : AdmissionState) (p : Proposal)
    (heq : p.target = s.target) :
    (admit h J s p).events = s.events ∧ (admit h J s p).target = s.target := by
  by_cases hc : causal s p <;> simp [admit,heq,hc]

lemma admit_clock_mono (h J : ℚ) (s : AdmissionState) (p : Proposal) :
    s.lastAdmission ≤ (admit h J s p).lastAdmission := by
  unfold admit
  split
  next hc => split <;> (try split) <;> exact hc.1
  next hc => exact le_rfl

/-- Every later finite run leaves the already executed reference jet unchanged. -/
lemma admit_prefix_jet {h J : ℚ} (hh : 0 < h) (g0 : ℝ)
    (s : AdmissionState) (p : Proposal) {t : ℝ} (ht : t ≤ (s.lastAdmission:ℝ)) :
    referenceJet g0 (h:ℝ) (realEvents (admit h J s p).events) t =
      referenceJet g0 (h:ℝ) (realEvents s.events) t := by
  unfold admit
  split
  next hc =>
    split
    next heq => rfl
    next hne =>
      split
      next hcheck =>
        rw [candidate_cast]
        exact prefix_jet (by exact_mod_cast hh)
          (show (p.current:ℝ) ≤ (p.execution:ℝ) by exact_mod_cast hc.2.2.1)
          g0 _ _ (le_trans ht (by exact_mod_cast hc.1))
      next hreject => rfl
  next hbad => rfl

theorem run_prefix_jet {h J : ℚ} (hh : 0 < h) (g0 : ℝ)
    (s : AdmissionState) (ps : List Proposal) {t : ℝ} (ht : t ≤ (s.lastAdmission:ℝ)) :
    referenceJet g0 (h:ℝ) (realEvents (run h J s ps).events) t =
      referenceJet g0 (h:ℝ) (realEvents s.events) t := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    change referenceJet g0 (h:ℝ) (realEvents (run h J (admit h J s p) ps).events) t = _
    rw [ih (admit h J s p) (le_trans ht (by exact_mod_cast admit_clock_mono h J s p))]
    exact admit_prefix_jet hh g0 s p ht

lemma sum_deltas_cast (es : List QEvent) :
    (((es.map Prod.snd).sum:ℚ):ℝ) = ((realEvents es).map Prod.snd).sum := by
  induction es with
  | nil => simp [realEvents]
  | cons e es ih => simpa [realEvents,realEvent] using congrArg (fun x : ℝ => (e.2:ℝ)+x) ih

/-- Rest starts four widths after the greatest accepted execution time.
The invariant includes future commitments; a nonempty history attains that maximum. -/
theorem run_final_rest {h J g0 : ℚ} (hh : 0 < h) (hJ : 0 ≤ J)
    (ps : List Proposal) {t : ℝ}
    (ht : ((run h J (initial g0) ps).lastExecution:ℝ)+4*(h:ℝ) ≤ t) :
    let s := run h J (initial g0) ps
    position (g0:ℝ) (h:ℝ) (realEvents s.events) t = (s.target:ℝ) ∧
    velocity (h:ℝ) (realEvents s.events) t = 0 ∧
    acceleration (h:ℝ) (realEvents s.events) t = 0 ∧
    jerk (h:ℝ) (realEvents s.events) t = 0 := by
  let s := run h J (initial g0) ps
  have hi := run_invariant hh (initial g0) ps (initial_invariant hJ)
  have hT : ∀ e ∈ realEvents s.events, e.1 ≤ (s.lastExecution:ℝ) := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
    change (q.1:ℝ) ≤ ((run h J (initial g0) ps).lastExecution:ℝ)
    exact_mod_cast (hi.2.2.2.2.1 q hq).2
  have hr := final_rest (by exact_mod_cast hh) (g0:ℝ) (realEvents s.events) hT ht
  have hg : (s.target:ℝ) = (g0:ℝ) + ((realEvents s.events).map Prod.snd).sum := by
    rw [← sum_deltas_cast,← Rat.cast_add]
    exact_mod_cast hi.2.1
  exact ⟨hr.1.trans hg.symm,hr.2⟩

theorem empty_rest (g0 h t : ℝ) :
    position g0 h [] t = g0 ∧ velocity h [] t = 0 ∧
    acceleration h [] t = 0 ∧ jerk h [] t = 0 := by
  simp [position,velocity,acceleration,response,jerk]

/-- This boundary receives one winner from the ready-packet batch.
Conflicting duplicate sequences must be rejected by the batch producer. -/
structure SequencedState where
  motion : AdmissionState
  watermark : ℤ
  deriving DecidableEq

def submit (h J : ℚ) (s : SequencedState) (sequence : ℤ)
    (ready : ℚ) (p : Proposal) : SequencedState :=
  if ready ≤ p.current ∧ s.watermark < sequence then
    ⟨admit h J s.motion p,sequence⟩
  else s

theorem submit_before_ready (h J : ℚ) (s : SequencedState) (sequence : ℤ)
    (ready : ℚ) (p : Proposal) (hnot : p.current < ready) :
    submit h J s sequence ready p = s := by simp [submit,not_le.mpr hnot]

theorem submit_stale_retains (h J : ℚ) (s : SequencedState) (sequence : ℤ)
    (ready : ℚ) (p : Proposal) (hstale : sequence ≤ s.watermark) :
    submit h J s sequence ready p = s := by simp [submit,not_lt.mpr hstale]

theorem submit_new_watermark (h J : ℚ) (s : SequencedState) (sequence : ℤ)
    (ready : ℚ) (p : Proposal) (hr : ready ≤ p.current) (hn : s.watermark < sequence) :
    (submit h J s sequence ready p).watermark = sequence := by simp [submit,hr,hn]

theorem submit_rejection_retains (h J : ℚ) (s : SequencedState) (sequence : ℤ)
    (ready : ℚ) (p : Proposal)
    (hcheck : check h J p.current (candidate s.motion p) = false) :
    (submit h J s sequence ready p).motion.events = s.motion.events ∧
    (submit h J s sequence ready p).motion.target = s.motion.target := by
  unfold submit
  split
  · exact rejection_retains h J s.motion p hcheck
  · exact ⟨rfl,rfl⟩

theorem submit_invariant {h J g0 : ℚ} (hh : 0 < h) (s : SequencedState)
    (sequence : ℤ) (ready : ℚ) (p : Proposal) (hs : Invariant h J g0 s.motion) :
    Invariant h J g0 (submit h J s sequence ready p).motion := by
  unfold submit
  split
  · exact admit_invariant hh s.motion p hs
  · exact hs

theorem run_last_execution_is_max {h J g0 : ℚ} (hh : 0 < h) (hJ : 0 ≤ J)
    (ps : List Proposal) (hne : (run h J (initial g0) ps).events ≠ []) :
    (∃ e ∈ (run h J (initial g0) ps).events,
      e.1 = (run h J (initial g0) ps).lastExecution) ∧
    (∀ e ∈ (run h J (initial g0) ps).events,
      e.1 ≤ (run h J (initial g0) ps).lastExecution) := by
  have hi := run_invariant hh (initial g0) ps (initial_invariant hJ)
  exact ⟨hi.2.2.2.2.2.resolve_left hne,fun e he => (hi.2.2.2.2.1 e he).2⟩

end RobotMotion
