import ReversalProposal

namespace RobotMotion.AccelerationAdmission

/-- A candidate execution time. The caller supplies current/ready time c.
No velocity or physical-state claim is hidden in this check. -/
def checkTimedCandidate (h A J c D : ℚ) (es : List QEvent) (delta tau : ℚ) : Bool :=
  decide (c ≤ tau ∧ tau+4*h ≤ D ∧ ∀ e ∈ es, e.1+4*h ≤ D) &&
    check h J c (es++[(tau,delta)]) && checkAcceleration h A c (es++[(tau,delta)])

def chooseExecution (h A J c D : ℚ) (es : List QEvent) (delta : ℚ) : List ℚ → Option ℚ
  | [] => none
  | tau::rest => if checkTimedCandidate h A J c D es delta tau then some tau
      else chooseExecution h A J c D es delta rest

lemma chosen_is_checked {h A J c D delta tau : ℚ} {es : List QEvent} {candidates : List ℚ}
    (hc : chooseExecution h A J c D es delta candidates = some tau) :
    tau ∈ candidates ∧ checkTimedCandidate h A J c D es delta tau = true := by
  induction candidates with
  | nil => simp [chooseExecution] at hc
  | cons u rest ih =>
    by_cases hb : checkTimedCandidate h A J c D es delta u = true
    · simp [chooseExecution,hb] at hc
      subst tau
      exact ⟨by simp,hb⟩
    · simp [chooseExecution,hb] at hc
      obtain ⟨hm,hv⟩ := ih hc
      exact ⟨by simp [hm],hv⟩

/-- Rejection is complete for the supplied finite candidate list only. -/
lemma choose_none_iff (h A J c D : ℚ) (es : List QEvent) (delta : ℚ) (candidates : List ℚ) :
    chooseExecution h A J c D es delta candidates = none ↔
      ∀ tau ∈ candidates, checkTimedCandidate h A J c D es delta tau = false := by
  induction candidates with
  | nil => simp [chooseExecution]
  | cons u rest ih =>
    by_cases hb : checkTimedCandidate h A J c D es delta u = true
    · simp [chooseExecution,hb]
    · simp [chooseExecution,hb,ih]

noncomputable section

/-- A selected time preserves the committed prefix and meets acceleration,
jerk and reference-rest deadline obligations on the full retained history. -/
theorem chosen_reference_contract {h A J c D delta tau : ℚ} {es : List QEvent}
    {candidates : List ℚ} (hc : chooseExecution h A J c D es delta candidates = some tau)
    (g0 : ℝ) :
    c ≤ tau ∧
    (∀ t : ℝ, (c:ℝ) ≤ t → |acceleration (h:ℝ) (realEvents (es++[(tau,delta)])) t| ≤ (A:ℝ)) ∧
    (∀ t : ℝ, (c:ℝ) ≤ t → |jerk (h:ℝ) (realEvents (es++[(tau,delta)])) t| ≤ (J:ℝ)) ∧
    (∀ t : ℝ, t ≤ (tau:ℝ) → referenceJet g0 (h:ℝ) (realEvents (es++[(tau,delta)])) t =
      referenceJet g0 (h:ℝ) (realEvents es) t) ∧
    (∀ t : ℝ, (D:ℝ) ≤ t →
      position g0 (h:ℝ) (realEvents (es++[(tau,delta)])) t =
        g0+((realEvents (es++[(tau,delta)])).map Prod.snd).sum ∧
      velocity (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0 ∧
      acceleration (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0 ∧
      jerk (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0) := by
  obtain ⟨_,hcheck⟩ := chosen_is_checked hc
  simp only [checkTimedCandidate,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hct,hdt,hOld⟩,hJ⟩,hA⟩ := hcheck
  obtain ⟨hh,_,hjerk⟩ := (check_real_iff h J c _).mp hJ
  obtain ⟨_,_,hacc⟩ := (checkAcceleration_real_iff h A c _).mp hA
  have hhr : (0:ℝ) < h := by exact_mod_cast hh
  refine ⟨hct,hacc,hjerk,?_,?_⟩
  · intro t ht
    have hp := prefix_jet (h:=h) (c:=tau) (tau:=tau) hhr le_rfl g0 (delta:ℝ) (realEvents es) ht
    simpa [realEvents,realEvent] using hp
  · intro t ht
    apply final_rest (T:=(D:ℝ)-4*(h:ℝ)) hhr g0 _ ?_ (by linarith)
    intro e he
    obtain ⟨qe,hqe,rfl⟩ := List.mem_map.mp he
    have hq : qe.1+4*h ≤ D := by
      rcases List.mem_append.mp hqe with ho | hn
      · exact hOld qe ho
      · simp only [List.mem_singleton] at hn
        subst qe
        exact hdt
    dsimp [realEvent]
    have hr : (qe.1:ℝ)+4*(h:ℝ) ≤ (D:ℝ) := by exact_mod_cast hq
    linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The frozen failed immediate return is tried first and rejected. -/
theorem delayed_time_selected :
    chooseExecution (1/5) (1/2) (15/2) (13/25) (17/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by decide +kernel

/-- If the same list cannot finish before a shorter deadline, report no candidate. -/
theorem insufficient_candidate_deadline :
    chooseExecution (1/5) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = none := by decide +kernel

/-- A candidate before current/ready time is rejected even if its geometry is safe. -/
theorem past_candidate_rejected :
    checkTimedCandidate (1/5) (1/2) (15/2) (7/10) (17/10)
      [(11/50,1/50)] (-1/50) (31/50) = false := by decide +kernel

end
end RobotMotion.AccelerationAdmission
