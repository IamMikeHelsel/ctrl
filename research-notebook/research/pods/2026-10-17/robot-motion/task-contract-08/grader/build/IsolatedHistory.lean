import TaskShape

open Set
noncomputable section
namespace RobotMotion.TaskContract

/-- The complete retained history has no pending or unfinished event after s. -/
def CompleteBy (h s : ℝ) (old : List Event) : Prop :=
  ∀ e ∈ old, e.1+4*h ≤ s

theorem completed_history {h s t : ℝ} (hh : 0 < h) (g0 : ℝ) (old : List Event)
    (hc : CompleteBy h s old) (ht : s ≤ t) :
    position g0 h old t = g0+(old.map Prod.snd).sum ∧
      velocity h old t = 0 ∧ acceleration h old t = 0 ∧ jerk h old t = 0 := by
  apply final_rest (T:=s-4*h) hh g0 old
  · intro e he
    have := hc e he
    linarith
  · linarith

/-- The old events are retained, and their completed contribution is the old goal. -/
theorem isolated_reference {h s t tau g0 a g : ℝ} (hh : 0 < h) (old : List Event)
    (hc : CompleteBy h s old) (ha : g0+(old.map Prod.snd).sum = a) (ht : s ≤ t) :
    position g0 h (old++[(tau,g-a)]) t = a+(g-a)*F0 ((t-tau)/h) := by
  have hold := (completed_history hh g0 old hc ht).1.trans ha
  unfold position
  rw [response_append]
  simp only [position,response,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] at *
  linarith

theorem isolated_hold {h s t tau g0 a g : ℝ} (hh : 0 < h) (old : List Event)
    (hc : CompleteBy h s old) (ha : g0+(old.map Prod.snd).sum = a)
    (hs : s ≤ t) (ht : t ≤ tau) :
    position g0 h (old++[(tau,g-a)]) t = a := by
  rw [isolated_reference hh old hc ha hs]
  have hz : (t-tau)/h ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
  rw [(left_tail hz).1]
  ring

theorem isolated_arrival {h s t tau g0 a g : ℝ} (hh : 0 < h) (old : List Event)
    (hc : CompleteBy h s old) (ha : g0+(old.map Prod.snd).sum = a)
    (hst : s ≤ tau) (ht : tau+4*h ≤ t) :
    position g0 h (old++[(tau,g-a)]) t = g := by
  have hs : s ≤ t := by linarith
  rw [isolated_reference hh old hc ha hs]
  have hz : 4 ≤ (t-tau)/h := (le_div_iff₀ hh).mpr (by linarith)
  rw [(right_tail hz).1]
  ring

theorem isolated_midpoint {h s tau g0 a g : ℝ} (hh : 0 < h) (old : List Event)
    (hc : CompleteBy h s old) (ha : g0+(old.map Prod.snd).sum = a) (hst : s ≤ tau) :
    position g0 h (old++[(tau,g-a)]) (tau+2*h) = a+(g-a)/2 := by
  rw [isolated_reference hh old hc ha (by linarith)]
  have he : (tau+2*h-tau)/h = 2 := by field_simp; ring
  rw [he,F0_two]
  ring

theorem event_jerk_bound {h : ℝ} (hh : 0 < h) (tau delta t : ℝ) :
    |eventJerk h (tau,delta) t| ≤ 2*|delta|/h^3 := by
  rw [eventJerk_eq hh]
  simp only [abs_div,abs_mul,abs_of_pos (pow_pos hh 3)]
  have hm := mul_le_mul_of_nonneg_left (F3_bound ((t-tau)/h)) (abs_nonneg delta)
  exact div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hh.le 3)

/-- A complete old tail and an isolated new-event bound imply safety of the full list. -/
theorem isolated_safe {h J s tau g0 a g : ℝ} (hh : 0 < h) (old : List Event)
    (hc : CompleteBy h s old) (hst : s ≤ tau)
    (hold : ∀ t : ℝ, 0 ≤ t → |jerk h old t| ≤ J)
    (hstep : 2*|g-a|/h^3 ≤ J) :
    ∀ t : ℝ, 0 ≤ t → |jerk h (old++[(tau,g-a)]) t| ≤ J := by
  intro t ht
  by_cases hbefore : t ≤ tau
  · rw [(prefix_preservation hh (le_refl tau) g0 (g-a) old hbefore).2.2.2]
    exact hold t ht
  · have hs : s ≤ t := by linarith
    have hz := (completed_history hh g0 old hc hs).2.2.2
    rw [jerk_append,hz]
    simp only [jerk,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,zero_add]
    exact (event_jerk_bound hh tau (g-a) t).trans hstep

/-- The executable exact guard accepts the retained list, using a proved sufficient bound. -/
theorem isolated_check {h J : ℚ} {s tau g0 a g : ℝ} (old : List QEvent)
    (accepted : check h J 0 old = true)
    (hc : CompleteBy (h:ℝ) s (realEvents old)) (hst : s ≤ tau)
    (et : ℚ) (ed : ℚ) (ht : (et:ℝ)=tau) (hd : (ed:ℝ)=g-a)
    (hstep : 2*|g-a|/(h:ℝ)^3 ≤ (J:ℝ)) :
    check h J 0 (old++[(et,ed)]) = true := by
  obtain ⟨hh,hJ,hbound⟩ := (check_real_iff h J 0 old).mp accepted
  apply (check_real_iff h J 0 (old++[(et,ed)])).mpr
  refine ⟨hh,hJ,?_⟩
  have hs := isolated_safe (g0:=g0) (by exact_mod_cast hh) (realEvents old)
    hc hst (by simpa using hbound) hstep
  simpa [realEvents,realEvent,ht,hd] using hs

theorem deadline_from_latency {s c tau D h L B tick Q : ℝ}
    (hcommit : c-s ≤ L+B+tick) (hqueue : tau-c ≤ Q)
    (hbudget : L+B+tick+Q+4*h ≤ D-s) : tau+4*h ≤ D := by linarith

end RobotMotion.TaskContract
