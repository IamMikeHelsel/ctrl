import AccelerationGuard

open Set
namespace RobotMotion.HistoryPruning

def qRetained (h c : ℚ) (es : List QEvent) : List QEvent :=
  es.filter (fun e => decide (c < e.1+4*h))

def qCompletedOffset (h c : ℚ) (es : List QEvent) : ℚ :=
  ((es.filter (fun e => decide (e.1+4*h ≤ c))).map Prod.snd).sum

noncomputable section

def retained (h c : ℝ) (es : List Event) : List Event :=
  es.filter (fun e => decide (c < e.1+4*h))

def completedOffset (h c : ℝ) (es : List Event) : ℝ :=
  ((es.filter (fun e => decide (e.1+4*h ≤ c))).map Prod.snd).sum

lemma response_pruned (f : ℝ → ℝ) (v : ℝ)
    (hf : ∀ z, 4 ≤ z → f z = v) {h c t : ℝ} (hh : 0 < h)
    (es : List Event) (ht : c ≤ t) :
    response f h es t = completedOffset h c es * v + response f h (retained h c es) t := by
  induction es with
  | nil => simp [response,completedOffset,retained]
  | cons e es ih =>
    by_cases he : e.1+4*h ≤ c
    · have hne : ¬c < e.1+4*h := not_lt.mpr he
      have hz : 4 ≤ (t-e.1)/h := (le_div_iff₀ hh).mpr (by linarith)
      simp only [response,List.map_cons,List.sum_cons] at ih ⊢
      simp [completedOffset,retained,he,hne,hf _ hz,response] at *
      linarith
    · have hlt : c < e.1+4*h := lt_of_not_ge he
      simp [completedOffset,retained,he,hlt,response] at *
      linarith

theorem future_jet_eq {h c t : ℝ} (hh : 0 < h) (g0 : ℝ)
    (es : List Event) (ht : c ≤ t) :
    referenceJet g0 h es t =
      referenceJet (g0+completedOffset h c es) h (retained h c es) t := by
  have h0 := response_pruned F0 1 (fun _ hz => (right_tail hz).1) hh es ht
  have h1 := response_pruned F1 0 (fun _ hz => (right_tail hz).2.1) hh es ht
  have h2 := response_pruned F2 0 (fun _ hz => (right_tail hz).2.2.1) hh es ht
  have h3 := response_pruned F3 0 (fun _ hz => (right_tail hz).2.2.2) hh es ht
  funext i
  fin_cases i <;>
    simp [referenceJet,position,velocity,acceleration,jerk_eq_response hh,h0,h1,h2,h3] <;> ring

lemma real_retained (h c : ℚ) (es : List QEvent) :
    realEvents (qRetained h c es) = retained (h:ℝ) (c:ℝ) (realEvents es) := by
  induction es with
  | nil => simp [realEvents,qRetained,retained]
  | cons e es ih =>
    have he : ((c:ℝ) < (e.1:ℝ)+4*(h:ℝ)) ↔ c < e.1+4*h := by norm_cast
    simp [realEvents,qRetained,retained,realEvent,List.filter_cons,he] at *
    split_ifs <;> simp_all [realEvent]

lemma real_completedOffset (h c : ℚ) (es : List QEvent) :
    ((qCompletedOffset h c es : ℚ):ℝ) = completedOffset (h:ℝ) (c:ℝ) (realEvents es) := by
  induction es with
  | nil => simp [qCompletedOffset,completedOffset,realEvents]
  | cons e es ih =>
    have he : ((e.1:ℝ)+4*(h:ℝ) ≤ (c:ℝ)) ↔ e.1+4*h ≤ c := by norm_cast
    simp [qCompletedOffset,completedOffset,realEvents,realEvent,List.filter_cons,he] at *
    split_ifs <;> simp_all [realEvent]

theorem rational_future_jet_eq {h c : ℚ} (hh : 0 < h) (g0 : ℝ)
    (es : List QEvent) {t : ℝ} (ht : (c:ℝ) ≤ t) :
    referenceJet g0 (h:ℝ) (realEvents es) t =
      referenceJet (g0+(qCompletedOffset h c es:ℝ)) (h:ℝ) (realEvents (qRetained h c es)) t := by
  rw [real_retained,real_completedOffset]
  exact future_jet_eq (by exact_mod_cast hh) g0 _ ht

theorem jerk_guard_pruned (h J c : ℚ) (es : List QEvent) :
    check h J c es = true ↔ check h J c (qRetained h c es) = true := by
  rw [check_real_iff,check_real_iff]
  constructor
  · rintro ⟨hh,hJ,hb⟩
    refine ⟨hh,hJ,?_⟩
    intro t ht
    have he := congrFun (rational_future_jet_eq hh 0 es ht) (3:Fin 4)
    change jerk (h:ℝ) (realEvents es) t = jerk (h:ℝ) (realEvents (qRetained h c es)) t at he
    rw [←he]
    exact hb t ht
  · rintro ⟨hh,hJ,hb⟩
    refine ⟨hh,hJ,?_⟩
    intro t ht
    have he := congrFun (rational_future_jet_eq hh 0 es ht) (3:Fin 4)
    change jerk (h:ℝ) (realEvents es) t = jerk (h:ℝ) (realEvents (qRetained h c es)) t at he
    rw [he]
    exact hb t ht

theorem acceleration_guard_pruned (h A c : ℚ) (es : List QEvent) :
    AccelerationAdmission.checkAcceleration h A c es = true ↔
      AccelerationAdmission.checkAcceleration h A c (qRetained h c es) = true := by
  rw [AccelerationAdmission.checkAcceleration_real_iff,AccelerationAdmission.checkAcceleration_real_iff]
  constructor
  · rintro ⟨hh,hA,hb⟩
    refine ⟨hh,hA,?_⟩
    intro t ht
    have he := congrFun (rational_future_jet_eq hh 0 es ht) (2:Fin 4)
    change acceleration (h:ℝ) (realEvents es) t =
      acceleration (h:ℝ) (realEvents (qRetained h c es)) t at he
    rw [←he]
    exact hb t ht
  · rintro ⟨hh,hA,hb⟩
    refine ⟨hh,hA,?_⟩
    intro t ht
    have he := congrFun (rational_future_jet_eq hh 0 es ht) (2:Fin 4)
    change acceleration (h:ℝ) (realEvents es) t =
      acceleration (h:ℝ) (realEvents (qRetained h c es)) t at he
    rw [he]
    exact hb t ht

theorem end_boundary_prunes : qRetained 1 4 [(0,1)] = [] := by decide +kernel
theorem end_boundary_keeps_position : qCompletedOffset 1 4 [(0,1)] = 1 := by decide +kernel
theorem premature_event_retained : qRetained 1 1 [(0,1)] = [(0,1)] := by decide +kernel
theorem queued_event_retained : qRetained 1 4 [(10,1)] = [(10,1)] := by decide +kernel
theorem signed_repeated_offset : qCompletedOffset 1 4 [(0,2),(0,-3),(1,4),(10,5)] = -1 := by decide +kernel
theorem signed_repeated_retained : qRetained 1 4 [(0,2),(0,-3),(1,4),(10,5)] = [(1,4),(10,5)] := by decide +kernel
theorem completed_nonzero_position : position 0 1 [(0,1)] 4 = 1 := by
  simpa using (final_rest (h:=1) (T:=0) (t:=4) (by norm_num) 0 [(0,1)]
    (by intro e he; simp only [List.mem_singleton] at he; subst e; norm_num) (by norm_num)).1

end
end RobotMotion.HistoryPruning
