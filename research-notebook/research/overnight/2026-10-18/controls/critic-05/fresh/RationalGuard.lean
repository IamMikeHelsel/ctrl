import Knots

namespace RobotMotion

abbrev QEvent := ℚ × ℚ

def qH (a t : ℚ) : ℚ := max (t-a) 0

def qEventJerk (h : ℚ) (e : QEvent) (t : ℚ) : ℚ :=
  e.2 / h^4 * (qH e.1 t - 4*qH (e.1+h) t + 6*qH (e.1+2*h) t -
    4*qH (e.1+3*h) t + qH (e.1+4*h) t)

def qJerk (h : ℚ) (es : List QEvent) (t : ℚ) : ℚ :=
  (es.map (fun e => qEventJerk h e t)).sum

def qEventRoots (h : ℚ) (e : QEvent) : List ℚ :=
  [e.1,e.1+h,e.1+2*h,e.1+3*h,e.1+4*h]

def qRoots (h : ℚ) (es : List QEvent) : List ℚ := es.flatMap (qEventRoots h)

def qGuardPoints (h c : ℚ) (es : List QEvent) : List ℚ :=
  c :: (qRoots h es).filter (fun t => decide (c ≤ t))

/-- Authoritative executable exact-rational guard. Includes validity checks. -/
def check (h J c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ J) &&
    (qGuardPoints h c es).all (fun t => decide (|qJerk h es t| ≤ J))

noncomputable def realEvent (e : QEvent) : Event := ((e.1:ℝ),(e.2:ℝ))
noncomputable def realEvents (es : List QEvent) : List Event := es.map realEvent

lemma cast_qH (a t : ℚ) : ((qH a t : ℚ):ℝ) = H (a:ℝ) (t:ℝ) := by
  simp [qH,H,Rat.cast_max]

lemma cast_qEventJerk (h t : ℚ) (e : QEvent) :
    ((qEventJerk h e t : ℚ):ℝ) = eventJerk (h:ℝ) (realEvent e) (t:ℝ) := by
  simp [qEventJerk,eventJerk,realEvent,qH,H,Rat.cast_max]

lemma cast_qJerk (h t : ℚ) (es : List QEvent) :
    ((qJerk h es t : ℚ):ℝ) = jerk (h:ℝ) (realEvents es) (t:ℝ) := by
  induction es with
  | nil => simp [qJerk,jerk,realEvents]
  | cons e es ih =>
    simp only [qJerk,jerk,realEvents,List.map_cons,List.sum_cons,Rat.cast_add] at *
    rw [cast_qEventJerk,ih]

lemma cast_qEventRoots (h : ℚ) (e : QEvent) :
    (qEventRoots h e).map (fun x : ℚ => (x:ℝ)) = eventRoots (h:ℝ) (realEvent e) := by
  simp [qEventRoots,eventRoots,realEvent]

lemma cast_qRoots (h : ℚ) (es : List QEvent) :
    (qRoots h es).map (fun x : ℚ => (x:ℝ)) = roots (h:ℝ) (realEvents es) := by
  induction es with
  | nil => simp [qRoots,roots,realEvents]
  | cons e es ih =>
    simp only [qRoots,roots,realEvents,List.flatMap_cons,List.map_cons,List.map_append] at *
    rw [cast_qEventRoots,ih]

/-- Membership and order in the executable point list agree with the real set. -/
lemma cast_guardPoints (h c : ℚ) (es : List QEvent) (x : ℝ) :
    x ∈ guardPoints (h:ℝ) (c:ℝ) (realEvents es) ↔
      ∃ t ∈ qGuardPoints h c es, (t:ℝ) = x := by
  rw [mem_guardPoints,← cast_qRoots]
  simp only [List.mem_map,qGuardPoints,List.mem_cons,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨⟨t,ht,rfl⟩,hct⟩)
    · exact ⟨c,Or.inl rfl,rfl⟩
    · exact ⟨t,Or.inr ⟨ht,by exact_mod_cast hct⟩,rfl⟩
  · rintro ⟨t,(rfl | ⟨ht,hct⟩),rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨t,ht,rfl⟩,by exact_mod_cast hct⟩

lemma check_eq_true (h J c : ℚ) (es : List QEvent) :
    check h J c es = true ↔ 0 < h ∧ 0 ≤ J ∧
      ∀ t ∈ qGuardPoints h c es, |qJerk h es t| ≤ J := by
  simp [check,Bool.and_eq_true,List.all_eq_true,and_assoc]

/-- Exact executable-to-real equivalence; no Python run is a premise. -/
theorem check_real_iff (h J c : ℚ) (es : List QEvent) :
    check h J c es = true ↔ 0 < h ∧ 0 ≤ J ∧
      ∀ t : ℝ, (c:ℝ) ≤ t → |jerk (h:ℝ) (realEvents es) t| ≤ (J:ℝ) := by
  rw [check_eq_true]
  constructor
  · rintro ⟨hh,hJ,hcheck⟩
    refine ⟨hh,hJ,(future_knot_iff (by exact_mod_cast hh) (by exact_mod_cast hJ) _).mpr ?_⟩
    intro x hx
    obtain ⟨t,ht,rfl⟩ := (cast_guardPoints h c es x).mp hx
    rw [← cast_qJerk,← Rat.cast_abs]
    exact_mod_cast hcheck t ht
  · rintro ⟨hh,hJ,hall⟩
    refine ⟨hh,hJ,?_⟩
    intro t ht
    have hg := (future_knot_iff (by exact_mod_cast hh) (by exact_mod_cast hJ) (realEvents es)).mp hall
    have hp := (cast_guardPoints h c es (t:ℝ)).mpr ⟨t,ht,rfl⟩
    have hv := hg (t:ℝ) hp
    rw [← cast_qJerk,← Rat.cast_abs] at hv
    exact_mod_cast hv

end RobotMotion
