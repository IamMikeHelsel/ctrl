import Kernel

open Set
noncomputable section
namespace RobotMotion
abbrev Event := ℝ × ℝ

def H (a t : ℝ) : ℝ := max (t-a) 0

def eventJerk (h : ℝ) (e : Event) (t : ℝ) : ℝ :=
  e.2 / h^4 * (H e.1 t - 4*H (e.1+h) t + 6*H (e.1+2*h) t -
    4*H (e.1+3*h) t + H (e.1+4*h) t)

def jerk (h : ℝ) (es : List Event) (t : ℝ) : ℝ := (es.map (fun e => eventJerk h e t)).sum

def eventRoots (h : ℝ) (e : Event) : List ℝ :=
  [e.1, e.1+h, e.1+2*h, e.1+3*h, e.1+4*h]

def roots (h : ℝ) (es : List Event) : List ℝ := es.flatMap (eventRoots h)

def guardPoints (h c : ℝ) (es : List Event) : Finset ℝ :=
  insert c ((roots h es).toFinset.filter (fun x => c ≤ x))

def Guard (h J c : ℝ) (es : List Event) : Prop :=
  ∀ x ∈ guardPoints h c es, |jerk h es x| ≤ J

lemma mem_guardPoints (h c : ℝ) (es : List Event) (x : ℝ) :
    x ∈ guardPoints h c es ↔ x = c ∨ x ∈ roots h es ∧ c ≤ x := by
  simp [guardPoints]

lemma H_affine {a L R t : ℝ} (hLt : L ≤ t) (htR : t ≤ R)
    (ha : a ≤ L ∨ R ≤ a) :
    (R-L)*H a t = (R-t)*H a L + (t-L)*H a R := by
  rcases ha with ha | ha
  · simp only [H,max_eq_left (by linarith : 0 ≤ t-a),
      max_eq_left (by linarith : 0 ≤ L-a),max_eq_left (by linarith : 0 ≤ R-a)]
    ring
  · simp only [H,max_eq_right (by linarith : t-a ≤ 0),
      max_eq_right (by linarith : L-a ≤ 0),max_eq_right (by linarith : R-a ≤ 0)]
    ring

lemma eventJerk_affine {h L R t : ℝ} (e : Event) (hLt : L ≤ t) (htR : t ≤ R)
    (hroot : ∀ a ∈ eventRoots h e, a ≤ L ∨ R ≤ a) :
    (R-L)*eventJerk h e t = (R-t)*eventJerk h e L + (t-L)*eventJerk h e R := by
  have h0 := H_affine hLt htR (hroot e.1 (by simp [eventRoots]))
  have h1 := H_affine hLt htR (hroot (e.1+h) (by simp [eventRoots]))
  have h2 := H_affine hLt htR (hroot (e.1+2*h) (by simp [eventRoots]))
  have h3 := H_affine hLt htR (hroot (e.1+3*h) (by simp [eventRoots]))
  have h4 := H_affine hLt htR (hroot (e.1+4*h) (by simp [eventRoots]))
  dsimp [eventJerk]
  linear_combination (e.2 / h^4) * h0 - 4*(e.2 / h^4)*h1 + 6*(e.2 / h^4)*h2 -
    4*(e.2 / h^4)*h3 + (e.2 / h^4)*h4

lemma jerk_affine {h L R t : ℝ} (es : List Event) (hLt : L ≤ t) (htR : t ≤ R)
    (hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a) :
    (R-L)*jerk h es t = (R-t)*jerk h es L + (t-L)*jerk h es R := by
  induction es with
  | nil => simp [jerk]
  | cons e es ih =>
    have he := eventJerk_affine (h:=h) e hLt htR (fun a ha => hroot a (by change a ∈ eventRoots h e ++ roots h es; exact List.mem_append_left _ ha))
    have hs := ih (fun a ha => hroot a (by simp [roots] at ha ⊢; exact Or.inr ha))
    simp only [jerk,List.map_cons,List.sum_cons] at *
    nlinarith

lemma eventJerk_tail {h t : ℝ} (hh : 0 < h) (e : Event) (ht : e.1+4*h ≤ t) :
    eventJerk h e t = 0 := by
  have h0 : 0 ≤ t-e.1 := by linarith
  have h1 : 0 ≤ t-(e.1+h) := by linarith
  have h2 : 0 ≤ t-(e.1+2*h) := by linarith
  have h3 : 0 ≤ t-(e.1+3*h) := by linarith
  have h4 : 0 ≤ t-(e.1+4*h) := by linarith
  simp only [eventJerk,H,max_eq_left h0,max_eq_left h1,max_eq_left h2,
    max_eq_left h3,max_eq_left h4]
  ring

lemma jerk_tail {h t : ℝ} (hh : 0 < h) (es : List Event)
    (ht : ∀ a ∈ roots h es, a ≤ t) : jerk h es t = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
  exact eventJerk_tail hh e (ht _ (List.mem_flatMap.mpr ⟨e,he,by simp [eventRoots]⟩))

lemma affine_abs_bound {L R t fL fR ft J : ℝ} (hLR : L < R)
    (hLt : L ≤ t) (htR : t ≤ R)
    (heq : (R-L)*ft = (R-t)*fL+(t-L)*fR)
    (hl : |fL| ≤ J) (hr : |fR| ≤ J) : |ft| ≤ J := by
  obtain ⟨hl1,hl2⟩ := abs_le.mp hl
  obtain ⟨hr1,hr2⟩ := abs_le.mp hr
  have a := mul_le_mul_of_nonneg_left hl2 (sub_nonneg.mpr htR)
  have b := mul_le_mul_of_nonneg_left hr2 (sub_nonneg.mpr hLt)
  have d := mul_le_mul_of_nonneg_left hl1 (sub_nonneg.mpr htR)
  have e := mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr hLt)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The finite set itself supplies adjacent endpoints. No external partition is assumed. -/
theorem future_knot_iff {h J c : ℝ} (hh : 0 < h) (hJ : 0 ≤ J) (es : List Event) :
    (∀ t, c ≤ t → |jerk h es t| ≤ J) ↔ Guard h J c es := by
  classical
  constructor
  · intro hall x hx
    rcases (mem_guardPoints h c es x).mp hx with rfl | ⟨_,hc⟩
    · exact hall _ le_rfl
    · exact hall x hc
  · intro hg t hct
    let E := guardPoints h c es
    by_cases htin : t ∈ E
    · exact hg t htin
    let lo := E.filter (fun x => x ≤ t)
    have hclo : c ∈ lo := by simp [lo,E,guardPoints,hct]
    have hlo : lo.Nonempty := ⟨c,hclo⟩
    let L := lo.max' hlo
    have hLlo : L ∈ lo := Finset.max'_mem lo hlo
    have hLE : L ∈ E := (Finset.mem_filter.mp hLlo).1
    have hLt : L ≤ t := (Finset.mem_filter.mp hLlo).2
    have hcL : c ≤ L := Finset.le_max' lo c hclo
    let hi := E.filter (fun x => t < x)
    by_cases hhi : hi.Nonempty
    · let R := hi.min' hhi
      have hRhi : R ∈ hi := Finset.min'_mem hi hhi
      have hRE : R ∈ E := (Finset.mem_filter.mp hRhi).1
      have htR : t < R := (Finset.mem_filter.mp hRhi).2
      have hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a := by
        intro a ha
        by_cases hac : a < c
        · exact Or.inl (le_trans hac.le hcL)
        have haE : a ∈ E := (mem_guardPoints h c es a).mpr (Or.inr ⟨ha,le_of_not_gt hac⟩)
        by_cases hat : a ≤ t
        · exact Or.inl (Finset.le_max' lo a (Finset.mem_filter.mpr ⟨haE,hat⟩))
        · exact Or.inr (Finset.min'_le hi a (Finset.mem_filter.mpr ⟨haE,lt_of_not_ge hat⟩))
      exact affine_abs_bound (lt_of_le_of_lt hLt htR) hLt htR.le
        (jerk_affine es hLt htR.le hroot) (hg L hLE) (hg R hRE)
    · have ht : ∀ a ∈ roots h es, a ≤ t := by
        intro a ha
        by_contra hat
        have hat' : t < a := lt_of_not_ge hat
        have haE : a ∈ E := (mem_guardPoints h c es a).mpr
          (Or.inr ⟨ha,le_trans hct hat'.le⟩)
        exact hhi ⟨a,Finset.mem_filter.mpr ⟨haE,hat'⟩⟩
      rw [jerk_tail hh es ht,abs_zero]
      exact hJ

end RobotMotion
