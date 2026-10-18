import Reference
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue

open Set
namespace RobotMotion.AccelerationAdmission

/-- Exact rational acceleration from the same truncated-power history. -/
def qEventAcceleration (h : ℚ) (e : QEvent) (t : ℚ) : ℚ :=
  e.2 / (2*h^4) * (qH e.1 t ^ 2 - 4*qH (e.1+h) t ^ 2 +
    6*qH (e.1+2*h) t ^ 2 - 4*qH (e.1+3*h) t ^ 2 + qH (e.1+4*h) t ^ 2)

def qAcceleration (h : ℚ) (es : List QEvent) (t : ℚ) : ℚ :=
  (es.map (fun e => qEventAcceleration h e t)).sum

def qCritical (h : ℚ) (es : List QEvent) (L R : ℚ) : ℚ :=
  (L*qJerk h es R-R*qJerk h es L)/(qJerk h es R-qJerk h es L)

/-- All pairs avoid trusting an external sorting or adjacency implementation.
Nonadjacent pairs can add redundant future sample points but cannot change exactness. -/
def qAccelerationPoints (h c : ℚ) (es : List QEvent) : List ℚ :=
  qGuardPoints h c es ++ (qGuardPoints h c es).flatMap (fun L =>
    (qGuardPoints h c es).flatMap (fun R =>
      if L < R ∧ qJerk h es L ≠ qJerk h es R ∧ c ≤ qCritical h es L R
      then [qCritical h es L R] else []))

def checkAcceleration (h A c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ A) &&
    (qAccelerationPoints h c es).all (fun t => decide (|qAcceleration h es t| ≤ A))

noncomputable section

lemma event_acceleration_eq {h : ℝ} (hh : 0 < h) (e : Event) (t : ℝ) :
    e.2 * F2 ((t-e.1)/h) / h^2 =
      e.2 / (2*h^4) * (H e.1 t ^ 2 - 4*H (e.1+h) t ^ 2 +
      6*H (e.1+2*h) t ^ 2 - 4*H (e.1+3*h) t ^ 2 + H (e.1+4*h) t ^ 2) := by
  simp only [F2,P,scaled_shift hh,max_scaled hh]
  field_simp <;> ring

lemma cast_qAcceleration {h : ℚ} (hh : 0 < h) (es : List QEvent) (t : ℚ) :
    ((qAcceleration h es t : ℚ):ℝ) = acceleration (h:ℝ) (realEvents es) (t:ℝ) := by
  induction es with
  | nil => simp [qAcceleration,acceleration,response,realEvents]
  | cons e es ih =>
    have he := event_acceleration_eq (by exact_mod_cast hh : (0:ℝ)<h) (realEvent e) (t:ℝ)
    simp [qEventAcceleration,realEvent,cast_qH] at he
    simp only [qAcceleration,List.map_cons,List.sum_cons,Rat.cast_add] at *
    rw [ih]
    simp only [acceleration,realEvents,List.map_cons,response,List.map_cons,List.sum_cons]
    simp only [qEventAcceleration,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_add,
      Rat.cast_pow,Rat.cast_ofNat,cast_qH]
    dsimp [realEvent] at he ⊢
    rw [add_div]
    linarith

/-- A continuous scalar function is bounded by endpoints and stationary values. -/
lemma interval_abs_bound {f df : ℝ → ℝ} {L R t A : ℝ}
    (hLR : L < R) (ht : t ∈ Icc L R) (hc : ContinuousOn f (Icc L R))
    (hd : ∀ x ∈ Ioo L R, HasDerivAt f (df x) x)
    (hL : |f L| ≤ A) (hR : |f R| ≤ A)
    (hcrit : ∀ x ∈ Ioo L R, df x = 0 → |f x| ≤ A) : |f t| ≤ A := by
  have upper {g dg : ℝ → ℝ} (hgc : ContinuousOn g (Icc L R))
      (hgd : ∀ x ∈ Ioo L R, HasDerivAt g (dg x) x)
      (hgL : g L ≤ A) (hgR : g R ≤ A)
      (hgcrit : ∀ x ∈ Ioo L R, dg x = 0 → g x ≤ A) : g t ≤ A := by
    obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hLR.le) hgc
    have hb : g x ≤ A := by
      by_cases hl : x = L
      · simpa [hl] using hgL
      by_cases hr : x = R
      · simpa [hr] using hgR
      have hi : x ∈ Ioo L R := ⟨lt_of_le_of_ne hx.1 (Ne.symm hl),lt_of_le_of_ne hx.2 hr⟩
      exact hgcrit x hi ((hm.isLocalMax (Icc_mem_nhds hi.1 hi.2)).hasDerivAt_eq_zero (hgd x hi))
    exact le_trans (hm ht) hb
  apply abs_le.mpr
  constructor
  · have hn := upper hc.neg (fun x hx => (hd x hx).neg) (neg_le.mpr (abs_le.mp hL).1)
      (neg_le.mpr (abs_le.mp hR).1) (fun x hx hz => neg_le.mpr (abs_le.mp (hcrit x hx (neg_eq_zero.mp hz))).1)
    change -f t ≤ A at hn
    linarith
  · exact upper hc hd (abs_le.mp hL).2 (abs_le.mp hR).2 (fun x hx hz => (abs_le.mp (hcrit x hx hz)).2)

lemma acceleration_tail {h t : ℝ} (hh : 0 < h) (es : List Event)
    (ht : ∀ a ∈ roots h es, a ≤ t) : acceleration h es t = 0 := by
  have h : response F2 h es t = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
    have he4 := ht (e.1+4*h) (List.mem_flatMap.mpr ⟨e,he,by simp [eventRoots]⟩)
    have hz : 4 ≤ (t-e.1)/h := (le_div_iff₀ hh).mpr (by linarith)
    simp [(right_tail hz).2.2.1]
  simp [acceleration,h]

/-- Degenerate affine jerk with an interior zero makes acceleration constant. -/
lemma flat_jerk_acceleration {h L R x : ℝ} (hh : 0 < h) (es : List Event)
    (hLR : L < R) (hx : x ∈ Icc L R)
    (hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a)
    (heq : jerk h es L = jerk h es R) (hz : jerk h es x = 0) :
    acceleration h es x = acceleration h es L := by
  have hzeroL : jerk h es L = 0 := by
    have ha := jerk_affine es hx.1 hx.2 hroot
    rw [hz,← heq] at ha
    nlinarith
  have hzero (y : ℝ) (hy : y ∈ Icc L R) : jerk h es y = 0 := by
    have ha := jerk_affine es hy.1 hy.2 hroot
    rw [← heq,hzeroL] at ha
    nlinarith
  have hb := (convex_Icc L R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (acceleration_deriv hh es y).hasDerivWithinAt)
    (fun y hy => by rw [hzero y hy]; simp : ∀ y ∈ Icc L R, ‖jerk h es y‖ ≤ (0:ℝ))
    (show L ∈ Icc L R from ⟨le_rfl,hLR.le⟩) hx
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using hb

lemma critical_identification {h L R x : ℝ} (es : List Event)
    (hx : x ∈ Icc L R) (hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a)
    (hne : jerk h es L ≠ jerk h es R) (hz : jerk h es x = 0) :
    x = (L*jerk h es R-R*jerk h es L)/(jerk h es R-jerk h es L) := by
  have ha := jerk_affine es hx.1 hx.2 hroot
  rw [hz] at ha
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hne))).mpr
  nlinarith


def critical (h : ℝ) (es : List Event) (L R : ℝ) : ℝ :=
  (L*jerk h es R-R*jerk h es L)/(jerk h es R-jerk h es L)

def AccelerationGuard (h A c : ℝ) (es : List Event) : Prop :=
  (∀ x ∈ guardPoints h c es, |acceleration h es x| ≤ A) ∧
  (∀ L ∈ guardPoints h c es, ∀ R ∈ guardPoints h c es,
    L < R → jerk h es L ≠ jerk h es R → c ≤ critical h es L R →
    |acceleration h es (critical h es L R)| ≤ A)

/-- An exact finite test for the all-future acceleration bound. -/
theorem future_acceleration_iff {h A c : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    (es : List Event) :
    (∀ t, c ≤ t → |acceleration h es t| ≤ A) ↔ AccelerationGuard h A c es := by
  classical
  constructor
  · intro hall
    constructor
    · intro x hx
      rcases (mem_guardPoints h c es x).mp hx with rfl | ⟨_,hc⟩
      · exact hall _ le_rfl
      · exact hall x hc
    · intro L _ R _ _ _ hc
      exact hall _ hc
  · rintro ⟨hg,hcritical⟩ t hct
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
      have hLR : L < R := lt_of_le_of_lt hLt htR
      have hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a := by
        intro a ha
        by_cases hac : a < c
        · exact Or.inl (le_trans hac.le hcL)
        have haE : a ∈ E := (mem_guardPoints h c es a).mpr (Or.inr ⟨ha,le_of_not_gt hac⟩)
        by_cases hat : a ≤ t
        · exact Or.inl (Finset.le_max' lo a (Finset.mem_filter.mpr ⟨haE,hat⟩))
        · exact Or.inr (Finset.min'_le hi a (Finset.mem_filter.mpr ⟨haE,lt_of_not_ge hat⟩))
      apply interval_abs_bound hLR ⟨hLt,htR.le⟩ (acceleration_continuous h es).continuousOn
        (fun x _ => acceleration_deriv hh es x) (hg L hLE) (hg R hRE)
      intro x hx hz
      by_cases heq : jerk h es L = jerk h es R
      · rw [flat_jerk_acceleration hh es hLR ⟨hx.1.le,hx.2.le⟩ hroot heq hz]
        exact hg L hLE
      · have he : x = critical h es L R := critical_identification es ⟨hx.1.le,hx.2.le⟩ hroot heq hz
        rw [he]
        exact hcritical L hLE R hRE hLR heq (by rw [← he]; exact le_trans hcL hx.1.le)
    · have ht : ∀ a ∈ roots h es, a ≤ t := by
        intro a ha
        by_contra hat
        have hat' : t < a := lt_of_not_ge hat
        have haE : a ∈ E := (mem_guardPoints h c es a).mpr
          (Or.inr ⟨ha,le_trans hct hat'.le⟩)
        exact hhi ⟨a,Finset.mem_filter.mpr ⟨haE,hat'⟩⟩
      rw [acceleration_tail hh es ht,abs_zero]
      exact hA

lemma mem_qAccelerationPoints (h c : ℚ) (es : List QEvent) (t : ℚ) :
    t ∈ qAccelerationPoints h c es ↔ t ∈ qGuardPoints h c es ∨
    ∃ L ∈ qGuardPoints h c es, ∃ R ∈ qGuardPoints h c es,
      L < R ∧ qJerk h es L ≠ qJerk h es R ∧ c ≤ qCritical h es L R ∧ t = qCritical h es L R := by
  simp [qAccelerationPoints,List.mem_flatMap,and_assoc]

lemma cast_critical (h : ℚ) (es : List QEvent) (L R : ℚ) :
    ((qCritical h es L R : ℚ):ℝ) = critical (h:ℝ) (realEvents es) (L:ℝ) (R:ℝ) := by
  simp [qCritical,critical,cast_qJerk]

lemma checkAcceleration_eq_true (h A c : ℚ) (es : List QEvent) :
    checkAcceleration h A c es = true ↔ 0 < h ∧ 0 ≤ A ∧
      ∀ t ∈ qAccelerationPoints h c es, |qAcceleration h es t| ≤ A := by
  simp [checkAcceleration,Bool.and_eq_true,List.all_eq_true,and_assoc]

/-- Executable exact rational guard is equivalent to a real all-time bound.
No external root finder, numeric sampling or desired acceleration bound is assumed. -/
theorem checkAcceleration_real_iff (h A c : ℚ) (es : List QEvent) :
    checkAcceleration h A c es = true ↔ 0 < h ∧ 0 ≤ A ∧
      ∀ t : ℝ, (c:ℝ) ≤ t → |acceleration (h:ℝ) (realEvents es) t| ≤ (A:ℝ) := by
  rw [checkAcceleration_eq_true]
  constructor
  · rintro ⟨hh,hA,hcheck⟩
    refine ⟨hh,hA,(future_acceleration_iff (by exact_mod_cast hh) (by exact_mod_cast hA) _).mpr ?_⟩
    constructor
    · intro x hx
      obtain ⟨t,ht,rfl⟩ := (cast_guardPoints h c es x).mp hx
      have hv := hcheck t ((mem_qAccelerationPoints h c es t).mpr (Or.inl ht))
      rw [← cast_qAcceleration hh,← Rat.cast_abs]
      exact_mod_cast hv
    · intro L hL R hR hLR hne hc
      obtain ⟨l,hl,rfl⟩ := (cast_guardPoints h c es L).mp hL
      obtain ⟨r,hr,rfl⟩ := (cast_guardPoints h c es R).mp hR
      have hneq : qJerk h es l ≠ qJerk h es r := by
        intro he
        apply hne
        rw [← cast_qJerk,← cast_qJerk,he]
      have hcr : c ≤ qCritical h es l r := by
        rw [← cast_critical] at hc
        exact_mod_cast hc
      have hp := (mem_qAccelerationPoints h c es (qCritical h es l r)).mpr
        (Or.inr ⟨l,hl,r,hr,by exact_mod_cast hLR,hneq,hcr,rfl⟩)
      rw [← cast_critical,← cast_qAcceleration hh,← Rat.cast_abs]
      exact_mod_cast hcheck _ hp
  · rintro ⟨hh,hA,hall⟩
    refine ⟨hh,hA,?_⟩
    intro t ht
    have hct : c ≤ t := by
      rcases (mem_qAccelerationPoints h c es t).mp ht with ht | ⟨L,_,R,_,_,_,hc,rfl⟩
      · simp only [qGuardPoints,List.mem_cons,List.mem_filter,decide_eq_true_eq] at ht
        rcases ht with rfl | ⟨_,hc⟩
        · exact le_rfl
        · exact hc
      · exact hc
    have hv := hall (t:ℝ) (by exact_mod_cast hct)
    rw [← cast_qAcceleration hh,← Rat.cast_abs] at hv
    exact_mod_cast hv

end
end RobotMotion.AccelerationAdmission
