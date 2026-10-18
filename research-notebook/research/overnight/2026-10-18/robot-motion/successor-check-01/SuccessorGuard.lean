import AccelerationGuard
import Mathlib.Data.List.MinMax

open Set
namespace RobotMotion.AccelerationAdmission.SuccessorCheck

def qNext (ps : List ℚ) (L : ℚ) : Option ℚ :=
  (ps.filter (fun R => decide (L < R))).min?

def qCellPoints (h : ℚ) (es : List QEvent) (ps : List ℚ) (L : ℚ) : List ℚ :=
  match qNext ps L with
  | none => []
  | some R =>
    if qJerk h es L ≠ qJerk h es R ∧ L ≤ qCritical h es L R ∧ qCritical h es L R ≤ R
    then [qCritical h es L R] else []

def qPoints (h c : ℚ) (es : List QEvent) : List ℚ :=
  let ps := qGuardPoints h c es
  ps ++ ps.flatMap (fun L => qCellPoints h es ps L)

def checkSuccessor (h A c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ A) &&
    (qPoints h c es).all (fun t => decide (|qAcceleration h es t| ≤ A))

lemma next_iff (ps : List ℚ) (L R : ℚ) :
    qNext ps L = some R ↔ R ∈ ps ∧ L < R ∧ ∀ a ∈ ps, L < a → R ≤ a := by
  simp [qNext,List.min?_eq_some_iff,List.mem_filter,and_assoc]

lemma mem_cell (h : ℚ) (es : List QEvent) (ps : List ℚ) (L t : ℚ) :
    t ∈ qCellPoints h es ps L ↔ ∃ R, qNext ps L = some R ∧
      qJerk h es L ≠ qJerk h es R ∧ L ≤ qCritical h es L R ∧
      qCritical h es L R ≤ R ∧ t = qCritical h es L R := by
  cases hn : qNext ps L <;> simp [qCellPoints,hn,and_assoc]

lemma mem_points (h c : ℚ) (es : List QEvent) (t : ℚ) :
    t ∈ qPoints h c es ↔ t ∈ qGuardPoints h c es ∨
      ∃ L ∈ qGuardPoints h c es, ∃ R, qNext (qGuardPoints h c es) L = some R ∧
      qJerk h es L ≠ qJerk h es R ∧ L ≤ qCritical h es L R ∧
      qCritical h es L R ≤ R ∧ t = qCritical h es L R := by
  simp [qPoints,List.mem_flatMap,mem_cell]

lemma check_eq_true (h A c : ℚ) (es : List QEvent) :
    checkSuccessor h A c es = true ↔ 0 < h ∧ 0 ≤ A ∧
      ∀ t ∈ qPoints h c es, |qAcceleration h es t| ≤ A := by
  simp [checkSuccessor,Bool.and_eq_true,List.all_eq_true,and_assoc]

noncomputable section

def SuccessorGuard (h A c : ℝ) (es : List Event) : Prop :=
  (∀ x ∈ guardPoints h c es, |acceleration h es x| ≤ A) ∧
  (∀ L ∈ guardPoints h c es, ∀ R ∈ guardPoints h c es,
    L < R → (∀ a ∈ guardPoints h c es, L < a → R ≤ a) →
    jerk h es L ≠ jerk h es R → L ≤ critical h es L R → critical h es L R ≤ R →
    |acceleration h es (critical h es L R)| ≤ A)

theorem successor_future_iff {h A c : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    (es : List Event) :
    (∀ t, c ≤ t → |acceleration h es t| ≤ A) ↔ SuccessorGuard h A c es := by
  classical
  constructor
  · intro hall
    constructor
    · intro x hx
      rcases (mem_guardPoints h c es x).mp hx with rfl | ⟨_,hc⟩
      · exact hall _ le_rfl
      · exact hall x hc
    · intro L hL R _ _ _ _ hLc _
      have hcL : c ≤ L := by
        rcases (mem_guardPoints h c es L).mp hL with rfl | ⟨_,hc⟩
        · exact le_rfl
        · exact hc
      exact hall _ (le_trans hcL hLc)
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
        have hnext : ∀ a ∈ guardPoints h c es, L < a → R ≤ a := by
          intro a ha hLa
          by_cases hat : a ≤ t
          · have haL := Finset.le_max' lo a (Finset.mem_filter.mpr ⟨ha,hat⟩)
            exact False.elim (not_lt_of_ge haL hLa)
          · exact Finset.min'_le hi a (Finset.mem_filter.mpr ⟨ha,lt_of_not_ge hat⟩)
        exact hcritical L hLE R hRE hLR hnext heq (by rw [←he]; exact hx.1.le)
          (by rw [←he]; exact hx.2.le)
    · have ht : ∀ a ∈ roots h es, a ≤ t := by
        intro a ha
        by_contra hat
        have hat' : t < a := lt_of_not_ge hat
        have haE : a ∈ E := (mem_guardPoints h c es a).mpr
          (Or.inr ⟨ha,le_trans hct hat'.le⟩)
        exact hhi ⟨a,Finset.mem_filter.mpr ⟨haE,hat'⟩⟩
      rw [acceleration_tail hh es ht,abs_zero]
      exact hA


/-- The executable successor check has the same real all-future contract. -/
theorem checkSuccessor_real_iff (h A c : ℚ) (es : List QEvent) :
    checkSuccessor h A c es = true ↔ 0 < h ∧ 0 ≤ A ∧
      ∀ t : ℝ, (c:ℝ) ≤ t → |acceleration (h:ℝ) (realEvents es) t| ≤ (A:ℝ) := by
  rw [check_eq_true]
  constructor
  · rintro ⟨hh,hA,hcheck⟩
    refine ⟨hh,hA,(successor_future_iff (by exact_mod_cast hh) (by exact_mod_cast hA) _).mpr ?_⟩
    constructor
    · intro x hx
      obtain ⟨t,ht,rfl⟩ := (cast_guardPoints h c es x).mp hx
      have hv := hcheck t ((mem_points h c es t).mpr (Or.inl ht))
      rw [←cast_qAcceleration hh,←Rat.cast_abs]
      exact_mod_cast hv
    · intro L hL R hR hLR hnext hne hLc hcR
      obtain ⟨l,hl,rfl⟩ := (cast_guardPoints h c es L).mp hL
      obtain ⟨r,hr,rfl⟩ := (cast_guardPoints h c es R).mp hR
      have hn : qNext (qGuardPoints h c es) l = some r := by
        apply (next_iff _ _ _).mpr
        refine ⟨hr,by exact_mod_cast hLR,?_⟩
        intro a ha hla
        have har := (cast_guardPoints h c es (a:ℝ)).mpr ⟨a,ha,rfl⟩
        have hav := hnext (a:ℝ) har (by exact_mod_cast hla)
        exact_mod_cast hav
      have hneq : qJerk h es l ≠ qJerk h es r := by
        intro he
        apply hne
        rw [←cast_qJerk,←cast_qJerk,he]
      have hLq : l ≤ qCritical h es l r := by
        rw [←cast_critical] at hLc
        exact_mod_cast hLc
      have hRq : qCritical h es l r ≤ r := by
        rw [←cast_critical] at hcR
        exact_mod_cast hcR
      have hp := (mem_points h c es (qCritical h es l r)).mpr
        (Or.inr ⟨l,hl,r,hn,hneq,hLq,hRq,rfl⟩)
      rw [←cast_critical,←cast_qAcceleration hh,←Rat.cast_abs]
      exact_mod_cast hcheck _ hp
  · rintro ⟨hh,hA,hall⟩
    refine ⟨hh,hA,?_⟩
    intro t ht
    have guard_ge (u : ℚ) (hu : u ∈ qGuardPoints h c es) : c ≤ u := by
      simp only [qGuardPoints,List.mem_cons,List.mem_filter,decide_eq_true_eq] at hu
      rcases hu with rfl | ⟨_,hc⟩
      · exact le_rfl
      · exact hc
    have hct : c ≤ t := by
      rcases (mem_points h c es t).mp ht with ht | ⟨L,hL,R,_,_,hLc,_,rfl⟩
      · exact guard_ge t ht
      · exact le_trans (guard_ge L hL) hLc
    have hv := hall (t:ℝ) (by exact_mod_cast hct)
    rw [←cast_qAcceleration hh,←Rat.cast_abs] at hv
    exact_mod_cast hv

/-- Optimization preserves acceptance, including invalid parameter rejection. -/
theorem same_acceptance (h A c : ℚ) (es : List QEvent) :
    checkSuccessor h A c es = true ↔ checkAcceleration h A c es = true := by
  rw [checkSuccessor_real_iff,checkAcceleration_real_iff]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem interior_peak_rejected : checkSuccessor 1 (1/2) 0 [(0,1)] = false := by decide +kernel
theorem interior_peak_boundary : checkSuccessor 1 (2/3) 0 [(0,1)] = true := by decide +kernel
theorem current_time_rejected : checkSuccessor 1 (1/10) (7/2) [(0,1)] = false := by decide +kernel
theorem repeated_cancel : checkSuccessor 1 0 0 [(0,100),(0,-100)] = true := by decide +kernel
theorem expired_zero : checkSuccessor 1 0 4 [(0,1)] = true := by decide +kernel
theorem queued_peak_rejected : checkSuccessor 1 (1/2) 0 [(10,1)] = false := by decide +kernel
theorem zero_width_rejected : checkSuccessor 0 1 0 [] = false := by decide +kernel
theorem negative_width_rejected : checkSuccessor (-1) 1 0 [] = false := by decide +kernel
theorem negative_limit_rejected : checkSuccessor 1 (-1) 0 [] = false := by decide +kernel
theorem empty_accepted : checkSuccessor 1 0 0 [] = true := by decide +kernel
theorem immediate_return_rejected : checkSuccessor (1/5) (1/2) 0 [(11/50,1/50),(13/25,-1/50)] = false := by decide +kernel
theorem delayed_return_accepted : checkSuccessor (1/5) (1/2) 0 [(11/50,1/50),(31/50,-1/50)] = true := by decide +kernel

/-- Repeated and unsorted input knots do not change the strict successor. -/
theorem unsorted_repeated_successor : qNext [3,0,1,1,2] 1 = some 2 := by decide +kernel
theorem last_point_has_no_successor : qNext [3,0,1,1,2] 3 = none := by decide +kernel
/-- A genuine nonzero acceleration plateau with zero jerk is retained. -/
theorem flat_jerk_nonzero_acceleration :
    qJerk 1 [(0,1),(1,2),(2,3)] 2 = 0 ∧
    qJerk 1 [(0,1),(1,2),(2,3)] 3 = 0 ∧
    qAcceleration 1 [(0,1),(1,2),(2,3)] (5/2) = 1 := by decide +kernel
theorem plateau_history_bound : checkSuccessor 1 (15/7) 2 [(0,1),(1,2),(2,3)] = true := by decide +kernel

end
end RobotMotion.AccelerationAdmission.SuccessorCheck
