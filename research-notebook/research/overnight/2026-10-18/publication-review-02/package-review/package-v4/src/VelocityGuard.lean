import VelocityBernstein

open Set
namespace RobotMotion.VelocityAdmission
open AccelerationAdmission AccelerationAdmission.SuccessorCheck

/-- Only the two interior Bernstein coefficients are added per adjacent cell.
The endpoint velocities are checked separately, including current time. -/
def qCellCoefficients (h : ℚ) (es : List QEvent) (ps : List ℚ) (L : ℚ) : List ℚ :=
  match qNext ps L with
  | none => []
  | some R => [qVelocity h es L+(R-L)*qAcceleration h es L/3,
      qVelocity h es R-(R-L)*qAcceleration h es R/3]

def qVelocityCoefficients (h c : ℚ) (es : List QEvent) : List ℚ :=
  let ps := qGuardPoints h c es
  ps.map (qVelocity h es) ++ ps.flatMap (qCellCoefficients h es ps)

/-- Sufficient velocity guard. This is not an exact speed-extremum test. -/
def checkVelocity (h V c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ V) &&
    (qVelocityCoefficients h c es).all (fun b => decide (|b| ≤ V))

lemma mem_cell_coefficients (h : ℚ) (es : List QEvent) (ps : List ℚ) (L b : ℚ) :
    b ∈ qCellCoefficients h es ps L ↔ ∃ R, qNext ps L = some R ∧
      (b = qVelocity h es L+(R-L)*qAcceleration h es L/3 ∨
       b = qVelocity h es R-(R-L)*qAcceleration h es R/3) := by
  cases hn : qNext ps L <;> simp [qCellCoefficients,hn]

lemma mem_coefficients (h c : ℚ) (es : List QEvent) (b : ℚ) :
    b ∈ qVelocityCoefficients h c es ↔
      (∃ t ∈ qGuardPoints h c es, qVelocity h es t = b) ∨
      ∃ L ∈ qGuardPoints h c es, ∃ R, qNext (qGuardPoints h c es) L = some R ∧
        (b = qVelocity h es L+(R-L)*qAcceleration h es L/3 ∨
         b = qVelocity h es R-(R-L)*qAcceleration h es R/3) := by
  simp [qVelocityCoefficients,List.mem_map,List.mem_flatMap,mem_cell_coefficients]

lemma checkVelocity_eq_true (h V c : ℚ) (es : List QEvent) :
    checkVelocity h V c es = true ↔ 0 < h ∧ 0 ≤ V ∧
      ∀ b ∈ qVelocityCoefficients h c es, |b| ≤ V := by
  simp [checkVelocity,Bool.and_eq_true,List.all_eq_true,and_assoc]

noncomputable section

/-- Endpoint and Bernstein coefficient obligations only on adjacent future cells. -/
def VelocityGuard (h V c : ℝ) (es : List Event) : Prop :=
  (∀ x ∈ guardPoints h c es, |velocity h es x| ≤ V) ∧
  (∀ L ∈ guardPoints h c es, ∀ R ∈ guardPoints h c es,
    L < R → (∀ a ∈ guardPoints h c es, L < a → R ≤ a) →
      |velocity h es L+(R-L)*acceleration h es L/3| ≤ V ∧
      |velocity h es R-(R-L)*acceleration h es R/3| ≤ V)

/-- Finite Bernstein checks imply a real all-future reference velocity bound.
No converse is claimed: a coefficient can exceed a cubic's maximum. -/
theorem future_velocity_of_guard {h V c : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (es : List Event) (hg : VelocityGuard h V c es) :
    ∀ t, c ≤ t → |velocity h es t| ≤ V := by
  classical
  obtain ⟨hend,hcell⟩ := hg
  intro t hct
  let E := guardPoints h c es
  by_cases htin : t ∈ E
  · exact hend t htin
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
    have hnext : ∀ a ∈ guardPoints h c es, L < a → R ≤ a := by
      intro a ha hLa
      by_cases hat : a ≤ t
      · have haL := Finset.le_max' lo a (Finset.mem_filter.mpr ⟨ha,hat⟩)
        exact False.elim (not_lt_of_ge haL hLa)
      · exact Finset.min'_le hi a (Finset.mem_filter.mpr ⟨ha,lt_of_not_ge hat⟩)
    obtain ⟨h1,h2⟩ := hcell L hLE R hRE hLR hnext
    exact velocity_cell_bound hh es hLR hLt htR.le hroot (hend L hLE) h1 h2 (hend R hRE)
  · have ht : ∀ a ∈ roots h es, a ≤ t := by
      intro a ha
      by_contra hat
      have hat' : t < a := lt_of_not_ge hat
      have haE : a ∈ E := (mem_guardPoints h c es a).mpr
        (Or.inr ⟨ha,le_trans hct hat'.le⟩)
      exact hhi ⟨a,Finset.mem_filter.mpr ⟨haE,hat'⟩⟩
    rw [velocity_tail hh es ht,abs_zero]
    exact hV

/-- Exact rational-to-real bridge for the finite sufficient obligations. -/
theorem checkVelocity_real_guard {h V c : ℚ} {es : List QEvent}
    (hc : checkVelocity h V c es = true) :
    0 < h ∧ 0 ≤ V ∧ VelocityGuard (h:ℝ) (V:ℝ) (c:ℝ) (realEvents es) := by
  obtain ⟨hh,hV,hcheck⟩ := (checkVelocity_eq_true h V c es).mp hc
  refine ⟨hh,hV,?_,?_⟩
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := (cast_guardPoints h c es x).mp hx
    have hv := hcheck _ ((mem_coefficients h c es _).mpr (Or.inl ⟨t,ht,rfl⟩))
    rw [←cast_qVelocity hh,←Rat.cast_abs]
    exact_mod_cast hv
  · intro L hL R hR hLR hnext
    obtain ⟨l,hl,rfl⟩ := (cast_guardPoints h c es L).mp hL
    obtain ⟨r,hr,rfl⟩ := (cast_guardPoints h c es R).mp hR
    have hn : qNext (qGuardPoints h c es) l = some r := by
      apply (next_iff _ _ _).mpr
      refine ⟨hr,by exact_mod_cast hLR,?_⟩
      intro a ha hla
      have har := (cast_guardPoints h c es (a:ℝ)).mpr ⟨a,ha,rfl⟩
      have hav := hnext (a:ℝ) har (by exact_mod_cast hla)
      exact_mod_cast hav
    have h1 := hcheck _ ((mem_coefficients h c es _).mpr (Or.inr ⟨l,hl,r,hn,Or.inl rfl⟩))
    have h2 := hcheck _ ((mem_coefficients h c es _).mpr (Or.inr ⟨l,hl,r,hn,Or.inr rfl⟩))
    rw [←cast_qVelocity hh,←cast_qVelocity hh,←cast_qAcceleration hh,←cast_qAcceleration hh]
    constructor <;> exact_mod_cast (by assumption)

/-- Passing the executable test bounds the actual retained reference at every
future real time, including the current time, knots and final zero-speed tail. -/
theorem checkVelocity_real_sound {h V c : ℚ} {es : List QEvent}
    (hc : checkVelocity h V c es = true) :
    0 < h ∧ 0 ≤ V ∧
      ∀ t : ℝ, (c:ℝ) ≤ t → |velocity (h:ℝ) (realEvents es) t| ≤ (V:ℝ) := by
  obtain ⟨hh,hV,hg⟩ := checkVelocity_real_guard hc
  exact ⟨hh,hV,future_velocity_of_guard (by exact_mod_cast hh) (by exact_mod_cast hV) _ hg⟩

end
end RobotMotion.VelocityAdmission
