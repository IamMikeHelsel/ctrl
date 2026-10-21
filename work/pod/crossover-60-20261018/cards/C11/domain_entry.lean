import Mathlib.Tactic
namespace C11Domain
noncomputable def robustEntry (v a : ℝ) : Prop :=
  ∀ ex ev ea : ℝ, |ex|≤1/1000 → |ev|≤1/100 → |ea|≤1/20 →
    |ex-v/4-a/32|≤2221/40000 ∧
    |ex+ev/4-a/32|≤2221/40000 ∧
    |ex+ev/2+ea/16+v/4+a/32|≤2221/40000

theorem coordinate_binding (mx mv ma ex ev ea : ℝ) :
    (mx+ex)-(mx+mv/4+ma/32)=ex-mv/4-ma/32 ∧
    (mx+ex)-(mx+mv/4+ma/32)+(mv+ev)/4=ex+ev/4-ma/32 ∧
    (mx+ex)-(mx+mv/4+ma/32)+(mv+ev)/2+(ma+ea)/16=
      ex+ev/2+ea/16+mv/4+ma/32 := by
  constructor
  · ring
  constructor <;> ring

theorem exact_guard (v a : ℝ) :
    robustEntry v a ↔ |8*v+a|≤928/625 ∧ |a|≤2081/1250 := by
  constructor
  · intro h
    have hp := h (1/1000) (1/100) (1/20) (by norm_num) (by norm_num) (by norm_num)
    have hn := h (-1/1000) (-1/100) (-1/20) (by norm_num) (by norm_num) (by norm_num)
    have hp1 := abs_le.mp hp.2.1
    have hn1 := abs_le.mp hn.2.1
    have hp2 := abs_le.mp hp.2.2
    have hn2 := abs_le.mp hn.2.2
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  · rintro ⟨hv,ha⟩ ex ev ea hx he hvv
    have hh := abs_le.mp hv
    have hh' := abs_le.mp ha
    have hx' := abs_le.mp hx
    have he' := abs_le.mp he
    have hvv' := abs_le.mp hvv
    refine ⟨?_,?_,?_⟩ <;> apply abs_le.mpr <;> constructor <;> linarith

theorem old_guard_implies_exact (v a : ℝ) (hv : |v|≤1/50) (ha : |a|≤5/4) :
    robustEntry v a := by
  apply (exact_guard v a).2
  have h0 := abs_le.mp hv
  have h1 := abs_le.mp ha
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem strict_widening : robustEntry (3/10) (-1) ∧ ¬(|(3/10:ℝ)|≤1/50) := by
  constructor
  · apply (exact_guard _ _).2; norm_num
  · norm_num

theorem source_widening_rejected : ¬robustEntry (3/100) (5/4) := by
  rw [exact_guard]; norm_num
end C11Domain
#print axioms C11Domain.coordinate_binding
#print axioms C11Domain.exact_guard
#print axioms C11Domain.old_guard_implies_exact
#print axioms C11Domain.strict_widening
#print axioms C11Domain.source_widening_rejected
