import Mathlib.Tactic
namespace V01Ratio

theorem error_identity {a b da db : ℝ} (hb : b≠0) (hp : b+db≠0) :
    (a+da)/(b+db)-a/b=(da-(a/b)*db)/(b+db) := by
  field_simp
  <;> ring

theorem error_bound {a b da db e B m : ℝ}
    (hb : b≠0) (hm : 0<m) (hden : m≤b+db)
    (he : 0≤e) (hB : 0≤B) (ha : |a/b|≤B)
    (hda : |da|≤e) (hdb : |db|≤e) :
    |(a+da)/(b+db)-a/b|≤e*(1+B)/m := by
  have hp : 0<b+db := lt_of_lt_of_le hm hden
  rw [error_identity hb (ne_of_gt hp),abs_div,abs_of_pos hp]
  have hmul : |(a/b)*db|≤B*e := by
    rw [abs_mul]
    exact mul_le_mul ha hdb (abs_nonneg db) hB
  have hnum : |da-a/b*db|≤e*(1+B) := by
    have hh := abs_sub_le da (a/b*db)
    nlinarith only [hh,hda,hmul]
  calc
    _ ≤ (e*(1+B))/(b+db) := (div_le_div_iff_of_pos_right hp).mpr hnum
    _ ≤ (e*(1+B))/m := div_le_div_of_nonneg_left (by positivity) hm hden

#print axioms error_identity
#print axioms error_bound
end V01Ratio
