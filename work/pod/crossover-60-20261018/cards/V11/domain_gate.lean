import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace V11BoundedAdmission
/-- Exact gate for a nonempty feasible interval; c has no assumed probabilistic meaning. -/
theorem interval_gate_iff (L U c E : ℝ) (hne : L ≤ U) :
    (∀ x, L ≤ x → x ≤ U → |x-c| ≤ E) ↔ c-E ≤ L ∧ U ≤ c+E := by
  constructor
  · intro hall
    have hL := abs_le.mp (hall L le_rfl hne)
    have hU := abs_le.mp (hall U hne le_rfl)
    constructor <;> linarith
  · rintro ⟨hL,hU⟩ x hxL hxU
    apply abs_le.mpr
    constructor <;> linarith
/-- Both bounds must apply to the actual same x. Compatibility alone is insufficient. -/
theorem two_bounds_intersection {x mu z a b : ℝ}
    (hp : |x-mu| ≤ a) (hm : |x-z| ≤ b) :
    max (mu-a) (z-b) ≤ x ∧ x ≤ min (mu+a) (z+b) := by
  rcases abs_le.mp hp with ⟨hp1,hp2⟩
  rcases abs_le.mp hm with ⟨hm1,hm2⟩
  exact ⟨max_le (by linarith) (by linarith), le_min (by linarith) (by linarith)⟩
/-- Prior-only worst-case error equals prior radius plus update displacement. -/
theorem prior_only_gate_iff (mu a d E : ℝ) (ha : 0 ≤ a) :
    (∀ x, |x-mu| ≤ a → |x-(mu+d)| ≤ E) ↔ a+|d| ≤ E := by
  constructor
  · intro hall
    have hl := hall (mu-a) (by apply abs_le.mpr; constructor <;> linarith)
    have hu := hall (mu+a) (by apply abs_le.mpr; constructor <;> linarith)
    rcases le_total 0 d with hd | hd
    · rw [abs_of_nonneg hd]
      have hh := (abs_le.mp hl).1
      linarith
    · rw [abs_of_nonpos hd]
      have hh := (abs_le.mp hu).2
      linarith
  · intro h x hx
    calc |x-(mu+d)| = |(x-mu)-d| := by congr 1; ring
      _ ≤ |x-mu|+|d| := abs_sub _ _
      _ ≤ a+|d| := by linarith
      _ ≤ E := h
/-- Preserving the same prior-only radius permits zero displacement only. -/
theorem no_nonzero_prior_only_move (mu a d : ℝ) (ha : 0 ≤ a) :
    (∀ x, |x-mu| ≤ a → |x-(mu+d)| ≤ a) ↔ d=0 := by
  rw [prior_only_gate_iff mu a d a ha]
  constructor
  · intro hh
    have hz : |d|=0 := by linarith [abs_nonneg d]
    exact abs_eq_zero.mp hz
  · rintro rfl
    simp
/-- Added scalar observation model: information mean equals gain-form mean. -/
theorem information_mean_eq (P R mu z : ℝ) (hP : 0 < P) (hR : 0 < R) :
    (mu/P+z/R)/(1/P+1/R) = mu+(P/(P+R))*(z-mu) := by
  have hp : P ≠ 0 := ne_of_gt hP
  have hr : R ≠ 0 := ne_of_gt hR
  have hs : P+R ≠ 0 := by positivity
  have hi : 1/P+1/R ≠ 0 := by positivity
  field_simp
  <;> ring
/-- Residual compatibility is existential, not an actual-inlier certificate. -/
theorem compatible_outlier_counterexample :
    |(-1:ℝ)-0| ≤ 1 ∧ |(21/20:ℝ)-0| ≤ 1+1/10 ∧
    ¬ |(-1:ℝ)-21/20| ≤ 1/10 ∧
    |(-1:ℝ)-(100/101)*(21/20)| = 206/101 ∧
    (1:ℝ)/101 < 1 ∧ 1 < 206/101 := by norm_num
/-- Valid hard bounds still do not make the covariance a deterministic squared-error bound. -/
theorem valid_bounds_covariance_counterexample :
    |(3/5:ℝ)-0| ≤ 1 ∧ |(3/5:ℝ)-1/2| ≤ 1/10 ∧
    |(3/5:ℝ)-50/101| = 53/505 ∧
    (1:ℝ)/101 < (53/505)^2 := by norm_num
/-- Sharp positive repair: keep the mean and carry a separate deterministic radius. -/
theorem positive_sharp_interval_gate :
    (∀ x : ℝ, 2/5 ≤ x → x ≤ 3/5 → |x-50/101| ≤ 53/505) ∧
    (∀ E : ℝ, (∀ x : ℝ, 2/5 ≤ x → x ≤ 3/5 → |x-50/101| ≤ E) → 53/505 ≤ E) := by
  constructor
  · apply (interval_gate_iff (2/5) (3/5) (50/101) (53/505) (by norm_num)).2
    norm_num
  · intro E hall
    have hh := (abs_le.mp (hall (3/5) (by norm_num) le_rfl)).2
    linarith
#print axioms interval_gate_iff
#print axioms two_bounds_intersection
#print axioms prior_only_gate_iff
#print axioms no_nonzero_prior_only_move
#print axioms information_mean_eq
#print axioms compatible_outlier_counterexample
#print axioms valid_bounds_covariance_counterexample
#print axioms positive_sharp_interval_gate
end V11BoundedAdmission
