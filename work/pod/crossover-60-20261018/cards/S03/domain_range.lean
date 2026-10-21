import LeanControls.Quantized
namespace S03Range
open LeanControls.PD LeanControls.SampledPD

theorem exact_support (x v : ℝ) :
    4*(control x v)^2+(13*x+v)^2=37*energy x v := by
  unfold LeanControls.SampledPD.control energy
  ring

theorem invariant_ranges {x v : ℝ} (hE : energy x v≤1/10) :
    |x|≤4/25 ∧ |v|≤9/25 ∧ |control x v|≤97/100 := by
  have hx : 4*x^2≤energy x v := by
    unfold energy
    nlinarith [sq_nonneg (x+v)]
  have hv : 4*v^2≤5*energy x v := by
    unfold energy
    nlinarith [sq_nonneg (5*x+v)]
  have hu := exact_support x v
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩
  all_goals nlinarith [sq_nonneg (13*x+v)]

/-- A sufficient raw-computation margin ensures the source clamp remains inactive. -/
theorem preclamp_range {x v a : ℝ} (hE : energy x v≤1/10)
    (ha : |a-control x v|≤3/100) : |a|≤1 := by
  have hu := (invariant_ranges hE).2.2
  have htri : |a|≤|a-control x v|+|control x v| := by
    simpa using abs_add_le (a-control x v) (control x v)
  linarith
end S03Range
#print axioms S03Range.exact_support
#print axioms S03Range.invariant_ranges
#print axioms S03Range.preclamp_range
