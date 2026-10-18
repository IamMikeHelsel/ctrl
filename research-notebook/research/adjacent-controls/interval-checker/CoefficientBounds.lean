module
public import LeanControls.UncertainLag
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
@[expose] public section
noncomputable section
namespace LeanControls.CoefficientBounds

def expPoly (r : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 10, (-r/20)^m / m.factorial
def velocityPoly (r : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 9, (-r)^m * (1/20:ℝ)^(m+1) / (m+1).factorial
def positionPoly (r : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 8, (-r)^m * (1/20:ℝ)^(m+2) / (m+2).factorial

/-- One shared remainder for all three exact held-flow coefficients. -/
theorem shared_remainder {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) :
    ∃ δ : ℝ, |δ| ≤ ((1/1000000000000000000:ℚ):ℝ) ∧
      Real.exp (-r/20) = expPoly r + δ ∧
      (1-Real.exp (-r/20))/r = velocityPoly r - δ/r ∧
      (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ/r^2 := by
  let δ := Real.exp (-r/20) - expPoly r
  have habs : |-r/20| ≤ (11/200:ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have h := Real.exp_bound (x := -r/20) (by linarith : |-r/20| ≤ 1)
    (n := 10) (by norm_num)
  have hd : |δ| ≤ ((1/1000000000000000000:ℚ):ℝ) := by
    change |Real.exp (-r/20) - expPoly r| ≤ _
    change |Real.exp (-r/20) - expPoly r| ≤
      |-r/20|^10 * (11 / ((Nat.factorial 10:ℝ)*10)) at h
    calc
      _ ≤ |-r/20|^10 * (11 / ((Nat.factorial 10:ℝ)*10)) := h
      _ ≤ (11/200:ℝ)^10 * (11 / ((Nat.factorial 10:ℝ)*10)) := by gcongr
      _ ≤ _ := by norm_num [Nat.factorial]
  have he : Real.exp (-r/20) = expPoly r + δ := by dsimp [δ]; ring
  have hn : r ≠ 0 := ne_of_gt (by linarith)
  refine ⟨δ, hd, he, ?_, ?_⟩
  · rw [he]
    norm_num [expPoly, velocityPoly, Finset.sum_range_succ, Nat.factorial]
    field_simp
    ring
  · rw [he]
    norm_num [expPoly, positionPoly, Finset.sum_range_succ, Nat.factorial]
    field_simp
    ring

end LeanControls.CoefficientBounds
#print axioms LeanControls.CoefficientBounds.shared_remainder
