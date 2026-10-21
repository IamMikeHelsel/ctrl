module
public import ClearancePolicy
@[expose] public section
noncomputable section
namespace S11Small
open LeanControls.DigitalHold LeanControls.WeightedEntry

/-- Prospective precision requirements, explicitly stronger than C5 sensors
and physical-error bounds. Only algebra, not a completed invariant execution. -/
theorem small_terminal_budget :
    let K : ℝ := 1/8120
    let M : ℝ := 1/10000+8*(1/1000000)+6*(1/100000)+(1/2)*(1/10000)
    let V := (203/25)*K
    let A := (1616/25)*K
    let U := (606/25)*K
    let W0 := 2*U+M
    let L0 := 8*V+12*A+6*U+6*W0
    V=1/1000 ∧ A<1/100 ∧ U+M<2 ∧
    M+(1/2000)*L0<3/10000 ∧ (3/10000:ℝ)<(38/15)*K := by
  norm_num

/-- Exact upper-face margin for the proposed small box and refined residual. -/
theorem small_third_face (r : ℝ) (hr0 : 8 ≤ r) (hr1 : r ≤ 12) :
    (-(41/5)+(21/40)*r)*(1/8120)+(r/16)*(3/10000)<0 := by
  linarith

#print axioms small_terminal_budget
#print axioms small_third_face
end S11Small
