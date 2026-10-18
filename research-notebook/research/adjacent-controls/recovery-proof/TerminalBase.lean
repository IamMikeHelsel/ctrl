module
public import LeanControls.UncertainLag
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.RecoveryTerminal
open Matrix BernsteinCertificate

def expApprox (q : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 10, (q/2)^m / m.factorial
def expError (q : ℝ) : ℝ :=
  |q/2|^10 * (11 / ((Nat.factorial 10 : ℝ) * 10))

/-- A rational certificate for an exponential at a point, using a half argument.
The exp bound and squaring are proved in the kernel; no native arithmetic oracle. -/
theorem exp_point {q a b lo hi : ℝ} (hq : |q/2| ≤ 1)
    (ha : 0 ≤ a) (hl : a ≤ expApprox q - expError q)
    (hu : expApprox q + expError q ≤ b)
    (hla : lo ≤ a^2) (hub : b^2 ≤ hi) :
    lo ≤ Real.exp q ∧ Real.exp q ≤ hi := by
  have h := Real.exp_bound (x := q/2) hq (n := 10) (by norm_num)
  change |Real.exp (q/2) - expApprox q| ≤ expError q at h
  have he := Real.exp_pos (q/2)
  have helo : a ≤ Real.exp (q/2) := by linarith [(abs_le.mp h).1]
  have hehi : Real.exp (q/2) ≤ b := by linarith [(abs_le.mp h).2]
  have heq : Real.exp q = Real.exp (q/2)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  constructor <;> nlinarith

theorem energy_ldl (z : Fin 3 → ℝ) :
    energy Generated.TravelQuarterLower.P z =
      ((38/5:ℚ):ℝ)*(z 0+((257/190:ℚ):ℝ)*z 1+((25/38:ℚ):ℝ)*z 2)^2 +
      ((29628/2375:ℚ):ℝ)*(z 1+((20465/29628:ℚ):ℝ)*z 2)^2 +
      ((1391479/740700:ℚ):ℝ)*(z 2)^2 := by
  simp [energy, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  norm_num
  ring

end LeanControls.RecoveryTerminal
