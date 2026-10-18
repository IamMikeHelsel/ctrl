module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Discrete-time certificates

All arithmetic is over exact mathematical reals. These results do not certify
floating-point code or the correspondence of a model to a physical plant.
-/

public section

namespace LeanControls

/-- A nonnegative one-step multiplier gives an all-time geometric bound. -/
theorem geometric_bound {V : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, V (n + 1) ≤ q * V n) (n : ℕ) :
    V n ≤ q ^ n * V 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      V (n + 1) ≤ q * V n := hstep n
      _ ≤ q * (q ^ n * V 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * V 0 := by ring

/-- A contracting nonnegative certificate tends to zero. -/
theorem geometric_tendsto_zero {V : ℕ → ℝ} {q : ℝ}
    (hV : ∀ n, 0 ≤ V n) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n, V (n + 1) ≤ q * V n) :
    Filter.Tendsto V Filter.atTop (nhds 0) := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (V 0)
  simp only [zero_mul] at hlim
  exact squeeze_zero hV (geometric_bound hq hstep) hlim

/-- An additive error budget preserves a prescribed certificate sublevel set. -/
theorem invariant_bound {V : ℕ → ℝ} {q d R : ℝ}
    (hq : 0 ≤ q) (hbudget : q * R + d ≤ R) (hinit : V 0 ≤ R)
    (hstep : ∀ n, V (n + 1) ≤ q * V n + d) : ∀ n, V n ≤ R := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
    calc
      V (n + 1) ≤ q * V n + d := hstep n
      _ ≤ q * R + d := add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
      _ ≤ R := hbudget

/-- Finite-time disturbance bound, expressed without division. -/
theorem affine_bound {V : ℕ → ℝ} {q d : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, V (n + 1) ≤ q * V n + d) (n : ℕ) :
    V n ≤ q ^ n * V 0 + d * ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      V (n + 1) ≤ q * V n + d := hstep n
      _ ≤ q * (q ^ n * V 0 + d * ∑ i ∈ Finset.range n, q ^ i) + d := by
        exact add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
      _ = q ^ (n + 1) * V 0 + d * ∑ i ∈ Finset.range (n + 1), q ^ i := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, pow_succ', ← Finset.mul_sum]
        ring

/-- Robust scalar interval invariance, allowing time-varying coefficients and errors. -/
theorem scalar_robust_invariant (a w x : ℕ → ℝ) {q d R : ℝ}
    (hq : 0 ≤ q) (ha : ∀ n, |a n| ≤ q) (hw : ∀ n, |w n| ≤ d)
    (hbudget : q * R + d ≤ R) (hinit : |x 0| ≤ R)
    (hdynamics : ∀ n, x (n + 1) = a n * x n + w n) :
    ∀ n, |x n| ≤ R := by
  apply invariant_bound hq hbudget hinit
  intro n
  rw [hdynamics n]
  calc
    |a n * x n + w n| ≤ |a n * x n| + |w n| := abs_add_le _ _
    _ = |a n| * |x n| + |w n| := by rw [abs_mul]
    _ ≤ q * |x n| + d := add_le_add
      (mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _)) (hw n)

end LeanControls
