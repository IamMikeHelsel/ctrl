import Primitive

open Set
noncomputable section
namespace RobotMotion

/-- Truncated-power numerator of the known four-box step filter. -/
def P (n : ℕ) (z : ℝ) : ℝ :=
  (max z 0)^n - 4*(max (z-1) 0)^n + 6*(max (z-2) 0)^n -
    4*(max (z-3) 0)^n + (max (z-4) 0)^n

def F0 (z : ℝ) : ℝ := P 4 z / 24
def F1 (z : ℝ) : ℝ := P 3 z / 6
def F2 (z : ℝ) : ℝ := P 2 z / 2
def F3 (z : ℝ) : ℝ := P 1 z

lemma power_deriv (n : ℕ) (hn : 2 ≤ n) (a z : ℝ) :
    HasDerivAt (fun y : ℝ => (max (y-a) 0)^n)
      ((n:ℝ)*(max (z-a) 0)^(n-1)) z := by
  convert (RobotMotionPreflight.positive_part_pow_derivative n hn (z-a)).comp z
    ((hasDerivAt_id z).sub_const a) using 1 <;> simp <;> rfl

lemma P_deriv (n : ℕ) (hn : 2 ≤ n) (z : ℝ) :
    HasDerivAt (P n) ((n:ℝ)*P (n-1) z) z := by
  have h0 := power_deriv n hn 0 z
  have h1 := (power_deriv n hn 1 z).const_mul 4
  have h2 := (power_deriv n hn 2 z).const_mul 6
  have h3 := (power_deriv n hn 3 z).const_mul 4
  have h4 := power_deriv n hn 4 z
  convert (((h0.sub h1).add h2).sub h3).add h4 using 1
  · funext y; simp only [P, Pi.add_apply, Pi.sub_apply, sub_zero]
  · dsimp [P] <;> ring

/-- Derivatives hold at every real point, including all five knots. -/
theorem F0_deriv (z : ℝ) : HasDerivAt F0 (F1 z) z := by
  convert (P_deriv 4 (by omega) z).div_const 24 using 1
  · funext y; dsimp [F0] <;> ring
  · dsimp [F1] <;> ring

theorem F1_deriv (z : ℝ) : HasDerivAt F1 (F2 z) z := by
  convert (P_deriv 3 (by omega) z).div_const 6 using 1
  · funext y; dsimp [F1] <;> ring
  · dsimp [F2] <;> ring

theorem F2_deriv (z : ℝ) : HasDerivAt F2 (F3 z) z := by
  convert (P_deriv 2 (by omega) z).div_const 2 using 1
  · funext y; dsimp [F2] <;> ring
  · dsimp [F3] <;> ring

lemma P_continuous (n : ℕ) : Continuous (P n) := by unfold P; fun_prop
theorem F0_continuous : Continuous F0 := (P_continuous 4).div_const 24
theorem F1_continuous : Continuous F1 := (P_continuous 3).div_const 6
theorem F2_continuous : Continuous F2 := (P_continuous 2).div_const 2
theorem F3_continuous : Continuous F3 := P_continuous 1

theorem left_tail {z : ℝ} (hz : z ≤ 0) :
    F0 z = 0 ∧ F1 z = 0 ∧ F2 z = 0 ∧ F3 z = 0 := by
  have h1 : z-1 ≤ 0 := by linarith
  have h2 : z-2 ≤ 0 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp [F0,F1,F2,F3,P,max_eq_right hz,max_eq_right h1,max_eq_right h2,
    max_eq_right h3,max_eq_right h4]

theorem right_tail {z : ℝ} (hz : 4 ≤ z) :
    F0 z = 1 ∧ F1 z = 0 ∧ F2 z = 0 ∧ F3 z = 0 := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : 0 ≤ z-2 := by linarith
  have h3 : 0 ≤ z-3 := by linarith
  have h4 : 0 ≤ z-4 := by linarith
  simp only [F0,F1,F2,F3,P,max_eq_left h0,max_eq_left h1,max_eq_left h2,
    max_eq_left h3,max_eq_left h4]
  constructor; · ring
  constructor; · ring
  constructor <;> ring

theorem K_left {z : ℝ} (hz : z ≤ 0) : F3 z = 0 := (left_tail hz).2.2.2
theorem K_right {z : ℝ} (hz : 4 ≤ z) : F3 z = 0 := (right_tail hz).2.2.2

theorem K_piece0 {z : ℝ} (hl : 0 ≤ z) (hr : z ≤ 1) : F3 z = z := by
  have h0 : 0 ≤ z := by linarith
  have h1 : z-1 ≤ 0 := by linarith
  have h2 : z-2 ≤ 0 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F3,P,pow_one,max_eq_left h0,max_eq_right h1,max_eq_right h2,max_eq_right h3,max_eq_right h4]
  ring

theorem K_piece1 {z : ℝ} (hl : 1 ≤ z) (hr : z ≤ 2) : F3 z = 4-3*z := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : z-2 ≤ 0 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F3,P,pow_one,max_eq_left h0,max_eq_left h1,max_eq_right h2,max_eq_right h3,max_eq_right h4]
  ring

theorem K_piece2 {z : ℝ} (hl : 2 ≤ z) (hr : z ≤ 3) : F3 z = 3*z-8 := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : 0 ≤ z-2 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F3,P,pow_one,max_eq_left h0,max_eq_left h1,max_eq_left h2,max_eq_right h3,max_eq_right h4]
  ring

theorem K_piece3 {z : ℝ} (hl : 3 ≤ z) (hr : z ≤ 4) : F3 z = 4-z := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : 0 ≤ z-2 := by linarith
  have h3 : 0 ≤ z-3 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F3,P,pow_one,max_eq_left h0,max_eq_left h1,max_eq_left h2,max_eq_left h3,max_eq_right h4]
  ring

end RobotMotion
