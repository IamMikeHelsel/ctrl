import Composition
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set
noncomputable section
namespace RobotMotion.TaskContract

lemma F1_piece0 {z : ℝ} (hl : 0 ≤ z) (hr : z ≤ 1) : F1 z = z^3/6 := by
  have h1 : z-1 ≤ 0 := by linarith
  have h2 : z-2 ≤ 0 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp [F1,P,max_eq_left hl,max_eq_right h1,max_eq_right h2,max_eq_right h3,max_eq_right h4]

lemma F1_piece1 {z : ℝ} (hl : 1 ≤ z) (hr : z ≤ 2) :
    F1 z = (1+3*(z-1)+3*(z-1)^2*(2-z))/6 := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : z-2 ≤ 0 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F1,P,max_eq_left h0,max_eq_left h1,max_eq_right h2,max_eq_right h3,max_eq_right h4]
  ring

lemma F1_piece2 {z : ℝ} (hl : 2 ≤ z) (hr : z ≤ 3) :
    F1 z = (1+3*(3-z)+3*(3-z)^2*(z-2))/6 := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : 0 ≤ z-2 := by linarith
  have h3 : z-3 ≤ 0 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F1,P,max_eq_left h0,max_eq_left h1,max_eq_left h2,max_eq_right h3,max_eq_right h4]
  ring

lemma F1_piece3 {z : ℝ} (hl : 3 ≤ z) (hr : z ≤ 4) : F1 z = (4-z)^3/6 := by
  have h0 : 0 ≤ z := by linarith
  have h1 : 0 ≤ z-1 := by linarith
  have h2 : 0 ≤ z-2 := by linarith
  have h3 : 0 ≤ z-3 := by linarith
  have h4 : z-4 ≤ 0 := by linarith
  simp only [F1,P,max_eq_left h0,max_eq_left h1,max_eq_left h2,max_eq_left h3,max_eq_right h4]
  ring

theorem F1_nonnegative (z : ℝ) : 0 ≤ F1 z := by
  by_cases h0 : z ≤ 0
  · rw [(left_tail h0).2.1]
  have hz : 0 ≤ z := le_of_lt (lt_of_not_ge h0)
  by_cases h1 : z ≤ 1
  · rw [F1_piece0 hz h1]; positivity
  have hz1 : 1 ≤ z := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : z ≤ 2
  · have ha : 0 ≤ z-1 := by linarith
    have hb : 0 ≤ 2-z := by linarith
    rw [F1_piece1 hz1 h2]; positivity
  have hz2 : 2 ≤ z := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : z ≤ 3
  · have ha : 0 ≤ 3-z := by linarith
    have hb : 0 ≤ z-2 := by linarith
    rw [F1_piece2 hz2 h3]; positivity
  have hz3 : 3 ≤ z := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : z ≤ 4
  · have ha : 0 ≤ 4-z := by linarith
    rw [F1_piece3 hz3 h4]; positivity
  · rw [(right_tail (le_of_lt (lt_of_not_ge h4))).2.1]

theorem F0_monotone : Monotone F0 :=
  monotone_of_hasDerivAt_nonneg F0_deriv F1_nonnegative

@[simp] theorem F0_zero : F0 0 = 0 := (left_tail (by norm_num)).1
@[simp] theorem F0_four : F0 4 = 1 := (right_tail (by norm_num)).1
@[simp] theorem F0_two : F0 2 = 1/2 := by norm_num [F0,P]

theorem F0_range (z : ℝ) : 0 ≤ F0 z ∧ F0 z ≤ 1 := by
  constructor
  · by_cases hz : z ≤ 0
    · rw [(left_tail hz).1]
    · simpa using F0_monotone (le_of_lt (lt_of_not_ge hz))
  · by_cases hz : 4 ≤ z
    · rw [(right_tail hz).1]
    · simpa using F0_monotone (le_of_lt (lt_of_not_ge hz))

theorem F3_bound (z : ℝ) : |F3 z| ≤ 2 := by
  by_cases h0 : z ≤ 0
  · rw [K_left h0]; norm_num
  have hz : 0 ≤ z := le_of_lt (lt_of_not_ge h0)
  by_cases h1 : z ≤ 1
  · rw [K_piece0 hz h1,abs_le]; constructor <;> linarith
  have hz1 : 1 ≤ z := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : z ≤ 2
  · rw [K_piece1 hz1 h2,abs_le]; constructor <;> linarith
  have hz2 : 2 ≤ z := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : z ≤ 3
  · rw [K_piece2 hz2 h3,abs_le]; constructor <;> linarith
  have hz3 : 3 ≤ z := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : z ≤ 4
  · rw [K_piece3 hz3 h4,abs_le]; constructor <;> linarith
  · rw [K_right (le_of_lt (lt_of_not_ge h4))]; norm_num

end RobotMotion.TaskContract
