import Mathlib.Tactic
namespace R02Guard
-- Exact interval guard for an abstract branch input; obtaining epsilon from IEEE code is separate.
theorem safe_left (t rounded cut e : ℝ) (herr : |rounded-t|≤e) (hmargin : t+e<cut) : rounded<cut := by
 rw [abs_le] at herr; linarith

theorem safe_right (t rounded cut e : ℝ) (herr : |rounded-t|≤e) (hmargin : cut≤t-e) : cut≤rounded := by
 rw [abs_le] at herr; linarith

theorem boundary_switch (cut e jleft jright : ℝ) (he : 0<e) :
 (if cut-e/2<cut then jleft else jright)=jleft ∧
 (if cut<cut then jleft else jright)=jright ∧ |cut-(cut-e/2)|≤e := by
 constructor
 · rw [if_pos (by linarith)]
 constructor
 · simp
 · rw [abs_of_nonneg (by linarith)]; linarith

theorem cancellation (a : ℝ) : |a+(-a)|=0 ∧ |a|+|-a|=2*|a| := by
 constructor <;> simp [abs_neg, two_mul]

theorem one_sided_budget (dq dv da dj : ℝ) :
 |800*dq+60*dv+(3/2)*da+dj/96|≤800*|dq|+60*|dv|+(3/2)*|da|+|dj|/96 := by
 calc
  |800*dq+60*dv+(3/2)*da+dj/96|≤|800*dq+60*dv+(3/2)*da|+|dj/96| := abs_add_le _ _
  _≤(|800*dq+60*dv|+|(3/2)*da|)+|dj/96| := by gcongr; exact abs_add_le _ _
  _≤((|800*dq|+|60*dv|)+|(3/2)*da|)+|dj/96| := by gcongr; exact abs_add_le _ _
  _=800*|dq|+60*|dv|+(3/2)*|da|+|dj|/96 := by simp only [abs_mul,abs_div]; norm_num
end R02Guard
#print axioms R02Guard.safe_left
#print axioms R02Guard.safe_right
#print axioms R02Guard.boundary_switch
#print axioms R02Guard.cancellation
#print axioms R02Guard.one_sided_budget
