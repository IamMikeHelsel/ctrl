import Mathlib
set_option maxHeartbeats 3000000
namespace E10
abbrev IV := ℚ × ℚ
def Mem (x : ℚ) (a : IV) : Prop := a.1 ≤ x ∧ x ≤ a.2
def k (x : ℚ) : IV := (x,x)
def add (a b : IV) : IV := (a.1+b.1,a.2+b.2)
def neg (a : IV) : IV := (-a.2,-a.1)
def sub (a b : IV) : IV := add a (neg b)
def mul (a b : IV) : IV :=
 (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
 max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))
def inv (a : IV) : IV := (1/a.2,1/a.1)
def sq (a : IV) : IV :=
 (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1*a.1) (a.2*a.2),
 max (a.1*a.1) (a.2*a.2))
theorem k_sound (x : ℚ) : Mem x (k x) := ⟨le_rfl,le_rfl⟩
theorem add_sound {a b : IV} {x y : ℚ} (hx : Mem x a) (hy : Mem y b) :
 Mem (x+y) (add a b) := ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩
theorem neg_sound {a : IV} {x : ℚ} (hx : Mem x a) : Mem (-x) (neg a) :=
 ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
theorem sub_sound {a b : IV} {x y : ℚ} (hx : Mem x a) (hy : Mem y b) :
 Mem (x-y) (sub a b) := by simpa [sub, sub_eq_add_neg] using add_sound hx (neg_sound hy)
theorem mul_sound {a b : IV} {x y : ℚ} (hx : Mem x a) (hy : Mem y b) :
 Mem (x*y) (mul a b) := by
 have aux (l u z t : ℚ) (hl : l ≤ t) (hu : t ≤ u) :
   min (l*z) (u*z) ≤ t*z ∧ t*z ≤ max (l*z) (u*z) := by
  by_cases hz : 0 ≤ z
  · constructor
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hz)
    · exact (mul_le_mul_of_nonneg_right hu hz).trans (le_max_right _ _)
  · constructor
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge hz))
    · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hz)).trans (le_max_left _ _)
 have h1 := aux b.1 b.2 a.1 y hy.1 hy.2
 have h2 := aux b.1 b.2 a.2 y hy.1 hy.2
 have h3 := aux a.1 a.2 y x hx.1 hx.2
 simp only [mul_comm b.1, mul_comm b.2] at h1 h2
 rw [mul_comm y a.1] at h1
 rw [mul_comm y a.2] at h2
 constructor
 · exact (min_le_min h1.1 h2.1).trans h3.1
 · exact h3.2.trans (max_le_max h1.2 h2.2)
theorem inv_sound {a : IV} {x : ℚ} (hx : Mem x a) (ha : 0 < a.1) :
 Mem (1/x) (inv a) :=
 ⟨one_div_le_one_div_of_le (ha.trans_le hx.1) hx.2,one_div_le_one_div_of_le ha hx.1⟩
theorem sq_sound {a : IV} {x : ℚ} (hx : Mem x a) : Mem (x^2) (sq a) := by
 rcases hx with ⟨hl,hu⟩
 constructor
 · change (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1*a.1) (a.2*a.2)) ≤ x^2
   split_ifs with h
   · exact sq_nonneg x
   · by_cases ha : 0 ≤ a.1
     · have hh : a.1*a.1 ≤ x^2 := by nlinarith
       exact (min_le_left _ _).trans hh
     · have hb : a.2 < 0 := by simp only [not_and_or, not_le] at h; rcases h with h|h <;> linarith
       have hh : a.2*a.2 ≤ x^2 := by nlinarith
       exact (min_le_right _ _).trans hh
 · change x^2 ≤ max (a.1*a.1) (a.2*a.2)
   by_cases hx : 0 ≤ x
   · exact (show x^2 ≤ a.2*a.2 by nlinarith).trans (le_max_right _ _)
   · exact (show x^2 ≤ a.1*a.1 by nlinarith).trans (le_max_left _ _)

inductive Expr where
 | c | j | lit (q : ℚ) | plus (a b : Expr) | minus (a : Expr)
 | times (a b : Expr) | square (a : Expr) | recip (a : Expr)
 deriving Repr
namespace Expr
def val (c j : ℚ) : Expr → ℚ
 | .c => c | .j => j | .lit q => q | .plus a b => val c j a + val c j b
 | .minus a => -val c j a | .times a b => val c j a * val c j b
 | .square a => (val c j a)^2 | .recip a => 1/val c j a
def box (c j : IV) : Expr → IV
 | .c => c | .j => j | .lit q => k q | .plus a b => add (box c j a) (box c j b)
 | .minus a => neg (box c j a) | .times a b => mul (box c j a) (box c j b)
 | .square a => sq (box c j a) | .recip a => inv (box c j a)
def safe (c j : IV) : Expr → Bool
 | .c | .j | .lit _ => true
 | .plus a b | .times a b => safe c j a && safe c j b
 | .minus a | .square a => safe c j a
 | .recip a => safe c j a && decide (0 < (box c j a).1)
theorem sound (e : Expr) {c j : ℚ} {cb jb : IV} (hc : Mem c cb) (hj : Mem j jb)
 (hs : safe cb jb e = true) : Mem (val c j e) (box cb jb e) := by
 induction e with
 | c => exact hc
 | j => exact hj
 | lit q => exact k_sound q
 | plus a b ia ib => exact add_sound (ia (Bool.and_eq_true_iff.mp hs).1) (ib (Bool.and_eq_true_iff.mp hs).2)
 | minus a ia => exact neg_sound (ia hs)
 | times a b ia ib => exact mul_sound (ia (Bool.and_eq_true_iff.mp hs).1) (ib (Bool.and_eq_true_iff.mp hs).2)
 | square a ia => exact sq_sound (ia hs)
 | recip a ia => exact inv_sound (ia (Bool.and_eq_true_iff.mp hs).1) (of_decide_eq_true (Bool.and_eq_true_iff.mp hs).2)
end Expr
end E10
