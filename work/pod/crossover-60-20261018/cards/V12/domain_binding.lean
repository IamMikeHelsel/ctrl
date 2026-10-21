import Mathlib.Tactic
namespace V12Binding

/-- The coefficient row represents the actual symmetric bilinear form. -/
theorem coefficient_binding (b11 b12 b22 b13 b23 b33 x y z u v w : ℝ) :
    (x*u)*b11+(x*v+y*u)*b12+(y*v)*b22+(z*u+x*w)*b13+
      (z*v+y*w)*b23+(z*w)*b33 =
    x*(b11*u+b12*v+b13*w)+y*(b12*u+b22*v+b23*w)+
      z*(b13*u+b23*v+b33*w) := by ring

/-- Homography scaling multiplies each constraint row by the same squared scale. -/
theorem gauge_row (s x y z u v w : ℝ) :
    (s*x)*(s*u)=s^2*(x*u) ∧
    (s*x)*(s*v)+(s*y)*(s*u)=s^2*(x*v+y*u) ∧
    (s*z)*(s*w)=s^2*(z*w) := by constructor <;> [ring; skip]; constructor <;> ring

noncomputable def q (x y z : ℝ) : ℝ :=
    x^2-(1/3)*x*y+(17/36)*y^2-(7/3)*x*z+(23/18)*y*z+(209/36)*z^2

theorem spd_squares (x y z : ℝ) :
    q x y z = (x-y/6-7*z/6)^2+((2/3)*y+(2/3)*z)^2+(2*z)^2 := by unfold q; ring

theorem concrete_spd (x y z : ℝ) (hn : x≠0 ∨ y≠0 ∨ z≠0) : 0<q x y z := by
  rw [spd_squares]
  by_contra h
  have hs0 := sq_nonneg (x-y/6-7*z/6)
  have hs1 := sq_nonneg ((2/3:ℝ)*y+(2/3)*z)
  have hs2 := sq_nonneg (2*z)
  have hz : z=0 := by nlinarith
  subst z
  have hy : y=0 := by nlinarith
  subst y
  have hx : x=0 := by nlinarith
  exact hn.elim (fun h => h hx) (fun h => h.elim (fun h => h rfl) (fun h => h rfl))

#print axioms coefficient_binding
#print axioms gauge_row
#print axioms spd_squares
#print axioms concrete_spd
end V12Binding
