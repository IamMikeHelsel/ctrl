import Mathlib.Tactic

namespace V06Inventor

/-- Half the Frobenius squared residual for each SO(2) edge, multiplied by two.
Gauge R0=I; all measurements -I; each directed edge appears once. -/
def cost (w01 w12 w02 x y u v : ℝ) : ℝ :=
  2*(w01*((x+1)^2+y^2)+w12*((x+u)^2+(y+v)^2)+w02*((u+1)^2+v^2))

theorem rational_certificate (x y u v : ℝ)
    (h1 : x^2+y^2=1) (h2 : u^2+v^2=1) :
    cost 15 12 20 x y u v=88+2*((5+3*x+4*u)^2+(3*y+4*v)^2) := by
  dsimp [cost]
  nlinarith

theorem rational_global (x y u v : ℝ)
    (h1 : x^2+y^2=1) (h2 : u^2+v^2=1) : 88 ≤ cost 15 12 20 x y u v := by
  rw [rational_certificate _ _ _ _ h1 h2]
  nlinarith [sq_nonneg (5+3*x+4*u), sq_nonneg (3*y+4*v)]

theorem rational_candidate :
    (-3/5 : ℝ)^2+(4/5)^2=1 ∧ (-4/5 : ℝ)^2+(-3/5)^2=1 ∧
    cost 15 12 20 (-3/5) (4/5) (-4/5) (-3/5)=88 := by norm_num [cost]

theorem weight_mutation :
    cost 15 13 20 (-3/5) (4/5) (-4/5) (-3/5)=92 ∧
    cost 15 13 20 (-29197/50005) (40596/50005) (-4/5) (-3/5)<92 := by
  norm_num [cost]

theorem mutated_candidate_feasible :
    (-29197/50005 : ℝ)^2+(40596/50005)^2=1 := by norm_num

theorem phase_certificate (x y u v : ℝ)
    (h1 : x^2+y^2=1) (h2 : u^2+v^2=1) :
    cost 24 12 32 x y u v=96+2*((8/7)*((7+3*x+4*u)^2+(3*y+4*v)^2)+
      (12/7)*((x-u)^2+(y-v)^2)) := by
  dsimp [cost]
  nlinarith

theorem phase_global (x y u v : ℝ)
    (h1 : x^2+y^2=1) (h2 : u^2+v^2=1) : 96 ≤ cost 24 12 32 x y u v := by
  rw [phase_certificate _ _ _ _ h1 h2]
  nlinarith [sq_nonneg (7+3*x+4*u), sq_nonneg (3*y+4*v),
    sq_nonneg (x-u), sq_nonneg (y-v)]

theorem phase_candidate : cost 24 12 32 (-1) 0 (-1) 0=96 := by norm_num [cost]

theorem phase_unique (x y u v : ℝ)
    (h1 : x^2+y^2=1) (h2 : u^2+v^2=1)
    (hmin : cost 24 12 32 x y u v=96) : x = -1 ∧ y = 0 ∧ u = -1 ∧ v = 0 := by
  rw [phase_certificate _ _ _ _ h1 h2] at hmin
  have hn1 := sq_nonneg (7+3*x+4*u)
  have hn2 := sq_nonneg (3*y+4*v)
  have hn3 := sq_nonneg (x-u)
  have hn4 := sq_nonneg (y-v)
  have hx : x=u := by nlinarith
  have hy : y=v := by nlinarith
  have hz : 7+3*x+4*u=0 := by nlinarith
  have hw : 3*y+4*v=0 := by nlinarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms rational_certificate
#print axioms rational_global
#print axioms rational_candidate
#print axioms weight_mutation
#print axioms mutated_candidate_feasible
#print axioms phase_certificate
#print axioms phase_global
#print axioms phase_candidate
#print axioms phase_unique
end V06Inventor
