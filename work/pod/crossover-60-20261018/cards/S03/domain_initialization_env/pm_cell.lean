import Mathlib.Tactic
namespace S03Cell
-- The source energy quadratic, without changing the source declaration.
def E (x v : ℝ) := 5*x*x+2*x*v+v*v

theorem quadratic_interval (a b c L U x B : ℝ) (ha : 0≤a)
    (hxL : L≤x) (hxU : x≤U)
    (hL : a*L*L+b*L+c≤B) (hU : a*U*U+b*U+c≤B) :
    a*x*x+b*x+c≤B := by
  by_cases h : L=U
  · have hxl : x=L := by linarith
    simpa [hxl] using hL
  have hpos : 0<U-L := by have : L<U := lt_of_le_of_ne (hxL.trans hxU) h; linarith
  have hp : 0 ≤ (U-L)*(B-(a*x*x+b*x+c)) := by
    calc
      0 ≤ (U-x)*(B-(a*L*L+b*L+c)) + (x-L)*(B-(a*U*U+b*U+c)) +
          a*(U-L)*(x-L)*(U-x) := by positivity
      _ = _ := by ring
  have := nonneg_of_mul_nonneg_right hp hpos
  linarith

theorem cell_bound (Lx Ux Lv Uv x v B : ℝ)
    (hx : Lx≤x ∧ x≤Ux) (hv : Lv≤v ∧ v≤Uv)
    (h00 : E Lx Lv≤B) (h01 : E Lx Uv≤B)
    (h10 : E Ux Lv≤B) (h11 : E Ux Uv≤B) : E x v≤B := by
  have lower : E Lx v≤B := by
    simpa [E, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using quadratic_interval 1 (2*Lx) (5*Lx*Lx) Lv Uv v B (by norm_num) hv.1 hv.2
        (by dsimp [E] at h00; nlinarith) (by dsimp [E] at h01; nlinarith)
  have upper : E Ux v≤B := by
    simpa [E, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using quadratic_interval 1 (2*Ux) (5*Ux*Ux) Lv Uv v B (by norm_num) hv.1 hv.2
        (by dsimp [E] at h10; nlinarith) (by dsimp [E] at h11; nlinarith)
  simpa [E, mul_comm, mul_left_comm, mul_assoc] using
    quadratic_interval 5 (2*v) (v*v) Lx Ux x B (by norm_num) hx.1 hx.2
      (by dsimp [E] at lower; nlinarith) (by dsimp [E] at upper; nlinarith)

#print axioms quadratic_interval
#print axioms cell_bound
end S03Cell
