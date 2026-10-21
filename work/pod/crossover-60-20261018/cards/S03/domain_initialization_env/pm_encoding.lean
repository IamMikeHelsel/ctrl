import Mathlib.Tactic
namespace S03Encoding

theorem decimal_dot_exact (X V : ℤ) :
    ((-2*X-3*V : ℤ) : ℝ)/10000 = -2*((X:ℝ)/10000)-3*((V:ℝ)/10000) := by
  push_cast
  ring

theorem decimal_sensor_error (X V : ℤ) (x v : ℝ)
    (hx : |(X:ℝ)/10000-x|≤1/20000)
    (hv : |(V:ℝ)/10000-v|≤1/20000) :
    |((-2*X-3*V : ℤ):ℝ)/10000-(-2*x-3*v)|≤1/4000 := by
  rw [decimal_dot_exact]
  have hid : -2*((X:ℝ)/10000)-3*((V:ℝ)/10000)-(-2*x-3*v) =
      -2*((X:ℝ)/10000-x)+ -3*((V:ℝ)/10000-v) := by ring
  rw [hid]
  calc
    _ ≤ |-2*((X:ℝ)/10000-x)|+|-3*((V:ℝ)/10000-v)| := abs_add_le _ _
    _ ≤ 1/4000 := by rw [abs_mul,abs_mul]; norm_num; linarith

-- This binds the C integer quadratic to the scaled real energy at a cell corner.
theorem corner_scale (X V sx sv : ℤ) :
    5*(((2*X+sx:ℤ):ℝ)/20000)^2 +
      2*(((2*X+sx:ℤ):ℝ)/20000)*(((2*V+sv:ℤ):ℝ)/20000) +
      (((2*V+sv:ℤ):ℝ)/20000)^2 =
      ((5*(2*X+sx)^2+2*(2*X+sx)*(2*V+sv)+(2*V+sv)^2:ℤ):ℝ)/400000000 := by
  push_cast
  ring

theorem corner_bound (X V sx sv : ℤ)
    (hq : 5*(2*X+sx)^2+2*(2*X+sx)*(2*V+sv)+(2*V+sv)^2≤40000000) :
    5*(((2*X+sx:ℤ):ℝ)/20000)^2 +
      2*(((2*X+sx:ℤ):ℝ)/20000)*(((2*V+sv:ℤ):ℝ)/20000) +
      (((2*V+sv:ℤ):ℝ)/20000)^2 ≤ 1/10 := by
  rw [corner_scale]
  have h : ((5*(2*X+sx)^2+2*(2*X+sx)*(2*V+sv)+(2*V+sv)^2:ℤ):ℝ)≤40000000 := by exact_mod_cast hq
  linarith

#print axioms decimal_dot_exact
#print axioms decimal_sensor_error
#print axioms corner_scale
#print axioms corner_bound
end S03Encoding
