import Mathlib.Tactic
namespace V01Guard

theorem height_bounds {u : ℝ} (hu : |u|≤1/2) :
    2/5≤4/5-4/5*u ∧ 4/5-4/5*u≤6/5 := by
  have := abs_le.mp hu
  constructor <;> linarith

theorem horizontal_patch {u : ℝ} (hu : |u|≤1/2) :
    1/2≤((3/5)*u+9/10)/(4/5-4/5*u) ∧
    ((3/5)*u+9/10)/(4/5-4/5*u)≤3 := by
  have hh := height_bounds hu
  have hp : 0<4/5-4/5*u := by linarith
  have hb := abs_le.mp hu
  constructor
  · apply (le_div_iff₀ hp).mpr; linarith
  · apply (div_le_iff₀ hp).mpr; linarith

theorem vertical_patch {u v : ℝ} (hu : |u|≤1/2) (hv : |v|≤1/4) :
    -1/2≤(v+1/20)/(4/5-4/5*u) ∧
    (v+1/20)/(4/5-4/5*u)≤3/4 := by
  have hh := height_bounds hu
  have hp : 0<4/5-4/5*u := by linarith
  have hb := abs_le.mp hv
  constructor
  · apply (le_div_iff₀ hp).mpr; linarith
  · apply (div_le_iff₀ hp).mpr; linarith

theorem residual_scale {u : ℝ} (hu : 4/5-4/5*u≠0) :
    (2/3)*(((3/5)*u+9/10)/(4/5-4/5*u))-3/4 = u/(4/5-4/5*u) := by
  field_simp
  <;> ring

theorem transport_gate {r q tau : ℝ} (hq : 0<q) :
    |r/q|≤tau/q ↔ |r|≤tau := by
  rw [abs_div,abs_of_pos hq]
  exact div_le_div_iff_of_pos_right hq

theorem guarded_perturbation {u v e0 e1 e2 : ℝ}
    (hu : |u|≤1/2) (hv : |v|≤1/4)
    (h0 : |e0|≤1/1000) (h1 : |e1|≤1/1000) (h2 : |e2|≤1/1000) :
    1593/4000≤(-4/5+e0)*u+e1*v+4/5+e2 := by
  have p0 : |e0*u|≤1/2000 := by
    rw [abs_mul]
    have := mul_le_mul h0 hu (abs_nonneg u) (by norm_num : (0:ℝ)≤1/1000)
    norm_num at this
    exact this
  have p1 : |e1*v|≤1/4000 := by
    rw [abs_mul]
    have := mul_le_mul h1 hv (abs_nonneg v) (by norm_num : (0:ℝ)≤1/1000)
    norm_num at this
    exact this
  have hh := height_bounds hu
  have a := (abs_le.mp p0).1
  have b := (abs_le.mp p1).1
  have c := (abs_le.mp h2).1
  nlinarith only [hh.1,a,b,c]

#print axioms height_bounds
#print axioms horizontal_patch
#print axioms vertical_patch
#print axioms residual_scale
#print axioms transport_gate
#print axioms guarded_perturbation
end V01Guard
