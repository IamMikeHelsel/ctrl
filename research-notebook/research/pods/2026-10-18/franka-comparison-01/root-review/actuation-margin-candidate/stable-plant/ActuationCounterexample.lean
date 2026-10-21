module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace ActuationCounterexample

def field (x u : ℝ) : ℝ := -x+u
def barrierExpression (x u : ℝ) : ℝ := field x u+x
def allowed (x u : ℝ) : Prop := |u|≤9/10 ∧ 0≤barrierExpression x u
def trajectory (t : ℝ) : ℝ := (10001/100000)*Real.exp (-t)-1/10

theorem global_cbf (x : ℝ) : ∃ u : ℝ, |u|≤1 ∧ 0≤barrierExpression x u := by
  refine ⟨1,?_,?_⟩ <;> simp [barrierExpression,field]

theorem exact_zero_variation (x y u : ℝ) :
    barrierExpression x u-barrierExpression y u=0 := by
  dsimp [barrierExpression,field]; ring

theorem nominal_feasible (x : ℝ) : allowed x 0 := by
  constructor
  · norm_num
  · simp [barrierExpression,field]

theorem admissible_real_input : |(-1/10:ℝ)|≤1 ∧ |(-1/10:ℝ)-0|≤1/10 := by
  norm_num

theorem initial_robust_safe : trajectory 0=1/100000 ∧
    ∀ x : ℝ, |x-trajectory 0|≤1/1000000 → 0≤x := by
  have hi : trajectory 0=(1/100000:ℝ) := by norm_num [trajectory]
  refine ⟨hi,?_⟩
  intro x hx
  rw [hi] at hx
  have h := (abs_le.mp hx).1
  linarith

theorem exact_measurement (t : ℝ) : |trajectory t-trajectory t|≤1/1000000 := by
  simp

theorem physical_solution (t : ℝ) :
    HasDerivAt trajectory (field (trajectory t) (-1/10)) t := by
  have hd := (((hasDerivAt_id t).neg.exp).const_mul (10001/100000:ℝ)).sub_const (1/10)
  convert hd using 1
  · funext x
    dsimp [trajectory]
  · dsimp [trajectory,field]
    ring

theorem exponential_upper (t : ℝ) : (1+t)*Real.exp (-t)≤1 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  have he : Real.exp t*Real.exp (-t)=1 := by
    rw [← Real.exp_add]; simp
  rw [he] at h
  linarith

theorem fails_before_first_sample :
    (0:ℝ)<1/2000 ∧ (1/2000:ℝ)<1/1000 ∧ trajectory (1/2000)<0 := by
  refine ⟨by norm_num,by norm_num,?_⟩
  have h := exponential_upper (1/2000)
  dsimp [trajectory]
  nlinarith

theorem all_sample_inputs_feasible (k : ℕ) : allowed (trajectory ((k:ℝ)/1000)) 0 :=
  nominal_feasible _

theorem missing_actuation_margin (x : ℝ) :
    allowed x 0 ∧ |(-1/10:ℝ)-0|≤1/10 ∧ barrierExpression x (-1/10)<0 := by
  refine ⟨nominal_feasible x,by norm_num,?_⟩
  dsimp [barrierExpression,field]; linarith

theorem repaired_condition (x u : ℝ) (hu : 1/10≤barrierExpression x u)
    (err : ℝ) (he : |err|≤1/10) : 0≤barrierExpression x (u+err) := by
  have h := (abs_le.mp he).1
  dsimp [barrierExpression,field] at *
  linarith

end ActuationCounterexample
