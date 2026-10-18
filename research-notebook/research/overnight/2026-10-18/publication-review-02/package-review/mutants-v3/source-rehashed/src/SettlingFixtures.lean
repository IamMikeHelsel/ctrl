module
public import Settling
@[expose] public section
noncomputable section
namespace LeanControls.SettlingFixtures
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking Settling

theorem exp_neg_four_le : Real.exp (-4:ℝ) ≤ 1/16 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 4
  have h4 : (16:ℝ) ≤ Real.exp 4 := by
    have heq : Real.exp (4:ℝ) = Real.exp 1 ^ 4 := by
      simpa using Real.exp_nat_mul (1:ℝ) 4
    rw [heq]
    norm_num at hpow ⊢
    exact hpow
  rw [Real.exp_neg]
  simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16) h4

/-- After one physical second, the inherited 0.2 mm cube reaches these
conservative bounds with the stated nonzero disturbance allowance. -/
theorem one_second_envelope {t : ℝ} (ht : 1 ≤ t) :
    3*(1/100:ℝ)/(8*10^2)+(5*(1/5000:ℝ)/4)*Real.exp (-(2/5)*(10*t)) ≤ 17/320000 := by
  have he : Real.exp (-(2/5)*(10*t)) ≤ 1/16 :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_neg_four_le
  nlinarith

theorem one_second_physical_constants :
    8*(10:ℝ)*(17/320000) = 17/4000 ∧
    64*(10:ℝ)^2*(17/320000) = 17/50 ∧
    24*(10:ℝ)^2*(17/320000) = 51/400 := by norm_num

/-- Two physical seconds without disturbance reach 0.078125 mm/s and
0.00625 m/s² from this same inherited cube. -/
theorem two_seconds_zero_disturbance {t : ℝ} (ht : 2 ≤ t) :
    (5*(1/5000:ℝ)/4)*Real.exp (-(2/5)*(10*t)) ≤ 1/1024000 := by
  have h8 : Real.exp (-8:ℝ) ≤ 1/256 := by
    have hmul := mul_le_mul exp_neg_four_le exp_neg_four_le (Real.exp_pos (-4:ℝ)).le
      (by norm_num : (0:ℝ) ≤ 1/16)
    norm_num [←Real.exp_add] at hmul ⊢
    exact hmul
  have he : Real.exp (-(2/5)*(10*t)) ≤ 1/256 :=
    (Real.exp_le_exp.mpr (by linarith)).trans h8
  nlinarith

theorem two_seconds_physical_constants :
    8*(10:ℝ)*(1/1024000) = 1/12800 ∧
    64*(10:ℝ)^2*(1/1024000) = 1/160 ∧
    (1/12800:ℝ) < 1/1000 ∧ (1/160:ℝ) < 1/50 := by norm_num

/-- End-to-end one-second position, speed and acceleration bounds. -/
theorem one_second_actual {H c : ℝ} (hH : 0 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hi : ∀ i, |coordinates c (scaleState 10 (f 0)) i| ≤ 1/5000) :
    ∀ t ∈ Icc 1 H,
      |f t 0-c| ≤ 17/320000 ∧ |f t 1| ≤ 17/4000 ∧ |f t 2| ≤ 17/50 := by
  have hb := settling_physical_bounds (σ:=10) (W:=1/100) (R:=1/5000)
    (by norm_num) hH (by norm_num) (by norm_num) hf
    (by convert hrlo using 1; norm_num) (by convert hrhi using 1; norm_num) hw hi
  intro t ht
  have hh := hb t ⟨by linarith [ht.1],ht.2⟩
  have he := one_second_envelope ht.1
  dsimp at hh
  obtain ⟨hx,hv,ha,hu⟩ := hh
  constructor
  · exact hx.trans he
  · constructor <;> nlinarith

/-- Without disturbance, the same inherited state meets the tighter speed
and acceleration bands after two physical seconds. -/
theorem two_seconds_actual_zero_disturbance {H c : ℝ} (hH : 0 ≤ H)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+(0:ℝ)) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hi : ∀ i, |coordinates c (scaleState 10 (f 0)) i| ≤ 1/5000) :
    ∀ t ∈ Icc 2 H,
      |f t 0-c| ≤ 1/1024000 ∧ |f t 1| ≤ 1/12800 ∧ |f t 2| ≤ 1/160 := by
  have hb := settling_physical_bounds (σ:=10) (W:=0) (R:=1/5000)
    (by norm_num) hH (by norm_num) (by norm_num) hf
    (by convert hrlo using 1; norm_num) (by convert hrhi using 1; norm_num) (by intro t ht; norm_num) hi
  intro t ht
  have hh := hb t ⟨by linarith [ht.1],ht.2⟩
  have he := two_seconds_zero_disturbance ht.1
  dsimp at hh
  obtain ⟨hx,hv,ha,hu⟩ := hh
  constructor
  · simpa using hx.trans (by simpa using he)
  · constructor <;> nlinarith

/-- A real trajectory with a finished reference and zero disturbance still
has nonzero velocity at every finite time. This refutes exact finite rest. -/
def nonrest (A t : ℝ) : State :=
  ![A*Real.exp (-4*t), -4*A*Real.exp (-4*t), 16*A*Real.exp (-4*t)]

theorem nonrest_isTrajectory (A H : ℝ) :
    IsTrajectory H (fun _ => 8)
      (fun t => command 0 (nonrest A t)+(0:ℝ)) (nonrest A) := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [nonrest] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-4:ℝ)).exp)
    fin_cases i
    · convert he.const_mul A using 1 <;> dsimp [nonrest] <;> ring
    · convert he.const_mul (-4*A) using 1 <;> dsimp [nonrest] <;> ring
    · convert he.const_mul (16*A) using 1 <;> dsimp [nonrest,command] <;> ring

theorem nonrest_initial_cube {A : ℝ} (hA : 0 ≤ A) :
    ∀ i, |coordinates 0 (nonrest A 0) i| ≤ A := by
  intro i
  fin_cases i <;> simp [nonrest,coordinates,abs_of_nonneg hA] <;>
    ring_nf <;> simp [abs_of_nonneg hA,hA]

theorem nonrest_velocity_ne_zero {A : ℝ} (hA : 0 < A) (t : ℝ) :
    nonrest A t 1 ≠ 0 := by
  dsimp [nonrest]
  exact ne_of_lt (mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _))

/-- A constant nonzero disturbance can coexist with exact rest. It shifts the
position equilibrium; the conservative speed floor is not a physical impossibility. -/
theorem biased_equilibrium_isTrajectory (H c W : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r
      (fun _ => command c (![c+W/8,0,0])+W)
      (fun _ => ![c+W/8,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro t ht i
    convert hasDerivAt_const t (![c+W/8,0,0] i) using 1 <;>
      fin_cases i <;> dsimp [command] <;> ring

end LeanControls.SettlingFixtures
