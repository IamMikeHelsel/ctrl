module
public import QuadraticAlgebra
@[expose] public section
noncomputable section
namespace LeanControls.QuadraticHold
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def qState (c : ℝ) (s : State) : State :=
  ![80000*(s 0-c),2000*s 1,50*s 2]

/-- The dimensionless state comes from the actual physical state. No reset. -/
theorem qState_ode {H c : ℝ} {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+w t) f)
    (t : ℝ) (ht : t ∈ Ioo 0 H) :
    HasDerivAt (fun s => qState c (f s) 0) (40*qState c (f t) 1) t ∧
    HasDerivAt (fun s => qState c (f s) 1) (40*qState c (f t) 2) t ∧
    HasDerivAt (fun s => qState c (f s) 2)
      (-r t/2*qState c (f t) 0-3*r t/2*qState c (f t) 1-
       3*r t/2*qState c (f t) 2+r t/2*(100*w t)) t := by
  have hx := hf.ode t ht 0
  have hv := hf.ode t ht 1
  have ha := hf.ode t ht 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx hv ha
  refine ⟨?_,?_,?_⟩
  · convert (hx.sub_const c).const_mul 80000 using 1 <;> dsimp [qState] <;> ring
  · convert hv.const_mul 2000 using 1 <;> dsimp [qState] <;> ring
  · convert ha.const_mul 50 using 1 <;>
      dsimp [qState,holdInput,command,scaleState] <;> ring

/-- Exact differentiation of the selected quadratic along the scaled ODE. -/
theorem energy_derivative {x y z : ℝ → ℝ} {r d t : ℝ}
    (hx : HasDerivAt x (40*y t) t) (hy : HasDerivAt y (40*z t) t)
    (hz : HasDerivAt z (-r/2*x t-3*r/2*y t-3*r/2*z t+r/2*d) t) :
    HasDerivAt (fun s => energy (x s) (y s) (z s))
      (energyRate r d (x t) (y t) (z t)) t := by
  convert (((((hx.pow 2).const_mul 49597375).add ((hx.mul hy).const_mul 120006000)).add
    ((hx.mul hz).const_mul 51027750)).add ((hy.pow 2).const_mul 212058000) |>.add
    ((hy.mul hz).const_mul 113732000) |>.add ((hz.pow 2).const_mul 102314375)).div_const
    68317631 using 1 <;> dsimp [energy,energyRate] <;> ring

/-- The actual trajectory obeys one scalar comparison. The rate and disturbance
only need pointwise bounds; no derivative or constancy premise is introduced. -/
theorem energy_envelope {H c : ℝ} (hH : 0 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hi : energy (qState c (f 0) 0) (qState c (f 0) 1) (qState c (f 0) 2) ≤ 1000000) :
    ∀ t ∈ Icc 0 H,
      energy (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2) ≤
        1+999999*Real.exp (-20*t) := by
  let V : ℝ → ℝ := fun t => energy (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2)
  let dV : ℝ → ℝ := fun t => energyRate (r t) (100*w t)
    (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2)
  let G : ℝ → ℝ := fun t => 1+999999*Real.exp (-20*t)
  let dG : ℝ → ℝ := fun t => -20*999999*Real.exp (-20*t)
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc : ContinuousOn V (Icc 0 H) := by dsimp [V,energy,qState]; fun_prop
  have hgc : ContinuousOn G (Icc 0 H) := by dsimp [G]; fun_prop
  have hdv (t : ℝ) (ht : t ∈ Ioo 0 H) : HasDerivAt V (dV t) t := by
    obtain ⟨hx,hy,hz⟩ := qState_ode hf t ht
    exact energy_derivative hx hy hz
  have hdg (t : ℝ) (_ht : t ∈ Ioo 0 H) : HasDerivAt G (dG t) t := by
    convert (((((hasDerivAt_id t).const_mul (-20:ℝ)).exp).const_mul 999999).const_add 1) using 1 <;>
      dsimp [G,dG] <;> ring
  apply linear_comparison hH (r:=fun _ => 20) continuousOn_const hc hgc hdv hdg
  · simpa [V,G] using hi
  · intro t ht
    have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
    have hwt : |100*w t| ≤ 1 := by
      rw [abs_mul]; norm_num
      linarith [hw t htc]
    have hh := dissipation (hrlo t htc) (hrhi t htc) hwt
      (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2)
    dsimp [V,dV,G,dG]
    linarith

/-- Loose exact arithmetic is sufficient for entry after two seconds. -/
theorem two_second_energy {t : ℝ} (ht : 2 ≤ t) :
    1+999999*Real.exp (-20*t) ≤ 101/100 := by
  have he40 : Real.exp (-40:ℝ) ≤ 1/1099511627776 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos (-4:ℝ)).le exp_neg_four_le 10
    have heq : Real.exp (-40:ℝ) = Real.exp (-4:ℝ)^10 := by
      simpa using Real.exp_nat_mul (-4:ℝ) 10
    rw [heq]
    norm_num at hp ⊢
    exact hp
  have he := (Real.exp_le_exp.mpr (show -20*t ≤ -40 by linarith)).trans he40
  linarith

/-- The original inherited cube supplies all physical initial-state components. -/
theorem cube_energy_initial {c : ℝ} {s : State}
    (hi : ∀ i, |coordinates c (scaleState 10 s) i| ≤ 1/5000) :
    energy (qState c s 0) (qState c s 1) (qState c s 2) ≤ 1000000 := by
  obtain ⟨hx,hv,ha,hu⟩ := cube_physical_bounds hi
  norm_num [scaleState,abs_div] at hx hv ha
  apply initial_energy
  · dsimp [qState]; rw [abs_mul]; norm_num; linarith
  · dsimp [qState]; rw [abs_mul]; norm_num; linarith
  · dsimp [qState]; rw [abs_mul]; norm_num; linarith

/-- For every classical hold trajectory of the original controller, arbitrary
bounded changing response and disturbance satisfy the original speed and
acceleration targets at all times from two seconds to the horizon. -/
theorem two_seconds_actual_changing_input {H c : ℝ} (hH : 0 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hi : ∀ i, |coordinates c (scaleState 10 (f 0)) i| ≤ 1/5000) :
    ∀ t ∈ Icc 2 H, |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50 := by
  have henv := energy_envelope hH hf hrlo hrhi hw (cube_energy_initial hi)
  intro t ht
  have hb := (henv t ⟨by linarith [ht.1],ht.2⟩).trans (two_second_energy ht.1)
  have hv := speed_coordinate (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2)
  have ha := acceleration_coordinate (qState c (f t) 0) (qState c (f t) 1) (qState c (f t) 2)
  have hv2 : (qState c (f t) 1)^2 ≤ 4 := by linarith
  have ha2 : (qState c (f t) 2)^2 ≤ 1 := by linarith
  dsimp [qState] at hv2 ha2
  constructor
  · apply abs_le.mpr; constructor <;> nlinarith
  · apply abs_le.mpr; constructor <;> nlinarith

end LeanControls.QuadraticHold
