module
public import ComparisonEnvelope
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.QuadraticSlowFilter
open Set
open scoped Matrix
open VariableResponse
open UncertainLag (State)
abbrev Vector := Fin 4 → ℝ

def A (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,0,0; 0,0,1,0; 0,0,-r,r; -16,-12,-1,-2]
def P : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(227:ℝ),(16487/100:ℝ),(82/5:ℝ),(143/100:ℝ);
     (16487/100:ℝ),(14809/100:ℝ),(1421/100:ℝ),(1567/100:ℝ);
     (82/5:ℝ),(1421/100:ℝ),(311/100:ℝ),(9/25:ℝ);
     (143/100:ℝ),(1567/100:ℝ),(9/25:ℝ),(1027/100:ℝ)]
def rhs (r : ℝ) (x : Vector) : Vector :=
  ![x 1,x 2,-r*x 2+r*x 3,-16*x 0-12*x 1-x 2-2*x 3]
def normSq (x : Vector) : ℝ := (x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2
def energy (x : Vector) : ℝ :=
  (227:ℝ) * (x 0)^2 + (16487/50:ℝ) * x 0 * x 1 + (164/5:ℝ) * x 0 * x 2 + (143/50:ℝ) * x 0 * x 3 + (14809/100:ℝ) * (x 1)^2 + (1421/50:ℝ) * x 1 * x 2 + (1567/50:ℝ) * x 1 * x 3 + (311/100:ℝ) * (x 2)^2 + (18/25:ℝ) * x 2 * x 3 + (1027/100:ℝ) * (x 3)^2
def dEnergy (r : ℝ) (x : Vector) : ℝ :=
  (227:ℝ) * (2*x 0*rhs r x 0) +
    (16487/50:ℝ) * (rhs r x 0*x 1+x 0*rhs r x 1) +
    (164/5:ℝ) * (rhs r x 0*x 2+x 0*rhs r x 2) +
    (143/50:ℝ) * (rhs r x 0*x 3+x 0*rhs r x 3) +
    (14809/100:ℝ) * (2*x 1*rhs r x 1) +
    (1421/50:ℝ) * (rhs r x 1*x 2+x 1*rhs r x 2) +
    (1567/50:ℝ) * (rhs r x 1*x 3+x 1*rhs r x 3) +
    (311/100:ℝ) * (2*x 2*rhs r x 2) +
    (18/25:ℝ) * (rhs r x 2*x 3+x 2*rhs r x 3) +
    (1027/100:ℝ) * (2*x 3*rhs r x 3)

def sos_lower (x : Vector) : ℝ :=
  (453/2:ℝ) * ((1:ℝ) * x 0 + (16487/22650:ℝ) * x 1 + (164/2265:ℝ) * x 2 + (143/22650:ℝ) * x 3)^2 +
    (62470181/2265000:ℝ) * ((1:ℝ) * x 1 + (5146970/62470181:ℝ) * x 2 + (33134909/62470181:ℝ) * x 3)^2 +
    (7717030751/6247018100:ℝ) * ((1:ℝ) * x 2 + (-5927448293/7717030751:ℝ) * x 3)^2 +
    (982162617761/771703075100:ℝ) * ((1:ℝ) * x 3)^2

theorem lower_identity (x : Vector) : energy x-(1/2)*normSq x = sos_lower x := by
  dsimp [energy,dEnergy,rhs,normSq,sos_lower]
  ring

theorem sos_lower_nonneg (x : Vector) : 0 ≤ sos_lower x := by
  dsimp [sos_lower]
  positivity

def sos_q8 (x : Vector) : ℝ :=
  (2263/50:ℝ) * ((1:ℝ) * x 0 + (28/31:ℝ) * x 1 + (-1324/2263:ℝ) * x 2 + (1799/2263:ℝ) * x 3)^2 +
    (1382/155:ℝ) * ((1:ℝ) * x 1 + (-10699/13820:ℝ) * x 2 + (21613/27640:ℝ) * x 3)^2 +
    (36507977/50443000:ℝ) * ((1:ℝ) * x 2 + (-23400119/73015954:ℝ) * x 3)^2 +
    (2523567219/3650797700:ℝ) * ((1:ℝ) * x 3)^2

theorem q8_identity (x : Vector) : -dEnergy 8 x-(1/2)*normSq x = sos_q8 x := by
  dsimp [energy,dEnergy,rhs,normSq,sos_q8]
  ring

theorem sos_q8_nonneg (x : Vector) : 0 ≤ sos_q8 x := by
  dsimp [sos_q8]
  positivity

def sos_q12 (x : Vector) : ℝ :=
  (2263/50:ℝ) * ((1:ℝ) * x 0 + (28/31:ℝ) * x 1 + (1956/2263:ℝ) * x 2 + (-1481/2263:ℝ) * x 3)^2 +
    (1382/155:ℝ) * ((1:ℝ) * x 1 + (-14437/13820:ℝ) * x 2 + (29089/27640:ℝ) * x 3)^2 +
    (146134073/50443000:ℝ) * ((1:ℝ) * x 2 + (-229595021/292268146:ℝ) * x 3)^2 +
    (13038256101/14613407300:ℝ) * ((1:ℝ) * x 3)^2

theorem q12_identity (x : Vector) : -dEnergy 12 x-(1/2)*normSq x = sos_q12 x := by
  dsimp [energy,dEnergy,rhs,normSq,sos_q12]
  ring

theorem sos_q12_nonneg (x : Vector) : 0 ≤ sos_q12 x := by
  dsimp [sos_q12]
  positivity

def sos_upper (x : Vector) : ℝ :=
  (273:ℝ) * ((1:ℝ) * x 0 + (-16487/27300:ℝ) * x 1 + (-82/1365:ℝ) * x 2 + (-11/2100:ℝ) * x 3)^2 +
    (688893131/2730000:ℝ) * ((1:ℝ) * x 1 + (-65831980/688893131:ℝ) * x 2 + (-45136741/688893131:ℝ) * x 3)^2 +
    (34003791864799/68889313100:ℝ) * ((1:ℝ) * x 2 + (-139562066557/34003791864799:ℝ) * x 3)^2 +
    (1661530348195576211/3400379186479900:ℝ) * ((1:ℝ) * x 3)^2

theorem upper_identity (x : Vector) : 500*normSq x-energy x = sos_upper x := by
  dsimp [energy,dEnergy,rhs,normSq,sos_upper]
  ring

theorem sos_upper_nonneg (x : Vector) : 0 ≤ sos_upper x := by
  dsimp [sos_upper]
  positivity

theorem energy_lower (x : Vector) : (1/2)*normSq x ≤ energy x := by
  linarith [lower_identity x,sos_lower_nonneg x]
theorem energy_upper (x : Vector) : energy x ≤ 500*normSq x := by
  linarith [upper_identity x,sos_upper_nonneg x]
theorem endpoint8 (x : Vector) : dEnergy 8 x ≤ -(1/2)*normSq x := by
  linarith [q8_identity x,sos_q8_nonneg x]
theorem endpoint12 (x : Vector) : dEnergy 12 x ≤ -(1/2)*normSq x := by
  linarith [q12_identity x,sos_q12_nonneg x]

theorem matrix_rhs (r : ℝ) (x : Vector) : A r *ᵥ x = rhs r x := by
  ext i
  fin_cases i <;> simp [A,rhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem matrix_energy (x : Vector) : x ⬝ᵥ (P *ᵥ x) = energy x := by
  simp [P,energy,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem P_symmetric : P.transpose = P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P,Matrix.transpose_apply]

theorem normSq_pos {x : Vector} (hx : x ≠ 0) : 0 < normSq x := by
  have hs0 := sq_nonneg (x 0)
  have hs1 := sq_nonneg (x 1)
  have hs2 := sq_nonneg (x 2)
  have hs3 := sq_nonneg (x 3)
  by_contra h
  have hzero : x = 0 := by
    have h0 : x 0 = 0 := sq_eq_zero_iff.mp (by dsimp [normSq] at h; linarith)
    have h1 : x 1 = 0 := sq_eq_zero_iff.mp (by dsimp [normSq] at h; linarith)
    have h2 : x 2 = 0 := sq_eq_zero_iff.mp (by dsimp [normSq] at h; linarith)
    have h3 : x 3 = 0 := sq_eq_zero_iff.mp (by dsimp [normSq] at h; linarith)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  exact hx hzero

theorem P_positive_definite : P.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using P_symmetric
  · intro x hx
    simpa only [star_trivial,matrix_energy] using
      (show 0 < energy x from lt_of_lt_of_le (by linarith [normSq_pos hx]) (energy_lower x))

theorem interval_dissipation {r : ℝ} (hlo : 8 ≤ r) (hhi : r ≤ 12) (x : Vector) :
    dEnergy r x ≤ -(1/2)*normSq x := by
  have h8 := mul_le_mul_of_nonneg_left (endpoint8 x) (show 0 ≤ (12-r)/4 by linarith)
  have h12 := mul_le_mul_of_nonneg_left (endpoint12 x) (show 0 ≤ (r-8)/4 by linarith)
  have hid : dEnergy r x = ((12-r)/4)*dEnergy 8 x+((r-8)/4)*dEnergy 12 x := by
    dsimp [dEnergy,rhs]; ring
  calc
    _ = _ := hid
    _ ≤ ((12-r)/4)*(-(1/2)*normSq x)+((r-8)/4)*(-(1/2)*normSq x) := add_le_add h8 h12
    _ = _ := by ring

theorem matrix_dissipation (r : ℝ) (x : Vector) :
    x ⬝ᵥ (((A r).transpose * P + P * A r) *ᵥ x) = dEnergy r x := by
  simp [A,P,dEnergy,rhs,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_succ]
  ring

theorem common_quadratic_certificate : P.PosDef ∧ (0:ℝ) < 1/2 ∧
    ∀ r, 8 ≤ r → r ≤ 12 → ∀ x : Vector,
      x ⬝ᵥ (((A r).transpose * P + P * A r) *ᵥ x) ≤ -(1/2)*normSq x := by
  refine ⟨P_positive_definite,by norm_num,?_⟩
  intro r hlo hhi x
  rw [matrix_dissipation]
  exact interval_dissipation hlo hhi x

theorem energy_derivative {x : ℝ → Vector} {r t : ℝ}
    (hd : ∀ i, HasDerivAt (fun s => x s i) (rhs r (x t) i) t) :
    HasDerivAt (fun s => energy (x s)) (dEnergy r (x t)) t := by
  convert ((((((((((((hd 0).pow 2).const_mul (227:ℝ)).add (((hd 0).mul (hd 1)).const_mul (16487/50:ℝ))).add (((hd 0).mul (hd 2)).const_mul (164/5:ℝ))).add (((hd 0).mul (hd 3)).const_mul (143/50:ℝ))).add (((hd 1).pow 2).const_mul (14809/100:ℝ))).add (((hd 1).mul (hd 2)).const_mul (1421/50:ℝ))).add (((hd 1).mul (hd 3)).const_mul (1567/50:ℝ))).add (((hd 2).pow 2).const_mul (311/100:ℝ))).add (((hd 2).mul (hd 3)).const_mul (18/25:ℝ))).add (((hd 3).pow 2).const_mul (1027/100:ℝ))) using 1 <;> (try funext s) <;> dsimp [energy,dEnergy] <;> ring

/-- Conditional decay for a supplied continuous, interior-classical augmented
trajectory. The rate may vary arbitrarily within the stated interval. -/
theorem energy_decay {H : ℝ} (hH : 0 ≤ H) {r : ℝ → ℝ} {x : ℝ → Vector}
    (hc : ContinuousOn x (Icc 0 H))
    (hd : ∀ t ∈ Ioo 0 H, ∀ i, HasDerivAt (fun s => x s i) (rhs (r t) (x t) i) t)
    (hlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hhi : ∀ t ∈ Icc 0 H, r t ≤ 12) :
    ∀ t ∈ Icc 0 H, energy (x t) ≤ Real.exp (-t/1000)*energy (x 0) := by
  have hxc (i : Fin 4) := (continuous_apply i).comp_continuousOn hc
  have hec : ContinuousOn (fun t => energy (x t)) (Icc 0 H) := by
    dsimp [energy]; fun_prop
  have hgc : ContinuousOn (fun t => Real.exp (-t/1000)*energy (x 0)) (Icc 0 H) := by fun_prop
  have hgd (t : ℝ) : HasDerivAt (fun t => Real.exp (-t/1000)*energy (x 0))
      (-(1/1000)*Real.exp (-t/1000)*energy (x 0)) t := by
    convert (((hasDerivAt_id t).neg.div_const 1000).exp).mul_const (energy (x 0)) using 1 <;> (try funext s) <;> dsimp <;> ring
  apply linear_comparison (r := fun _ => (1:ℝ)/1000) hH continuousOn_const hec hgc
    (fun t ht => energy_derivative (hd t ht)) (fun t _ => hgd t)
  · simp
  · intro t ht
    have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
    have hdis := interval_dissipation (hlo t htc) (hhi t htc) (x t)
    have hup := energy_upper (x t)
    linarith

/-- The augmented state for zero disturbance and zero reference jerk. -/
def augmented (f q : ℝ → State) (u : ℝ → ℝ) (t : ℝ) : Vector :=
  ![f t 0-q t 0,f t 1-q t 1,f t 2-q t 2,u t-q t 2]

def target (f q : ℝ → State) (t : ℝ) : ℝ :=
  q t 2-8*(f t 0-q t 0)-6*(f t 1-q t 1)-(f t 2-q t 2)/2

theorem actual_augmented_ode {H : ℝ} {f q : ℝ → State} {u r : ℝ → ℝ}
    (hf : IsTrajectory H r u f)
    (hq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,0] i) t)
    (hu : ∀ t ∈ Ioo 0 H, HasDerivAt u (2*(target f q t-u t)) t)
    (t : ℝ) (ht : t ∈ Ioo 0 H) (i : Fin 4) :
    HasDerivAt (fun s => augmented f q u s i) (rhs (r t) (augmented f q u t) i) t := by
  fin_cases i
  · convert (hf.ode t ht 0).sub (hq t ht 0) using 1 <;> (try funext s) <;> simp [augmented,rhs]
  · convert (hf.ode t ht 1).sub (hq t ht 1) using 1 <;> (try funext s) <;> simp [augmented,rhs]
  · convert (hf.ode t ht 2).sub (hq t ht 2) using 1 <;> (try funext s) <;> simp [augmented,rhs] <;> ring
  · convert (hu t ht).sub (hq t ht 2) using 1 <;> (try funext s) <;> simp [augmented,rhs,target] <;> ring

/-- Actual plant and filter at lambda=2, sigma=1. Supplied trajectories remain
a premise. No forcing, replan, stopping, or measured smoothness claim follows. -/
theorem actual_homogeneous_decay {H : ℝ} (hH : 0 ≤ H)
    {f q : ℝ → State} {u r : ℝ → ℝ}
    (hf : IsTrajectory H r u f) (hqc : ContinuousOn q (Icc 0 H))
    (hq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,0] i) t)
    (huc : ContinuousOn u (Icc 0 H))
    (hu : ∀ t ∈ Ioo 0 H, HasDerivAt u (2*(target f q t-u t)) t)
    (hlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hhi : ∀ t ∈ Icc 0 H, r t ≤ 12) :
    ∀ t ∈ Icc 0 H, energy (augmented f q u t) ≤
      Real.exp (-t/1000)*energy (augmented f q u 0) := by
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hqc' (i : Fin 3) := (continuous_apply i).comp_continuousOn hqc
  have hc : ContinuousOn (augmented f q u) (Icc 0 H) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [augmented] <;> fun_prop
  exact energy_decay hH hc (fun t ht i => actual_augmented_ode hf hq hu t ht i) hlo hhi

theorem false_stronger_margin_witness :
    -dEnergy 8 ![1,0,0,0] < 100*normSq ![1,0,0,0] := by
  norm_num [dEnergy,rhs,normSq]

end LeanControls.QuadraticSlowFilter
