module
public import SettlingFixtures
@[expose] public section
noncomputable section
namespace LeanControls.ConstantBias
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures

/-- An analysis offset. It is not a new controller command. -/
def offset (σ b : ℝ) : ℝ := b/(8*σ^2)

/-- The original controller plus constant bias is the zero-disturbance field
about a shifted equilibrium. The commanded goal remains c. -/
theorem input_shift {σ : ℝ} (hσ : 0 < σ) (c b : ℝ)
    (f : ℝ → State) (t : ℝ) :
    holdInput σ c f t+b = holdInput σ (c+offset σ b) f t := by
  dsimp [holdInput,command,scaleState,offset]
  field_simp
  ring

theorem coordinate_shift (c d : ℝ) (s : State) (i : Fin 3) :
    coordinates (c+d) s i = coordinates c s i-d := by
  fin_cases i <;> dsimp [coordinates] <;> ring

/-- Retain the actual state and enlarge only its analysis box. -/
theorem shifted_initial_cube {c d R : ℝ} {s : State}
    (hi : ∀ i, |coordinates c s i| ≤ R) :
    ∀ i, |coordinates (c+d) s i| ≤ R+|d| := by
  intro i
  rw [coordinate_shift]
  exact (abs_sub _ _).trans (add_le_add (hi i) le_rfl)

/-- This is the same physical trajectory with an equal right-hand side. -/
theorem biased_trajectory {σ H c b : ℝ} (hσ : 0 < σ)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput σ c f t+b) f) :
    IsTrajectory H r (fun t => holdInput σ (c+offset σ b) f t+(0:ℝ)) f := by
  have heq : (fun t => holdInput σ c f t+b) =
      (fun t => holdInput σ (c+offset σ b) f t+(0:ℝ)) := by
    funext t
    rw [add_zero,input_shift hσ]
  rw [heq] at hf
  exact hf

/-- The transient radius about the analysis equilibrium. -/
def transient (σ R b t : ℝ) : ℝ :=
  (5*(R+|offset σ b|)/4)*Real.exp (-(2/5)*(σ*t))

/-- Constant bias does not require a speed or acceleration floor. The position
bound about the true goal must retain the equilibrium offset. -/
theorem physical_bounds {σ H R c b : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput σ c f t+b) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hi : ∀ i, |coordinates c (scaleState σ (f 0)) i| ≤ R) :
    ∀ t ∈ Icc 0 H,
      |f t 0-c| ≤ |offset σ b|+transient σ R b t ∧
      |f t 1| ≤ 8*σ*transient σ R b t ∧
      |f t 2| ≤ 64*σ^2*transient σ R b t ∧
      |holdInput σ c f t+b| ≤ 24*σ^2*transient σ R b t ∧
      |holdInput σ c f t| ≤ 24*σ^2*transient σ R b t+|b| := by
  have hR' : 0 ≤ R+|offset σ b| := add_nonneg hR (abs_nonneg _)
  have hb := settling_physical_bounds (W:=0) hσ hH (by norm_num) hR'
    (biased_trajectory hσ hf) hrlo hrhi (by intro t ht; norm_num)
    (shifted_initial_cube (d:=offset σ b) hi)
  intro t ht
  have hh := hb t ht
  dsimp at hh
  simp only [mul_zero,zero_div,zero_add] at hh
  obtain ⟨hx,hv,ha,hu⟩ := hh
  have ht0 : |f t 0-c| ≤ |offset σ b|+transient σ R b t := by
    calc
      |f t 0-c| = |(f t 0-(c+offset σ b))+offset σ b| := by congr 1; ring
      _ ≤ |f t 0-(c+offset σ b)|+|offset σ b| := abs_add_le _ _
      _ ≤ |offset σ b|+transient σ R b t := by dsimp [transient]; linarith
  have ht3 : |holdInput σ c f t+b| ≤ 24*σ^2*transient σ R b t := by
    rw [input_shift hσ]
    exact hu
  refine ⟨ht0,hv,ha,ht3,?_⟩
  calc
    |holdInput σ c f t| = |(holdInput σ c f t+b)-b| := by congr 1; ring
    _ ≤ |holdInput σ c f t+b|+|b| := abs_sub _ _
    _ ≤ 24*σ^2*transient σ R b t+|b| := add_le_add ht3 le_rfl

/-- The shifted equilibrium itself is an exact physical realization for any
rate signal. A positive bias can coexist with exactly zero velocity. -/
theorem equilibrium_trajectory {σ : ℝ} (hσ : 0 < σ) (H c b : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r
      (fun t => holdInput σ c (fun _ => ![c+offset σ b,0,0]) t+b)
      (fun _ => ![c+offset σ b,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro t ht i
    rw [input_shift hσ]
    convert hasDerivAt_const t ((![c+offset σ b,0,0] : State) i) using 1 <;>
      fin_cases i <;> dsimp [holdInput,command,scaleState] <;> ring

end LeanControls.ConstantBias
