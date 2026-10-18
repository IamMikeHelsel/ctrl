module
public import ConstantBias
@[expose] public section
noncomputable section
namespace LeanControls.BiasFixtures
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures ConstantBias

theorem offset_bound {b : ℝ} (hb : |b| ≤ 1/100) : |offset 10 b| ≤ 1/80000 := by
  dsimp [offset]
  rw [abs_div]
  norm_num
  linarith

theorem enlarged_cube_bound {b : ℝ} (hb : |b| ≤ 1/100) :
    (1/5000:ℝ)+|offset 10 b| ≤ 17/80000 := by linarith [offset_bound hb]

theorem two_second_transient {b t : ℝ} (hb : |b| ≤ 1/100) (ht : 2 ≤ t) :
    transient 10 (1/5000) b t ≤ 17/16384000 := by
  have he : Real.exp (-(2/5)*(10*t)) ≤ 1/256 := by
    have h := two_seconds_zero_disturbance ht
    nlinarith
  have hR := enlarged_cube_bound hb
  have hnonneg : 0 ≤ Real.exp (-(2/5)*(10*t)) := (Real.exp_pos _).le
  have hm := mul_le_mul hR he hnonneg (by norm_num : (0:ℝ) ≤ 17/80000)
  dsimp [transient]
  nlinarith

theorem two_second_constants :
    (1/80000:ℝ)+17/16384000 = 1109/81920000 ∧
    8*(10:ℝ)*(17/16384000) = 17/204800 ∧
    64*(10:ℝ)^2*(17/16384000) = 17/2560 ∧
    (17/204800:ℝ) < 1/1000 ∧ (17/2560:ℝ) < 1/50 := by norm_num

/-- H>=2 makes the certified interval nonempty. The original goal and the
actual initial state are retained. Only the bias is assumed constant. -/
theorem two_second_actual {H c b : ℝ} (hH : 2 ≤ H) (hb : |b| ≤ 1/100)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+b) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hi : ∀ i, |coordinates c (scaleState 10 (f 0)) i| ≤ 1/5000) :
    ∀ t ∈ Icc 2 H,
      |f t 0-c| ≤ 1109/81920000 ∧
      |f t 1| ≤ 17/204800 ∧ |f t 2| ≤ 17/2560 := by
  have h := physical_bounds (σ:=10) (R:=1/5000)
    (by norm_num) (by linarith) (by norm_num) hf
    (by convert hrlo using 1; norm_num) (by convert hrhi using 1; norm_num) hi
  intro t ht
  obtain ⟨hx,hv,ha,hu,hcmd⟩ := h t ⟨by linarith [ht.1],ht.2⟩
  have he := two_second_transient hb ht.1
  have ho := offset_bound hb
  constructor
  · linarith
  · constructor <;> nlinarith

theorem two_second_endpoint {H c b : ℝ} (hH : 2 ≤ H) (hb : |b| ≤ 1/100)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 c f t+b) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hi : ∀ i, |coordinates c (scaleState 10 (f 0)) i| ≤ 1/5000) :
    |f 2 0-c| ≤ 1109/81920000 ∧
      |f 2 1| ≤ 17/204800 ∧ |f 2 2| ≤ 17/2560 :=
  two_second_actual hH hb hf hrlo hrhi hi 2 ⟨le_rfl,hH⟩

end LeanControls.BiasFixtures
