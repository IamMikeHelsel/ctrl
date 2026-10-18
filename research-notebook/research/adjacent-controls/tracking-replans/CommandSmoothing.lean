module
public import ScaledTracking
@[expose] public section
noncomputable section
namespace LeanControls.CommandSmoothing
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking

/-- A filter can reuse the tracking certificate only if its actual command error
is included in the disturbance budget. This does not prove a filter maintains D. -/
theorem tracking_under_bounded_filter_error {σ H R W D J : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r w j u : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => u t+w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,j t] i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hj : ∀ t ∈ Icc 0 H, |j t| ≤ J)
    (hfilter : ∀ t ∈ Icc 0 H, |u t-physicalInput σ f q j t| ≤ D)
    (budget : W+D+J/(48*σ) ≤ 2*σ^2*R)
    (hi : ∀ i, |coordinates 0 (scaledError σ f q 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R := by
  let w' := fun t => w t+(u t-physicalInput σ f q j t)
  have hf' : IsTrajectory H r (fun t => physicalInput σ f q j t+w' t) f := by
    have heq : (fun t => physicalInput σ f q j t+w' t) = (fun t => u t+w t) := by
      funext t
      dsimp [w']
      ring
    rw [heq]
    exact hf
  apply tracking_cube_scaled hσ hH hR hf' hq hdq hrlo hrhi _ hj budget hi
  intro t ht
  exact (abs_add_le _ _).trans (add_le_add (hw t ht) (hfilter t ht))

/-- With matched physical and reference states, jerk feedforward alone causes
this exact jump in the nominal acceleration target. -/
theorem matched_target_jump (σ h jOld jNew : ℝ) {f g q p : ℝ → State}
    (hf : g 0 = f h) (hq : p 0 = q h) :
    physicalInput σ g p (fun _ => jNew) 0 -
      physicalInput σ f q (fun _ => jOld) h = (5/(48*σ))*(jNew-jOld) := by
  unfold physicalInput
  rw [hf,hq]
  ring

/-- A continuous filter retains its state u at the switch. Its error must
absorb the nominal target jump; it cannot reset to zero on both sides. -/
theorem matched_mismatch_transfer (σ h jOld jNew u : ℝ) {f g q p : ℝ → State}
    (hf : g 0 = f h) (hq : p 0 = q h) :
    u-physicalInput σ g p (fun _ => jNew) 0 =
      (u-physicalInput σ f q (fun _ => jOld) h)-(5/(48*σ))*(jNew-jOld) := by
  linarith [matched_target_jump σ h jOld jNew hf hq]

/-- A necessary two-sided condition for any retained filter state to fit D. -/
theorem admissible_target_jump {u oldTarget newTarget D : ℝ}
    (ho : |u-oldTarget| ≤ D) (hn : |u-newTarget| ≤ D) :
    |newTarget-oldTarget| ≤ 2*D := by
  obtain ⟨hol,hou⟩ := abs_le.mp ho
  obtain ⟨hnl,hnu⟩ := abs_le.mp hn
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Extra filter-error allowance in the earlier .2 mm illustrative contract. -/
theorem illustrative_filter_budget (D : ℝ) :
    (1:ℝ)/100+D+10/(48*10) ≤ 2*10^2*(1/5000) ↔ D ≤ 11/1200 := by
  constructor <;> intro h <;> linarith

/-- A -10 to +10 m/s³ planned-jerk switch at σ=10 changes the nominal
acceleration target by 5/24 m/s². No continuous filter state can fit the same
11/1200 budget on both sides. This rejects certificate transfer, not safety. -/
theorem illustrative_jump_incompatible :
    ¬ ∃ d : ℝ, |d| ≤ 11/1200 ∧ |d-5/24| ≤ 11/1200 := by
  rintro ⟨d,hd,hn⟩
  have ha := (abs_le.mp hd).2
  have hb := (abs_le.mp hn).1
  linarith

/-- Even a continuous command does not force matching physical jerk across a
rate/disturbance switch. This is an exact right-hand-side jump identity. -/
theorem continuous_command_jerk_jump (u a rBefore rAfter wBefore wAfter : ℝ) :
    rAfter*(u+wAfter-a)-rBefore*(u+wBefore-a) =
      (rAfter-rBefore)*(u+wBefore-a)+rAfter*(wAfter-wBefore) := by ring

end LeanControls.CommandSmoothing
