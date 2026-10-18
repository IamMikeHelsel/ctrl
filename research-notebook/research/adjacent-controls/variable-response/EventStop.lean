module
public import ActualStop

/-! First-stop guarantees with braking dynamics and target bounds required only
while every velocity up to the current time is positive. The target may switch
at the first zero itself. The post-event trajectory remains unspecified. -/
@[expose] public section
noncomputable section
namespace LeanControls.EventStop
open Set
open UncertainLag (State heldSolution)
open VariableResponse StoppingCertificate ActualStop

/-- The current instant is included, so this guard is false at the first zero. -/
def BeforeStop (D : ℝ) (f : ℝ → State) (t : ℝ) : Prop :=
  ∀ s ∈ Icc 0 (D+t), 0 < f s 1

/-- Actual braking equations only while the stop event has not occurred. -/
def GuardedBraking (D H : ℝ) (r b : ℝ → ℝ) (f : ℝ → State) : Prop :=
  ∀ t ∈ Ioo 0 H, BeforeStop D f t → ∀ i : Fin 3,
    HasDerivAt (fun s => f (D+s) i)
      (![f (D+t) 1, f (D+t) 2, r t*(b t-f (D+t) 2)] i) t

/-- A continuous nonnegative-initial velocity either has a first zero on the
closed horizon or stays strictly positive on the whole horizon. -/
theorem first_zero_or_positive {H : ℝ} (_hH : 0 ≤ H) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc 0 H)) (hv0 : 0 ≤ v 0) :
    (∃ T ∈ Icc 0 H, v T = 0 ∧ ∀ t ∈ Ico 0 T, 0 < v t) ∨
      (∀ t ∈ Icc 0 H, 0 < v t) := by
  by_cases he : ∃ t ∈ Icc 0 H, v t ≤ 0
  · obtain ⟨s, hs, hvs⟩ := he
    obtain ⟨T, hT, hz, hp⟩ := FirstStop.exists_first_zero hs.1
      (hv.mono (Icc_subset_Icc le_rfl hs.2)) hv0 hvs
    exact Or.inl ⟨T, ⟨hT.1, hT.2.trans hs.2⟩, hz, hp⟩
  · exact Or.inr fun t ht => lt_of_not_ge fun h => he ⟨t, ht, h⟩

/-- Comparison up to a possible stop endpoint. The auxiliary target agrees
with the actual target strictly before S and is set to -1.2 at S. This only
supplies the comparison lemma's closed endpoint bound: no actual target or
ODE requirement is imposed at the stop instant or after it. -/
theorem guarded_flow_bound {D S : ℝ} (hD0 : 0 ≤ D) (hS0 : 0 ≤ S) (hS1 : S ≤ 1/2)
    {f : ℝ → State} {r b : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (D+1/2)))
    (hguard : GuardedBraking D (1/2) r b f)
    (hrc : ContinuousOn r (Icc 0 (1/2)))
    (hrlo : ∀ t ∈ Icc 0 (1/2), 8 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 (1/2), r t ≤ 12)
    (hb : ∀ t ∈ Icc 0 (1/2), BeforeStop D f t → b t ≤ -6/5)
    (hinit : ∀ i : Fin 3, f D i ≤ engagementUpper i)
    (hbefore : ∀ t ∈ Ico 0 (D+S), 0 < f t 1) :
    ∀ t ∈ Icc 0 S, ∀ i : Fin 3,
      f (D+t) i ≤ heldSolution 8 t (-6/5) engagementUpper i := by
  let bCut : ℝ → ℝ := fun t => if t < S then b t else -6/5
  have hactive {t : ℝ} (ht : t < S) : BeforeStop D f t := by
    intro s hs
    exact hbefore s ⟨hs.1, lt_of_le_of_lt hs.2 (by linarith)⟩
  have hcut : IsTrajectory S r bCut (fun t => f (D+t)) := by
    constructor
    · exact hfc.comp (continuous_const.add continuous_id).continuousOn
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · intro t ht i
      simpa only [bCut, ite_eq_left ht.2] using
        hguard t ⟨ht.1, ht.2.trans_le hS1⟩ (hactive ht.2) i
  have hbcut : ∀ t ∈ Icc 0 S, bCut t ≤ -6/5 := by
    intro t ht
    dsimp only [bCut]
    split_ifs with hlt
    · exact hb t ⟨ht.1, ht.2.trans hS1⟩ (hactive hlt)
    · exact le_rfl
  have hu := upper_flow_bound (rlo := 8) (rhi := 12) (bHi := -6/5)
    (zHi := engagementUpper) hS0
    (hrc.mono (Icc_subset_Icc le_rfl hS1)) (by norm_num)
    (fun t ht => hrlo t ⟨ht.1, ht.2.trans hS1⟩)
    (fun t ht => hrhi t ⟨ht.1, ht.2.trans hS1⟩) hbcut hcut
    (by simpa using hinit)
  have hrate : upperRate 8 12 (engagementUpper 2) (-6/5) = 8 := by
    norm_num [upperRate, engagementUpper]
  simpa only [hrate] using hu

/-- The first-stop certificate needs no braking ODE or target constraint at
or after the first zero. The actual target may change to a hold command there.
This theorem does not certify the later hold motion or maintained rest. -/
theorem delayed_event_first_stop {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1/20)
    {f : ℝ → State} {r b : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (D+1/2)))
    (hdelay : IsDelayTrajectory D f)
    (hx : f 0 0 ≤ 1/1000) (hv0 : 0 ≤ f 0 1) (hv1 : f 0 1 ≤ 41/100)
    (ha : ∀ t ∈ Icc 0 D, f t 2 ≤ 1/10)
    (hguard : GuardedBraking D (1/2) r b f)
    (hrc : ContinuousOn r (Icc 0 (1/2)))
    (hrlo : ∀ t ∈ Icc 0 (1/2), 8 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 (1/2), r t ≤ 12)
    (hb : ∀ t ∈ Icc 0 (1/2), BeforeStop D f t → b t ≤ -6/5) :
    ∃ T ∈ Icc 0 (D+1/2), T ≤ 11/20 ∧ f T 1 = 0 ∧
      (∀ t ∈ Ico 0 T, 0 < f t 1) ∧ ∀ t ∈ Icc 0 T, f t 0 ≤ 3/20 := by
  obtain ⟨hinit, hprefix⟩ := delay_engagement hD0 hD1 hdelay hx hv1 ha
  rcases first_zero_or_positive (v := fun t => f t 1) (by linarith : 0 ≤ D+1/2)
      ((continuous_apply 1).comp_continuousOn hfc) hv0 with hz | hpos
  · obtain ⟨T, hT, hz, hbefore⟩ := hz
    refine ⟨T, hT, by linarith [hT.2], hz, hbefore, ?_⟩
    intro t ht
    by_cases htd : t ≤ D
    · exact hprefix t ⟨ht.1, htd⟩
    · have hS0 : 0 ≤ T-D := by linarith [ht.2]
      have hS1 : T-D ≤ 1/2 := by linarith [hT.2]
      have hbefore' : ∀ s ∈ Ico 0 (D+(T-D)), 0 < f s 1 := by
        simpa only [add_sub_cancel] using hbefore
      have hu := guarded_flow_bound hD0 hS0 hS1 hfc hguard hrc hrlo hrhi hb hinit hbefore'
      have hs : t-D ∈ Icc 0 (T-D) := ⟨by linarith, by linarith [ht.2]⟩
      have hp := (hu (t-D) hs 0).trans (upper_position_le hs.1)
      simpa only [add_sub_cancel] using hp
  · have hu := guarded_flow_bound hD0 (by norm_num : (0:ℝ) ≤ 1/2) le_rfl
      hfc hguard hrc hrlo hrhi hb hinit
      (fun t ht => hpos t ⟨ht.1, ht.2.le⟩)
    have hvend := (hu (1/2) ⟨by norm_num, le_rfl⟩ 1).trans upper_velocity_by_half_second
    have hpositive := hpos (D+1/2) ⟨by linarith, le_rfl⟩
    linarith

end LeanControls.EventStop
#print axioms LeanControls.EventStop.first_zero_or_positive
#print axioms LeanControls.EventStop.guarded_flow_bound
#print axioms LeanControls.EventStop.delayed_event_first_stop
