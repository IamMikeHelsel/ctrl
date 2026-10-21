module
public import ClearancePolicy
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.TimingBudget
open Set Filter DigitalHold WeightedEntry

/-- Exact overlap with the original pending interval. No timestamp is renewed. -/
def overlap (D s t : ℝ) : ℝ := min t D-min s D

theorem overlap_bounds {D s t : ℝ} (hD : 0≤D) (hs : 0≤s) (hst : s≤t) :
    0≤overlap D s t ∧ overlap D s t≤D ∧ overlap D s t≤t-s := by
  dsimp [overlap]
  constructor
  · exact sub_nonneg.mpr (min_le_min hst le_rfl)
  constructor
  · have h0 : 0≤min s D := le_min hs hD
    have h1 : min t D≤D := min_le_right _ _
    linarith
  · by_cases hds : D≤s
    · rw [min_eq_right hds,min_eq_right (hds.trans hst)]; linarith
    · by_cases htd : t≤D
      · rw [min_eq_left htd,min_eq_left (hst.trans htd)]
      · rw [min_eq_left (le_of_not_ge hds),min_eq_right (le_of_not_ge htd)]
        linarith

theorem segment_variation {H s t L : ℝ} {g dg : ℝ→ℝ}
    (hc : ContinuousOn g (Icc 0 H))
    (hd : ∀ x∈Ico 0 H, HasDerivWithinAt g (dg x) (Ici x) x)
    (hs : 0≤s) (hst : s≤t) (ht : t≤H)
    (hb : ∀ x∈Ico s t, |dg x|≤L) : |g t-g s|≤L*(t-s) := by
  have sub : Icc s t⊆Icc 0 H := Icc_subset_Icc hs ht
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_right_le_segment (hc.mono sub)
      (fun x hx => hd x ⟨hs.trans hx.1,hx.2.trans_le ht⟩)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx)
      t ⟨hst,le_rfl⟩

/-- Derivative jumps at D are allowed. The post-D segment uses the right side. -/
theorem phase_variation {H D s t P L : ℝ} {g dg : ℝ→ℝ}
    (hc : ContinuousOn g (Icc 0 H))
    (hd : ∀ x∈Ico 0 H, HasDerivWithinAt g (dg x) (Ici x) x)
    (hs : 0≤s) (hst : s≤t) (ht : t≤H)
    (hpre : ∀ x∈Ico 0 H, x<D → |dg x|≤P)
    (hpost : ∀ x∈Ico 0 H, D≤x → |dg x|≤L) :
    |g t-g s|≤P*overlap D s t+L*((t-s)-overlap D s t) := by
  by_cases hds : D≤s
  · have hh := segment_variation hc hd hs hst ht
      (fun x hx => hpost x ⟨hs.trans hx.1,hx.2.trans_le ht⟩ (hds.trans hx.1))
    simpa [overlap,min_eq_right hds,min_eq_right (hds.trans hst)] using hh
  · by_cases htd : t≤D
    · have hh := segment_variation hc hd hs hst ht
        (fun x hx => hpre x ⟨hs.trans hx.1,hx.2.trans_le ht⟩ (hx.2.trans_le htd))
      simpa [overlap,min_eq_left htd,min_eq_left (hst.trans htd)] using hh
    · have hsd : s<D := lt_of_not_ge hds
      have hdt : D<t := lt_of_not_ge htd
      have hp := segment_variation hc hd hs hsd.le (hdt.le.trans ht)
        (fun x hx => hpre x ⟨hs.trans hx.1,(hx.2.trans hdt).trans_le ht⟩ hx.2)
      have hq := segment_variation hc hd (hs.trans hsd.le) hdt.le ht
        (fun x hx => hpost x ⟨(hs.trans hsd.le).trans hx.1,hx.2.trans_le ht⟩ hx.1)
      have hh := abs_sub_le (g t) (g D) (g s)
      rw [overlap,min_eq_left hsd.le,min_eq_right hdt.le]
      linarith

/-- Age a and startup duration d are caps. The larger pending slope may be
charged only for the actual overlap, whose length is at most d. -/
theorem split_age {H D s t P L a d : ℝ} {g dg : ℝ→ℝ}
    (hc : ContinuousOn g (Icc 0 H))
    (hd : ∀ x∈Ico 0 H, HasDerivWithinAt g (dg x) (Ici x) x)
    (hs : 0≤s) (hst : s≤t) (ht : t≤H) (hD : 0≤D) (hDd : D≤d)
    (hage : t-s≤a) (hL : 0≤L) (hLP : L≤P)
    (hpre : ∀ x∈Ico 0 H, x<D → |dg x|≤P)
    (hpost : ∀ x∈Ico 0 H, D≤x → |dg x|≤L) :
    |g t-g s|≤L*a := by
  have hv := phase_variation hc hd hs hst ht hpre hpost
  have ho := overlap_bounds hD hs hst
  have hp := mul_nonneg (sub_nonneg.mpr hLP) (show 0≤d-overlap D s t by linarith)
  have hq := mul_nonneg hL (show 0≤a-(t-s) by linarith)
  nlinarith

def noise : ℝ := 103/1000
def coarseSlope (K : ℝ) : ℝ := 384*K+618/1000
def firstResidual (a K : ℝ) : ℝ := noise+a*coarseSlope K
def digitalSlope (a K : ℝ) : ℝ := 96*K+6*firstResidual a K
def splitResidual (a d K : ℝ) : ℝ := noise+8*d+digitalSlope a K*(a-d)
def closedResidual (a d K : ℝ) : ℝ := noise+8*d+108*K*(a-d)
def age : ℝ := 3/2000
def delay : ℝ := 1/2000
def supportRadius : ℝ := 567/10000
def residual : ℝ := 283/2500
def entryDrift : ℝ := 3/5000

theorem exact_expansion (a d K : ℝ) :
    splitResidual a d K=noise+8*d+(618/1000)*(a-d)*(1+6*a)+
      ((a-d)*(96+2304*a))*K := by
  dsimp [splitResidual,digitalSlope,firstResidual,coarseSlope,noise]; ring

theorem fixed_expansion (K : ℝ) :
    digitalSlope age K=99456/1000*K+623562/1000000 ∧
    splitResidual age delay K=107623562/1000000000+99456/1000000*K := by
  constructor <;> dsimp [digitalSlope,firstResidual,coarseSlope,noise,age,splitResidual,delay] <;> ring

theorem old_cube_fails :
    splitResidual age delay radius=282864641/2500000000 ∧
    2*radius<splitResidual age delay radius := by
  norm_num [splitResidual,digitalSlope,firstResidual,coarseSlope,noise,age,delay,radius]

/-- All inflation radii, not only the final support cube. -/
theorem repaired_prefix_budget {K : ℝ} (hK : supportRadius≤K) (hmax : K≤1/16) :
    0≤digitalSlope age K ∧ digitalSlope age K≤8 ∧
    splitResidual age delay K≤2*K ∧ 24*K+93/1000≤2 := by
  have he := fixed_expansion K
  dsimp [supportRadius] at hK
  constructor
  · linarith [he.1]
  constructor
  · linarith [he.1]
  constructor
  · linarith [he.2]
  · linarith

theorem repaired_closed_budget :
    closedResidual age delay supportRadius=282809/2500000 ∧
    closedResidual age delay supportRadius≤residual ∧
    residual<2*supportRadius := by
  norm_num [closedResidual,age,delay,supportRadius,residual,noise]

theorem startup_still_inside {m : State} (hg : ClearancePolicy.Guard m) (i : Fin 3) :
    weight i*ClearancePolicy.policyRadius m<supportRadius := by
  have hh := ClearancePolicy.weighted_inside_old_cube hg i
  norm_num [radius,supportRadius] at *
  linarith

/-- Same weighted target and policy, slower derived entry rate. -/
theorem weighted_face {K r w : ℝ} {z : State}
    (hK : target≤K) (hrlo : 8≤r) (hrhi : r≤12)
    (hw : |w|≤residual) (hz : ∀ i, |z i|≤weight i*K) (i : Fin 3) :
    (z i=weight i*K → transformedRHS r w z i≤-weight i*entryDrift) ∧
    (z i=-weight i*K → weight i*entryDrift≤transformedRHS r w z i) := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hw' := abs_le.mp hw
  norm_num [weight] at h0 h1 h2
  have hK0 : 0≤K := by dsimp [target] at hK; linarith
  fin_cases i
  · norm_num [weight,transformedRHS]
    dsimp [target,entryDrift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    dsimp [target,entryDrift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    have p0 := mul_nonneg (show 0≤r-8 by linarith) (show 0≤z 0+(51/50)*K by linarith)
    have p1 := mul_nonneg (show 0≤r-8 by linarith) (show 0≤(101/100)*K-z 1 by linarith)
    have p2 := mul_nonneg (show 0≤r by linarith) (show 0≤residual-w by linarith)
    have n0 := mul_nonneg (show 0≤r-8 by linarith) (show 0≤(51/50)*K-z 0 by linarith)
    have n1 := mul_nonneg (show 0≤r-8 by linarith) (show 0≤z 1+(101/100)*K by linarith)
    have n2 := mul_nonneg (show 0≤r by linarith) (show 0≤w+residual by linarith)
    have pk := mul_nonneg (show 0≤12-r by linarith) hK0
    dsimp [residual] at p2 n2 hw'
    dsimp [target,entryDrift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> nlinarith

theorem naive_residual_outward :
    0<transformedRHS 12 (115/1000) ![-(51/50)*target,(101/100)*target,target] 2 := by
  norm_num [transformedRHS,target]

theorem old_drift_fails_and_new_tight :
    transformedRHS 12 residual ![-(51/50)*target,(101/100)*target,target] 2 = -entryDrift ∧
    ¬transformedRHS 12 residual ![-(51/50)*target,(101/100)*target,target] 2≤-drift := by
  norm_num [transformedRHS,target,residual,entryDrift,drift]

end LeanControls.TimingBudget
