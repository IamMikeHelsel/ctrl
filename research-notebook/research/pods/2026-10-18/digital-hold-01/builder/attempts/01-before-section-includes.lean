module
public import RobustHold
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
noncomputable section
namespace LeanControls.DigitalHold
open Set Filter
open UncertainLag (State)
open RobustHold

def radius : ℝ := 2221/40000

def clip (u : ℝ) : ℝ := max (-2) (min 2 u)

theorem clip_eq {u : ℝ} (h : |u| ≤ 2) : clip u = u := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  simp [clip, min_eq_right hu, max_eq_right hl]

def rhs (r u d : ℝ) (s : State) : State := ![s 1, s 2, r*(u+d-s 2)]

/-- Both one-sided channels use one continuous physical state. `true` is the
right channel; `false` is the left channel. No derivative of the command or
of the disturbance is assumed. Clipping precedes physical target error. -/
structure Execution (H c : ℝ) (f : ℝ → State)
    (r d stamp : Bool → ℝ → ℝ) (read : Bool → ℝ → State) : Prop where
  continuous : ContinuousOn f (Icc 0 H)
  causal : ∀ b t, t ∈ Icc 0 H → 0 ≤ stamp b t ∧ stamp b t ≤ t ∧ t-stamp b t ≤ 1/1000
  error : ∀ b t, t ∈ Icc 0 H →
    |read b t 0-f (stamp b t) 0| ≤ 1/1000 ∧
    |read b t 1-f (stamp b t) 1| ≤ 1/100 ∧
    |read b t 2-f (stamp b t) 2| ≤ 1/20
  rate : ∀ b t, t ∈ Icc 0 H → 8 ≤ r b t ∧ r b t ≤ 12
  target_error : ∀ b t, t ∈ Icc 0 H → |d b t| ≤ 1/100
  right_ode : ∀ t ∈ Ico 0 H, ∀ i, HasDerivWithinAt (fun s => f s i)
    (rhs (r true t) (clip (command c (read true t))) (d true t) (f t) i) (Ici t) t
  left_ode : ∀ t ∈ Ioc 0 H, ∀ i, HasDerivWithinAt (fun s => f s i)
    (rhs (r false t) (clip (command c (read false t))) (d false t) (f t) i) (Iic t) t

def mismatch (c : ℝ) (f : ℝ → State) (d : Bool → ℝ → ℝ)
    (read : Bool → ℝ → State) (b : Bool) (t : ℝ) : ℝ :=
  clip (command c (read b t)) + d b t - command c (f t)

def slopeRHS (r w : ℝ) (z : State) : ℝ :=
  (4*r-64)*z 0+(160-12*r)*z 1+(12*r-96)*z 2-r*w/2

theorem measurement_cost {c : ℝ} {m s : State}
    (hx : |m 0-s 0| ≤ 1/1000) (hv : |m 1-s 1| ≤ 1/100)
    (ha : |m 2-s 2| ≤ 1/20) : |command c m-command c s| ≤ 93/1000 := by
  obtain ⟨hxl,hxu⟩ := abs_le.mp hx
  obtain ⟨hvl,hvu⟩ := abs_le.mp hv
  obtain ⟨hal,hau⟩ := abs_le.mp ha
  dsimp [command]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem slope_bound {K r w : ℝ} {z : State} (hK : 0 ≤ K)
    (hr : 8 ≤ r ∧ r ≤ 12) (hz : ∀ i, |z i| ≤ K) :
    |slopeRHS r w z| ≤ 96*K+6*|w| := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hw := abs_le.mp (le_refl |w|)
  have p0 := mul_nonneg (show 0 ≤ 64-4*r by linarith [hr.2]) (show 0 ≤ K+z 0 by linarith)
  have n0 := mul_nonneg (show 0 ≤ 64-4*r by linarith [hr.2]) (show 0 ≤ K-z 0 by linarith)
  have p1 := mul_nonneg (show 0 ≤ 160-12*r by linarith [hr.2]) (show 0 ≤ K-z 1 by linarith)
  have n1 := mul_nonneg (show 0 ≤ 160-12*r by linarith [hr.2]) (show 0 ≤ K+z 1 by linarith)
  have p2 := mul_nonneg (show 0 ≤ 12*r-96 by linarith [hr.1]) (show 0 ≤ K-z 2 by linarith)
  have n2 := mul_nonneg (show 0 ≤ 12*r-96 by linarith [hr.1]) (show 0 ≤ K+z 2 by linarith)
  have p3 := mul_nonneg (show 0 ≤ r by linarith [hr.1]) (show 0 ≤ |w|+w by linarith)
  have n3 := mul_nonneg (show 0 ≤ r by linarith [hr.1]) (show 0 ≤ |w|-w by linarith)
  have pk := mul_nonneg (show 0 ≤ r-8 by linarith [hr.1]) hK
  have pw := mul_nonneg (show 0 ≤ 12-r by linarith [hr.2]) (abs_nonneg w)
  dsimp [slopeRHS]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem command_deriv {c t r u d : ℝ} {f : ℝ → State} {S : Set ℝ}
    (hd : ∀ i, HasDerivWithinAt (fun s => f s i) (rhs r u d (f t) i) S t) :
    HasDerivWithinAt (fun s => command c (f s))
      (slopeRHS r (u+d-command c (f t)) (coordinates c (f t))) S t := by
  have hx := hd 0
  have hv := hd 1
  have ha := hd 2
  convert (((hx.sub_const c).const_mul (-8)).sub (hv.const_mul 6)).sub (ha.div_const 2) using 1 <;>
    (try funext s) <;> dsimp [rhs, command, coordinates, slopeRHS] <;> ring

theorem coordinate_deriv {c t r u d : ℝ} {f : ℝ → State} {S : Set ℝ}
    (hd : ∀ i, HasDerivWithinAt (fun s => f s i) (rhs r u d (f t) i) S t) (i : Fin 3) :
    HasDerivWithinAt (fun s => coordinates c (f s) i)
      (transformedRHS r (u+d-command c (f t)) (coordinates c (f t)) i) S t := by
  have hx := hd 0
  have hv := hd 1
  have ha := hd 2
  fin_cases i
  · convert hx.sub_const c using 1 <;> (try funext s) <;> dsimp [rhs, coordinates, transformedRHS] <;> ring
  · convert (hx.sub_const c).add (hv.div_const 4) using 1 <;> (try funext s) <;> dsimp [rhs, coordinates, transformedRHS] <;> ring
  · convert ((hx.sub_const c).add (hv.div_const 2)).add (ha.div_const 16) using 1 <;> (try funext s) <;>
      dsimp [rhs, coordinates, transformedRHS, command] <;> ring

/-- A bound on the right derivative controls every sample-to-current interval.
This allows derivative jumps at every dispatch. -/
theorem age_bound {H s t L : ℝ} {g dg : ℝ → ℝ}
    (hc : ContinuousOn g (Icc 0 H))
    (hd : ∀ x ∈ Ico 0 H, HasDerivWithinAt g (dg x) (Ici x) x)
    (hb : ∀ x ∈ Ico 0 H, |dg x| ≤ L)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ H) : |g t-g s| ≤ L*(t-s) := by
  have sub : Icc s t ⊆ Icc 0 H := Icc_subset_Icc hs ht
  have sub' : Ico s t ⊆ Ico 0 H := fun x hx => ⟨hs.trans hx.1, hx.2.trans_le ht⟩
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_right_le_segment (hc.mono sub)
      (fun x hx => hd x (sub' hx)) (fun x hx => by simpa only [Real.norm_eq_abs] using hb x (sub' hx))
      t ⟨hst,le_rfl⟩

theorem finite_prefix_barrier {ι : Type*} [Finite ι] {H : ℝ} (_hH : 0 ≤ H)
    {y dy : ι → ℝ → ℝ}
    (hc : ∀ i, ContinuousOn (y i) (Icc 0 H))
    (hd : ∀ i t, t ∈ Ioo 0 H → HasDerivWithinAt (y i) (dy i t) (Iic t) t)
    (hi : ∀ i, y i 0 < 0)
    (hin : ∀ t ∈ Ioo 0 H, (∀ u ∈ Icc 0 t, ∀ i, y i u ≤ 0) → ∀ i, y i t = 0 → dy i t < 0) :
    ∀ t ∈ Icc 0 H, ∀ i, y i t ≤ 0 := by
  intro t ht i
  by_contra hbad
  have hpos : 0 < y i t := lt_of_not_ge hbad
  have hct : ContinuousOn (y i) (Icc 0 t) := (hc i).mono (Icc_subset_Icc_right ht.2)
  obtain ⟨s, hs, hys⟩ := intermediate_value_Icc ht.1 hct ⟨(hi i).le, hpos.le⟩
  have hst : s < t := lt_of_le_of_ne hs.2 (by intro he; subst s; linarith)
  let Z : Set ℝ := Icc 0 t ∩ ⋃ j : ι, (y j) ⁻¹' {0}
  have hZclosed : IsClosed Z := by
    have heq : Z = ⋃ j : ι, Icc 0 t ∩ (y j) ⁻¹' {0} := by
      simp only [Z, inter_iUnion]
    rw [heq]
    exact isClosed_iUnion_of_finite fun j => ((hc j).mono (Icc_subset_Icc_right ht.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
  have hsZ : s ∈ Z := ⟨hs, mem_iUnion.mpr ⟨i, hys⟩⟩
  obtain ⟨T, hT, hmin⟩ := hZcompact.exists_isMinOn ⟨s, hsZ⟩ continuousOn_id
  obtain ⟨j, hj⟩ := mem_iUnion.mp hT.2
  change y j T = 0 at hj
  have hTpos : 0 < T := lt_of_le_of_ne hT.1.1 (by intro he; have := hi j; rw [he, hj] at this; linarith)
  have hTt : T < t := lt_of_le_of_lt (hmin hsZ) hst
  have hTint : T ∈ Ioo 0 H := ⟨hTpos, hTt.trans_le ht.2⟩
  have hbefore : ∀ u ∈ Ico 0 T, ∀ k, y k u < 0 := by
    intro u hu k
    by_contra hnot
    have huk : 0 ≤ y k u := le_of_not_gt hnot
    obtain ⟨v, hv, hyv⟩ := intermediate_value_Icc hu.1
      ((hc k).mono (Icc_subset_Icc_right (hu.2.le.trans (hT.1.2.trans ht.2)))) ⟨(hi k).le, huk⟩
    have hvZ : v ∈ Z := ⟨⟨hv.1, hv.2.trans (hu.2.le.trans hT.1.2)⟩, mem_iUnion.mpr ⟨k, hyv⟩⟩
    have hTv : T ≤ v := hmin hvZ
    linarith [hv.2, hu.2]
  have hall : ∀ k, y k T ≤ 0 := by
    intro k
    by_contra hnot
    have hkp : 0 < y k T := lt_of_not_ge hnot
    obtain ⟨v, hv, hyv⟩ := intermediate_value_Icc hTpos.le
      ((hc k).mono (Icc_subset_Icc_right (hT.1.2.trans ht.2))) ⟨(hi k).le, hkp.le⟩
    have hvT : v < T := lt_of_le_of_ne hv.2 (by intro he; subst v; linarith)
    have := hbefore v ⟨hv.1,hvT⟩ k
    linarith
  have hprefix : ∀ u ∈ Icc 0 T, ∀ k, y k u ≤ 0 := by
    intro u hu k
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact (hbefore u ⟨hu.1,hlt⟩ k).le
    · simpa only [heq] using hall k
  have hneg := hin T hTint hprefix j hj
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show T ∉ Iio T by simp)).mp ((hd j T hTint).Iio_of_Iic)
  have hnonneg : 0 ≤ dy j T := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hTpos] with u hu
    rw [slope_def_field, hj]
    exact div_nonneg_of_nonpos (by linarith [hbefore u ⟨hu.1.le,hu.2⟩ j]) (by linarith [hu.2])
  linarith


section Prefix
variable {H c T K : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ}
  {read : Bool → ℝ → State} (ex : Execution H c f r d stamp read)
  (hT : T ≤ H) (hK : 0 ≤ K) (hKmax : K ≤ 1/16)
  (hz : ∀ t ∈ Icc 0 T, ∀ i, |coordinates c (f t) i| ≤ K)

theorem prefix_read_bound (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |command c (read b t)| ≤ 24*K+93/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hb := (cube_physical_bounds (hz (stamp b t) ⟨hs.1,hs.2.1.trans ht.2⟩)).2.2.2
  have hm := measurement_cost he.1 he.2.1 he.2.2
  calc |command c (read b t)| ≤ |command c (read b t)-command c (f (stamp b t))|+
      |command c (f (stamp b t))| := by
        convert abs_add_le (command c (read b t)-command c (f (stamp b t))) (command c (f (stamp b t))) using 1 <;> ring
    _ ≤ 24*K+93/1000 := by linarith

theorem prefix_clip_eq (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    clip (command c (read b t)) = command c (read b t) := by
  apply clip_eq
  have hb := prefix_read_bound ex hT hz b t ht
  linarith

theorem coarse_mismatch (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 48*K+103/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hr := prefix_read_bound ex hT hz b t ht
  have hk := (cube_physical_bounds (hz t ht)).2.2.2
  have hd := ex.target_error b t htH
  dsimp [mismatch]
  rw [prefix_clip_eq ex hT hKmax hz b t ht]
  calc |command c (read b t)+d b t-command c (f t)| ≤
      |command c (read b t)|+|d b t|+|command c (f t)| := (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ 48*K+103/1000 := by linarith

theorem improve_mismatch {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ t ∈ Ico 0 T,
      |slopeRHS (r true t) (mismatch c f d read true t) (coordinates c (f t))| ≤ L)
    (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 103/1000+L/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hm := measurement_cost he.1 he.2.1 he.2.2
  have hc : ContinuousOn (fun t => command c (f t)) (Icc 0 T) := by
    have hh : ∀ i, ContinuousOn (fun t => f t i) (Icc 0 T) := fun i =>
      (continuous_apply i).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hT))
    dsimp [command]; fun_prop
  have hd : ∀ x ∈ Ico 0 T, HasDerivWithinAt (fun t => command c (f t))
      (slopeRHS (r true x) (mismatch c f d read true x) (coordinates c (f x))) (Ici x) x := by
    intro x hx
    exact command_deriv (ex.right_ode x ⟨hx.1,hx.2.trans_le hT⟩)
  have hmove := age_bound hc hd hslope hs.1 hs.2.1 ht.2
  have hage := mul_le_mul_of_nonneg_left hs.2.2 hL
  have hnoise := ex.target_error b t htH
  have htri : |command c (read b t)+d b t-command c (f t)| ≤
      |command c (read b t)-command c (f (stamp b t))|+
      |command c (f t)-command c (f (stamp b t))|+|d b t| := by
    calc _ = |(command c (read b t)-command c (f (stamp b t))) -
        (command c (f t)-command c (f (stamp b t))) + d b t| := by congr 1; ring
      _ ≤ |(command c (read b t)-command c (f (stamp b t))) -
        (command c (f t)-command c (f (stamp b t)))|+|d b t| := abs_add_le _ _
      _ ≤ _ := add_le_add_right (abs_sub _ _) _
  dsimp [mismatch]
  rw [prefix_clip_eq ex hT hKmax hz b t ht]
  linarith

/-- Two finite refinements. The only trajectory enclosure premise is the cube
on a prefix. There is no aggregate mismatch premise. -/
theorem prefix_mismatch (hKR : radius ≤ K) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 103621708/1000000000 + 98304/1000000*K := by
  have hsl0 : ∀ x ∈ Ico 0 T,
      |slopeRHS (r true x) (mismatch c f d read true x) (coordinates c (f x))| ≤ 384*K+618/1000 := by
    intro x hx
    have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
    have hh := slope_bound hK (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
    have hw := coarse_mismatch ex hT hKmax hz true x hxc
    linarith
  have hw0 := improve_mismatch ex hT hKmax hz (by positivity : 0 ≤ 384*K+618/1000) hsl0
  have hsl1 : ∀ x ∈ Ico 0 T,
      |slopeRHS (r true x) (mismatch c f d read true x) (coordinates c (f x))| ≤
        96*K+6*(103/1000+(384*K+618/1000)/1000) := by
    intro x hx
    have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
    have hh := slope_bound hK (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
    have hw := hw0 true x hxc
    linarith
  have hw1 := improve_mismatch ex hT hKmax hz (by positivity :
      0 ≤ 96*K+6*(103/1000+(384*K+618/1000)/1000)) hsl1 b t ht
  linarith

theorem prefix_budget (hKR : radius ≤ K) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 2*K := by
  have hh := prefix_mismatch ex hT hK hKmax hz hKR b t ht
  norm_num [radius] at hKR
  linarith
end Prefix
