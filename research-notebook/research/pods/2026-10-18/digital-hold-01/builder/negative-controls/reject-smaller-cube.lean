module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
noncomputable section
namespace LeanControls.DigitalHold
open Set Filter
abbrev State := Fin 3 → ℝ

/- The following coordinate definitions, face lemma and physical-coordinate
bound are copied from the frozen RobustHold.lean input, with no mathematical
change. This self-contained module does not import that module's classical
trajectory theorem or any cached local proof artifact. -/
/-- Coordinates chosen to expose a robust invariant cube. -/
def coordinates (c : ℝ) (s : State) : State :=
  ![s 0 - c, s 0 - c + s 1 / 4, s 0 - c + s 1 / 2 + s 2 / 16]

/-- Continuous-state holding feedback; w is added to this acceleration target. -/
def command (c : ℝ) (s : State) : ℝ := -8 * (s 0 - c) - 6 * s 1 - s 2 / 2

def transformedRHS (r w : ℝ) (z : State) : State :=
  ![4 * (-z 0 + z 1), 4 * (-z 1 + z 2),
    4 * ((1-r/8)*z 0 + 3*(r/8-1)*z 1 + (2-3*r/8)*z 2) + r/16*w]

/-- At any face of any larger cube, the vector field points inward. -/
theorem cube_face {R K r w : ℝ} {z : State}
    (hR : 0 ≤ R) (hKR : R ≤ K) (hrlo : 8 ≤ r) (hrhi : r ≤ 12)
    (hw : |w| ≤ 2*R) (hz : ∀ i, |z i| ≤ K) (i : Fin 3) :
    (z i = K → transformedRHS r w z i ≤ 0) ∧
    (z i = -K → 0 ≤ transformedRHS r w z i) := by
  have hK : 0 ≤ K := hR.trans hKR
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hw' := abs_le.mp hw
  fin_cases i
  · dsimp [transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · dsimp [transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · dsimp [transformedRHS]
    have p0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 0+K by linarith)
    have p1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ K-z 1 by linarith)
    have p2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ 2*R-w by linarith)
    have p3 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ K-R by linarith)
    have p4 := mul_nonneg (show 0 ≤ 12-r by linarith) hK
    have n0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ K-z 0 by linarith)
    have n1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 1+K by linarith)
    have n2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ w+2*R by linarith)
    constructor <;> intro he <;> rw [he] <;> nlinarith

/-- The cube gives a position tube and finite velocity, acceleration, and
command bounds in the original coordinates. -/
theorem cube_physical_bounds {R c : ℝ} {s : State}
    (hz : ∀ i, |coordinates c s i| ≤ R) :
    |s 0 - c| ≤ R ∧ |s 1| ≤ 8*R ∧ |s 2| ≤ 64*R ∧ |command c s| ≤ 24*R := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  dsimp [coordinates] at h0 h1 h2
  dsimp [command]
  exact ⟨abs_le.mpr h0, abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩, abs_le.mpr ⟨by linarith,by linarith⟩⟩


def radius : ℝ := 1/20

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

include ex hT hz
theorem prefix_read_bound (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |command c (read b t)| ≤ 24*K+93/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hb := (cube_physical_bounds (hz (stamp b t) ⟨hs.1,hs.2.1.trans ht.2⟩)).2.2.2
  have hm := measurement_cost (c := c) he.1 he.2.1 he.2.2
  calc |command c (read b t)| ≤ |command c (read b t)-command c (f (stamp b t))|+
      |command c (f (stamp b t))| := by
        simpa only [sub_add_cancel] using abs_add_le (command c (read b t)-command c (f (stamp b t))) (command c (f (stamp b t)))
    _ ≤ 24*K+93/1000 := by linarith

include hKmax
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
      |command c (read b t)|+|d b t|+|command c (f t)| := by
        have h1 := abs_sub (command c (read b t)+d b t) (command c (f t))
        have h2 := abs_add_le (command c (read b t)) (d b t)
        linarith
    _ ≤ 48*K+103/1000 := by linarith

theorem improve_mismatch {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ t ∈ Ico 0 T,
      |slopeRHS (r true t) (mismatch c f d read true t) (coordinates c (f t))| ≤ L)
    (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 103/1000+L/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hm := measurement_cost (c := c) he.1 he.2.1 he.2.2
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
      _ ≤ _ := by
        have hh := abs_sub (command c (read b t)-command c (f (stamp b t))) (command c (f t)-command c (f (stamp b t)))
        linarith
  dsimp [mismatch]
  rw [prefix_clip_eq ex hT hKmax hz b t ht]
  linarith

include hK
/-- Two finite refinements. The only trajectory enclosure premise is the cube
on a prefix. There is no aggregate mismatch premise. -/
theorem prefix_mismatch (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 103621708/1000000000 + 98304/1000000*K := by
  have hsl0 : ∀ x ∈ Ico 0 T,
      |slopeRHS (r true x) (mismatch c f d read true x) (coordinates c (f x))| ≤ 384*K+618/1000 := by
    intro x hx
    have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
    have hh := slope_bound (w := mismatch c f d read true x) hK (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
    have hw := coarse_mismatch ex hT hKmax hz true x hxc
    linarith
  have hw0 := improve_mismatch ex hT hKmax hz (by positivity : 0 ≤ 384*K+618/1000) hsl0
  have hsl1 : ∀ x ∈ Ico 0 T,
      |slopeRHS (r true x) (mismatch c f d read true x) (coordinates c (f x))| ≤
        96*K+6*(103/1000+(384*K+618/1000)/1000) := by
    intro x hx
    have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
    have hh := slope_bound (w := mismatch c f d read true x) hK (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
    have hw := hw0 true x hxc
    linarith
  have hw1 := improve_mismatch ex hT hKmax hz (by positivity :
      0 ≤ 96*K+6*(103/1000+(384*K+618/1000)/1000)) hsl1 b t ht
  linarith

theorem prefix_budget (hKR : radius ≤ K) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch c f d read b t| ≤ 2*K := by
  have hh := prefix_mismatch ex hT hK hKmax hz b t ht
  norm_num [radius] at hKR
  linarith
end Prefix

/-- Noncircular cube preservation for every supplied execution. The proof
bounds only the strict first-contact prefix, derives its mismatch bound in two
finite passes, and then rules out that contact. Existence is not concluded. -/
theorem digital_invariant {H c : ℝ} (hH : 0 ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ radius := by
  let z := fun t => coordinates c (f t)
  have hradius : 0 ≤ radius := by norm_num [radius]
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) (hsmall : ε*(1+H) ≤ 1/16-radius) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ radius+ε*(1+t) := by
    let K := fun t : ℝ => radius+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t) (mismatch c f d read false t) (z t) p.1
       else -transformedRHS (r false t) (mismatch c f d read false t) (z t) p.1)-ε
    have hKc : Continuous K := by dsimp [K]; fun_prop
    have hKd (t : ℝ) : HasDerivAt K ε t := by
      convert (((hasDerivAt_id t).const_add 1).const_mul ε).const_add radius using 1 <;> simp [K]
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := c) (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub (hKd t).hasDerivWithinAt
      · exact hd.sub (hKd t).hasDerivWithinAt
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      cases b <;> dsimp [y,K,z] <;> linarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hKR : radius ≤ K t := by dsimp [K]; nlinarith [ht.1]
      have hKpos : 0 ≤ K t := hradius.trans hKR
      have hKmax : K t ≤ 1/16 := by dsimp [K]; nlinarith [ht.2]
      have hzt (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin 3) : |z u i| ≤ K t := by
        have hp := hall u hu (i,true)
        have hn := hall u hu (i,false)
        dsimp [y,K] at hp hn ⊢
        exact abs_le.mpr ⟨by nlinarith [hu.2],by nlinarith [hu.2]⟩
      have hw := prefix_budget ex ht.2.le hKpos hKmax hzt hKR false t ⟨ht.1.le,le_rfl⟩
      obtain ⟨i,b⟩ := p
      have hface := cube_face hKpos le_rfl (ex.rate false t htc).1 (ex.rate false t htc).2 hw
        (hzt t ⟨ht.1.le,le_rfl⟩) i
      cases b
      · dsimp [y] at he
        have hzi : z t i = -K t := by linarith
        have hh := hface.2 hzi
        dsimp [dy]
        linarith
      · dsimp [y] at he
        have hzi : z t i = K t := by linarith
        have hh := hface.1 hzi
        dsimp [dy]
        linarith
    have hbar := finite_prefix_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,K] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < 1+H := by linarith
  let δ := min (ε/(1+H)) ((1/16-radius)/(1+H))
  have hδ : 0 < δ := lt_min (div_pos hε hden) (div_pos (by norm_num [radius]) hden)
  have hδ1 : δ*(1+H) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hδ2 : δ*(1+H) ≤ 1/16-radius := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hh := inflated δ hδ hδ2 t ht i
  change |z t i| ≤ radius+ε
  nlinarith [ht.2]

/-- Safety and authority consequences use the same physical state, including
at updates. The target error is outside command clipping. -/
theorem digital_bounds {H c : ℝ} (hH : 0 ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    ∀ t ∈ Icc 0 H, |f t 0-c| ≤ radius ∧ |f t 1| ≤ 8*radius ∧ |f t 2| ≤ 64*radius ∧
      ∀ b, |command c (read b t)| ≤ 891/625 ∧
        clip (command c (read b t)) = command c (read b t) ∧
        |clip (command c (read b t))+d b t| ≤ 3589/2500 := by
  have hz := digital_invariant hH ex hi
  intro t ht
  have hp := cube_physical_bounds (hz t ht)
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  intro b
  have hb := prefix_read_bound ex le_rfl hz b t ht
  have hc := prefix_clip_eq ex le_rfl (by norm_num [radius] : radius ≤ 1/16) hz b t ht
  have hd := ex.target_error b t ht
  refine ⟨by norm_num [radius] at hb; exact hb,hc,?_⟩
  rw [hc]
  have hh := abs_add_le (command c (read b t)) (d b t)
  norm_num [radius] at hb
  linarith

/-- Dispatches are strictly ordered. Indices select one held reading on each
side of an update; no physical state is reset. -/
structure Schedule where
  sample : ℕ → ℝ
  dispatch : ℕ → ℝ
  measurement : ℕ → State
  index : Bool → ℝ → ℕ

structure IsSchedule (H : ℝ) (q : Schedule) (stamp : Bool → ℝ → ℝ)
    (read : Bool → ℝ → State) : Prop where
  first_dispatch : q.dispatch 0 = 0
  first_sample : q.sample 0 = 0
  first_index : ∀ b, q.index b 0 = 0
  sample_order : ∀ n, 0 ≤ q.sample n ∧ q.sample n ≤ q.dispatch n
  dispatch_order : StrictMono q.dispatch
  locally_finite : ∀ T : ℝ, Set.Finite {n | q.dispatch n ≤ T}
  right_cell : ∀ t ∈ Ico 0 H,
    q.dispatch (q.index true t) ≤ t ∧ t < q.dispatch (q.index true t+1)
  left_cell : ∀ t ∈ Ioc 0 H,
    q.dispatch (q.index false t) < t ∧ t ≤ q.dispatch (q.index false t+1)
  timestamp : ∀ b t, t ∈ Icc 0 H → stamp b t = q.sample (q.index b t)
  held_reading : ∀ b t, t ∈ Icc 0 H → read b t = q.measurement (q.index b t)


/-- The schedule conditions imply that each reading and its timestamp really
are held on the half-open dispatch cell. -/
theorem right_held_reading {H t : ℝ} {q : Schedule}
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H q stamp read) (ht : t ∈ Ico 0 H) (n : ℕ)
    (hn : q.dispatch n ≤ t ∧ t < q.dispatch (n+1)) :
    stamp true t = q.sample n ∧ read true t = q.measurement n := by
  have hi := hs.right_cell t ht
  have heq : q.index true t = n := by
    rcases lt_trichotomy (q.index true t) n with hlt | heq | hgt
    · have hh := hs.dispatch_order.monotone (show q.index true t+1 ≤ n by omega)
      linarith [hi.2,hn.1]
    · exact heq
    · have hh := hs.dispatch_order.monotone (show n+1 ≤ q.index true t by omega)
      linarith [hi.1,hn.2]
  have htc : t ∈ Icc 0 H := ⟨ht.1,ht.2.le⟩
  exact ⟨by rw [hs.timestamp true t htc,heq], by rw [hs.held_reading true t htc,heq]⟩

/-- The left derivative at dispatch n+1 uses command n. -/
theorem left_held_reading {H t : ℝ} {q : Schedule}
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H q stamp read) (ht : t ∈ Ioc 0 H) (n : ℕ)
    (hn : q.dispatch n < t ∧ t ≤ q.dispatch (n+1)) :
    stamp false t = q.sample n ∧ read false t = q.measurement n := by
  have hi := hs.left_cell t ht
  have heq : q.index false t = n := by
    rcases lt_trichotomy (q.index false t) n with hlt | heq | hgt
    · have hh := hs.dispatch_order.monotone (show q.index false t+1 ≤ n by omega)
      linarith [hi.2,hn.1]
    · exact heq
    · have hh := hs.dispatch_order.monotone (show n+1 ≤ q.index false t by omega)
      linarith [hi.1,hn.2]
  have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2⟩
  exact ⟨by rw [hs.timestamp false t htc,heq], by rw [hs.held_reading false t htc,heq]⟩

def IsSampledExecution (H c : ℝ) (f : ℝ → State)
    (r d stamp : Bool → ℝ → ℝ) (read : Bool → ℝ → State) (q : Schedule) : Prop :=
  Execution H c f r d stamp read ∧ IsSchedule H q stamp read

theorem first_command_fresh {H : ℝ} (hH : 0 ≤ H) {q : Schedule}
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H q stamp read) (b : Bool) :
    stamp b 0 = 0 ∧ read b 0 = q.measurement 0 := by
  have ht : (0:ℝ) ∈ Icc 0 H := ⟨le_rfl,hH⟩
  constructor
  · rw [hs.timestamp b 0 ht,hs.first_index,hs.first_sample]
  · rw [hs.held_reading b 0 ht,hs.first_index]

/-- Fixed 1 ms total-age digital hold theorem. It quantifies over the actual
sampled execution and proves the cube for every real time in the horizon. -/
theorem sampled_hold {H c : ℝ} (hH : 0 ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (hx : IsSampledExecution H c f r d stamp read q)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    (∀ b, stamp b 0 = 0 ∧ read b 0 = q.measurement 0) ∧
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc 0 H, |f t 0-c| ≤ radius ∧ |f t 1| ≤ 8*radius ∧ |f t 2| ≤ 64*radius ∧
      ∀ b, |command c (read b t)| ≤ 891/625 ∧
        clip (command c (read b t)) = command c (read b t) ∧
        |clip (command c (read b t))+d b t| ≤ 3589/2500) := by
  exact ⟨fun b => first_command_fresh hH hx.2 b,digital_invariant hH hx.1 hi,digital_bounds hH hx.1 hi⟩

/-- A concrete supplied execution exists; this is not a general initial-value
existence or uniqueness theorem. -/
theorem equilibrium_execution {H : ℝ} (hH : H ≤ 1/1000) (c : ℝ) :
    Execution H c (fun _ => ![c,0,0]) (fun _ _ => 8) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => ![c,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro b t ht
    exact ⟨le_rfl,ht.1,by linarith [ht.2]⟩
  · intro b t ht
    norm_num
  · intro b t ht
    norm_num
  · intro b t ht
    norm_num
  · intro t ht i
    convert (hasDerivAt_const t (![c,0,0] i)).hasDerivWithinAt using 1 <;>
      fin_cases i <;> norm_num [rhs,command,clip]
  · intro t ht i
    convert (hasDerivAt_const t (![c,0,0] i)).hasDerivWithinAt using 1 <;>
      fin_cases i <;> norm_num [rhs,command,clip]

def singleCellSchedule (c : ℝ) : Schedule where
  sample n := n/1000
  dispatch n := n/1000
  measurement _ := ![c,0,0]
  index _ _ := 0

theorem single_cell_schedule (c : ℝ) :
    IsSchedule (1/1000) (singleCellSchedule c) (fun _ _ => 0) (fun _ _ => ![c,0,0]) := by
  constructor
  · norm_num [singleCellSchedule]
  · norm_num [singleCellSchedule]
  · intro b; rfl
  · intro n; dsimp [singleCellSchedule]; exact ⟨by positivity,le_rfl⟩
  · intro m n hmn
    dsimp [singleCellSchedule]
    exact div_lt_div_of_pos_right (by exact_mod_cast hmn) (by norm_num)
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (1000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change (n:ℝ)/1000 ≤ T at hn
    change n < N
    have hh : (n:ℝ) < N := by linarith
    exact_mod_cast hh
  · intro t ht; simpa [singleCellSchedule] using ht
  · intro t ht; simpa [singleCellSchedule] using ht
  · intro b t ht; norm_num [singleCellSchedule]
  · intro b t ht; rfl

theorem sampled_nonempty (c : ℝ) :
    IsSampledExecution (1/1000) c (fun _ => ![c,0,0]) (fun _ _ => 8)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => ![c,0,0]) (singleCellSchedule c) ∧
    (∀ i, |coordinates c (![c,0,0]) i| ≤ radius) := by
  refine ⟨⟨equilibrium_execution le_rfl c,single_cell_schedule c⟩,?_⟩
  intro i
  fin_cases i <;> norm_num [coordinates,radius]

end LeanControls.DigitalHold
