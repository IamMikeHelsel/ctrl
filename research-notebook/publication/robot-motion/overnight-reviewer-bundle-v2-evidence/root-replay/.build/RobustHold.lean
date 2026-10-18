module
public import ComparisonEnvelope
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.RobustHold
open Set Filter
open UncertainLag (State)
open VariableResponse

/-- A finite collection of strict inward barriers cannot acquire a positive
value. The proof uses a first contact and its left derivative. -/
theorem finite_barrier {ι : Type*} [Finite ι] {H : ℝ} (_hH : 0 ≤ H)
    {y dy : ι → ℝ → ℝ}
    (hc : ∀ i, ContinuousOn (y i) (Icc 0 H))
    (hd : ∀ i t, t ∈ Ioo 0 H → HasDerivAt (y i) (dy i t) t)
    (hi : ∀ i, y i 0 < 0)
    (hin : ∀ t ∈ Ioo 0 H, (∀ i, y i t ≤ 0) → ∀ i, y i t = 0 → dy i t < 0) :
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
  have hneg := hin T hTint hall j hj
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp (hd j T hTint)).1
  have hnonneg : 0 ≤ dy j T := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hTpos] with u hu
    rw [slope_def_field, hj]
    exact div_nonneg_of_nonpos (by linarith [hbefore u ⟨hu.1.le,hu.2⟩ j]) (by linarith [hu.2])
  linarith

/-- Coordinates chosen to expose a robust invariant cube. -/
def coordinates (c : ℝ) (s : State) : State :=
  ![s 0 - c, s 0 - c + s 1 / 4, s 0 - c + s 1 / 2 + s 2 / 16]

/-- Continuous-state holding feedback; w is added to this acceleration target. -/
def command (c : ℝ) (s : State) : ℝ := -8 * (s 0 - c) - 6 * s 1 - s 2 / 2

def transformedRHS (r w : ℝ) (z : State) : State :=
  ![4 * (-z 0 + z 1), 4 * (-z 1 + z 2),
    4 * ((1-r/8)*z 0 + 3*(r/8-1)*z 1 + (2-3*r/8)*z 2) + r/16*w]

/-- The invariant-coordinate ODE follows from the physical position, velocity,
and lagged-acceleration ODE. It is not an extra dynamical assumption. -/
theorem coordinates_ode {H c : ℝ} {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => command c (f t) + w t) f)
    (t : ℝ) (ht : t ∈ Ioo 0 H) (i : Fin 3) :
    HasDerivAt (fun s => coordinates c (f s) i)
      (transformedRHS (r t) (w t) (coordinates c (f t)) i) t := by
  have hx := hf.ode t ht 0
  have hv := hf.ode t ht 1
  have ha := hf.ode t ht 2
  change HasDerivAt (fun s => f s 0) (f t 1) t at hx
  change HasDerivAt (fun s => f s 1) (f t 2) t at hv
  change HasDerivAt (fun s => f s 2) (r t * (command c (f t) + w t - f t 2)) t at ha
  fin_cases i
  · convert hx.sub_const c using 1 <;> (try funext s) <;> dsimp [coordinates, transformedRHS] <;> ring
  · convert (hx.sub_const c).add (hv.div_const 4) using 1 <;> (try funext s) <;> dsimp [coordinates, transformedRHS] <;> ring
  · convert ((hx.sub_const c).add (hv.div_const 2)).add (ha.div_const 16) using 1 <;> (try funext s) <;>
      dsimp [coordinates, transformedRHS, command] <;> ring

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

/-- Arbitrary finite-horizon cube invariance. Radius zero is included. The
expanding barriers make first contact strict, then their expansion tends to zero. -/
theorem transformed_cube_invariant {H R : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {z : ℝ → State}
    (hc : ∀ i, ContinuousOn (fun t => z t i) (Icc 0 H))
    (hd : ∀ i t, t ∈ Ioo 0 H → HasDerivAt (fun s => z s i)
      (transformedRHS (r t) (w t) (z t) i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 2*R)
    (hi : ∀ i, |z 0 i| ≤ R) :
    ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ R := by
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ R + ε*(1+t) := by
    let K : ℝ → ℝ := fun t => R + ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1) - K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r t) (w t) (z t) p.1
       else -transformedRHS (r t) (w t) (z t) p.1) - ε
    have hKc : Continuous K := by dsimp [K]; fun_prop
    have hKd (t : ℝ) : HasDerivAt K ε t := by
      convert (((hasDerivAt_id t).const_add 1).const_mul ε).const_add R using 1 <;> simp [K]
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivAt (y p) (dy p t) t := by
      obtain ⟨i,b⟩ := p
      cases b
      · exact (hd i t ht).neg.sub (hKd t)
      · exact (hd i t ht).sub (hKd t)
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      cases b <;> dsimp [y,K] <;> linarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H) (hall : ∀ p, y p t ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hKR : R ≤ K t := by dsimp [K]; nlinarith [ht.1]
      have hzt (i : Fin 3) : |z t i| ≤ K t := by
        have hp := hall (i,true)
        have hn := hall (i,false)
        dsimp [y] at hp hn
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      obtain ⟨i,b⟩ := p
      have hface := cube_face hR hKR (hrlo t htc) (hrhi t htc) (hw t htc) hzt i
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
    have hbar := finite_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,K] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hdpos : 0 < 1+t := by linarith [ht.1]
  have heq : ε/(1+t)*(1+t) = ε := div_mul_cancel₀ ε (ne_of_gt hdpos)
  simpa only [heq] using inflated (ε/(1+t)) (div_pos hε hdpos) t ht i

/-- Every actual trajectory under this holding feedback remains in the cube.
No continuity or derivative bound on r or w is needed beyond existence of the
stated classical trajectory and their pointwise bounds. -/
theorem actual_hold_invariant {H R c : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => command c (f t) + w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 2*R)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ R := by
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc (i : Fin 3) : ContinuousOn (fun t => coordinates c (f t) i) (Icc 0 H) := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop
  exact transformed_cube_invariant hH hR hc
    (fun i t ht => coordinates_ode hf t ht i) hrlo hrhi hw hi

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

/-- Actual holding preserves the position tube and command authority bound. -/
theorem actual_hold_bounds {H R c : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => command c (f t) + w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 2*R)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H, |f t 0 - c| ≤ R ∧ |command c (f t)| ≤ 24*R ∧
      |command c (f t) + w t| ≤ 26*R := by
  intro t ht
  have hb := cube_physical_bounds (actual_hold_invariant hH hR hf hrlo hrhi hw hi t ht)
  refine ⟨hb.1,hb.2.2.2,?_⟩
  calc |command c (f t)+w t| ≤ |command c (f t)|+|w t| := abs_add_le _ _
    _ ≤ 24*R+2*R := add_le_add hb.2.2.2 (hw t ht)
    _ = 26*R := by ring

/-- A real zero-velocity braking state fits a tube whose front edge equals its
current position, if residual acceleration is nonpositive and bounded. -/
theorem zero_velocity_capture {R c : ℝ} {s : State} (hR : 0 ≤ R)
    (hx : s 0 = c+R) (hv : s 1 = 0) (ha : -32*R ≤ s 2 ∧ s 2 ≤ 0) :
    ∀ i, |coordinates c s i| ≤ R := by
  intro i
  fin_cases i <;> dsimp [coordinates] <;> simp only [hx,hv] <;>
    apply abs_le.mpr <;> constructor <;> linarith

/-- The equilibrium trajectory makes the holding assumptions nonvacuous for
any actuator-rate signal and any reference position. -/
theorem equilibrium_isTrajectory (H c : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r (fun t => command c (![c,0,0]) + (0:ℝ)) (fun _ => ![c,0,0]) := by
  constructor
  · exact continuousOn_const
  · intro t ht i
    convert hasDerivAt_const t (![c,0,0] i) using 1 <;>
      fin_cases i <;> norm_num [command]

end LeanControls.RobustHold
#print axioms LeanControls.RobustHold.finite_barrier
#print axioms LeanControls.RobustHold.coordinates_ode
#print axioms LeanControls.RobustHold.cube_face
#print axioms LeanControls.RobustHold.transformed_cube_invariant
#print axioms LeanControls.RobustHold.actual_hold_invariant
#print axioms LeanControls.RobustHold.cube_physical_bounds
#print axioms LeanControls.RobustHold.actual_hold_bounds
#print axioms LeanControls.RobustHold.zero_velocity_capture
#print axioms LeanControls.RobustHold.equilibrium_isTrajectory
