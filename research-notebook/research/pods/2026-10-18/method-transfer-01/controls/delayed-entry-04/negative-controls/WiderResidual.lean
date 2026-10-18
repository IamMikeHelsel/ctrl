module
public import AdaptiveAdmission
public import WeightedEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.DelayedEntry
open Set Filter DigitalHold WeightedEntry

def residual : ℝ := 3/25
def envelope (D t : ℝ) : ℝ := max target (radius-drift*(t-D))

theorem envelope_startup {D t : ℝ} (ht : t ≤ D) : radius ≤ envelope D t := by
  have hh : radius-drift*(t-D) ≤ envelope D t := le_max_right _ _
  dsimp [drift] at hh
  linarith

theorem envelope_before {D t : ℝ} (ht : t ≤ D+entryTime) :
    envelope D t = radius-drift*(t-D) := by
  apply max_eq_right
  dsimp [entryTime,drift,target,radius] at ht ⊢
  linarith

theorem envelope_plateau {D t : ℝ} (ht : D+entryTime ≤ t) : envelope D t = target := by
  apply max_eq_left
  dsimp [entryTime,drift,target,radius] at ht ⊢
  linarith

/-- The derivative at the plateau kink is the incoming left derivative.
This changes the analytic envelope only; no physical timestamp is shifted. -/
theorem envelope_left_deriv (D t : ℝ) :
    HasDerivWithinAt (envelope D) (if t ≤ D+entryTime then -drift else 0) (Iic t) t := by
  by_cases ht : t ≤ D+entryTime
  · rw [if_pos ht]
    have hd : HasDerivAt (fun u : ℝ => radius-drift*(u-D)) (-drift) t := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id t).sub_const D).const_mul drift).const_sub radius
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventually_mem_nhdsWithin] with u hu
      change u ≤ t at hu
      exact envelope_before (hu.trans ht)
    · exact envelope_before ht
  · rw [if_neg ht]
    have hd : HasDerivAt (envelope D) 0 t := by
      apply (hasDerivAt_const t target).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge ht)] with u hu
      exact envelope_plateau hu.le
    exact hd.hasDerivWithinAt

/-- All radii K>=.045, with the actual larger mixed-history residual .111. -/
theorem weighted_face {K r w : ℝ} {z : State}
    (hK : target ≤ K) (hrlo : 8 ≤ r) (hrhi : r ≤ 12)
    (hw : |w| ≤ residual) (hz : ∀ i, |z i| ≤ weight i*K) (i : Fin 3) :
    (z i = weight i*K → transformedRHS r w z i ≤ -weight i*drift) ∧
    (z i = -weight i*K → weight i*drift ≤ transformedRHS r w z i) := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hw' := abs_le.mp hw
  norm_num [weight] at h0 h1 h2
  have hK0 : 0 ≤ K := by dsimp [target] at hK; linarith
  fin_cases i
  · norm_num [weight,transformedRHS]
    dsimp [target,drift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    dsimp [target,drift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    have p0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 0+(51/50)*K by linarith)
    have p1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ (101/100)*K-z 1 by linarith)
    have p2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ residual-w by linarith)
    have n0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ (51/50)*K-z 0 by linarith)
    have n1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 1+(101/100)*K by linarith)
    have n2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ w+residual by linarith)
    have pk := mul_nonneg (show 0 ≤ 12-r by linarith) hK0
    dsimp [residual] at p2 n2 hw'
    dsimp [target,drift] at hK ⊢
    constructor <;> intro he <;> rw [he] <;> nlinarith

/-- First use the accepted delayed invariant; then recover the exact .111
residual from its actual whole-history slope. This is a conclusion, not a
new residual or invariant premise. -/
theorem derived_history_residual {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ AdaptiveAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : AdaptiveAdmission.Execution H D m f r d stamp read)
    (hi : AdaptiveAdmission.Admitted m f) :
    ∀ b t, t ∈ Icc 0 H → |mismatch (AdaptiveAdmission.center m) f d read b t| ≤ residual := by
  have hR : 0 ≤ radius := by norm_num [radius]
  have hRmax : radius ≤ 1/16 := by norm_num [radius]
  have hz := AdaptiveAdmission.delayed_invariant (hD.trans hDH) hD hDH hlim ex hi
  have hw := AdaptiveAdmission.prefix_budget ex (T := H) (K := radius)
    le_rfl hR hRmax hz le_rfl hD hDH hi hlim
  have hsl : ∀ x ∈ Ico 0 H, |AdaptiveAdmission.actualSlope D m f r d read true x| ≤ 8 := by
    intro x hx
    by_cases hb : x < D
    · exact AdaptiveAdmission.startup_actual_slope ex hD hDH hi hlim x ⟨hx.1,hb⟩
    · have hxc : x ∈ Icc 0 H := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch (AdaptiveAdmission.center m) f d read true x)
        hR (ex.rate true x hxc) (hz x hxc)
      have hmx := hw true x hxc
      have he : AdaptiveAdmission.actualSlope D m f r d read true x =
          slopeRHS (r true x) (mismatch (AdaptiveAdmission.center m) f d read true x)
            (coordinates (AdaptiveAdmission.center m) (f x)) := by
        simp [AdaptiveAdmission.actualSlope,AdaptiveAdmission.actualMismatch,
          AdaptiveAdmission.actualCommand,mismatch,hb]
      rw [he]
      norm_num [radius] at hh hmx
      linarith
  intro b t ht
  have hh := AdaptiveAdmission.improve_mismatch ex (T := H) (K := radius)
    le_rfl hRmax hz (by norm_num : (0:ℝ) ≤ 8) hsl b t ht
  convert hh using 1 <;> norm_num [residual]

/-- The moving-box argument stays on [0,H]. Contact at or before D is
excluded by the proved cube and the envelope. Only strictly after D is the
incoming command rewritten as digital feedback. -/
theorem delayed_shrinking_box {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ AdaptiveAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : AdaptiveAdmission.Execution H D m f r d stamp read)
    (hi : AdaptiveAdmission.Admitted m f) :
    ∀ t ∈ Icc 0 H, ∀ i,
      |coordinates (AdaptiveAdmission.center m) (f t) i| ≤ weight i*envelope D t := by
  let z := fun t => coordinates (AdaptiveAdmission.center m) (f t)
  have hH := hD.trans hDH
  have hz := AdaptiveAdmission.delayed_invariant hH hD hDH hlim ex hi
  have hw := derived_history_residual hD hDH hlim ex hi
  have hR : 0 ≤ radius := by norm_num [radius]
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ weight i*(envelope D t+ε*(1+t)) := by
    let K := fun t => envelope D t+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-weight p.1*K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t)
        (AdaptiveAdmission.actualMismatch D m f d read false t) (z t) p.1
       else -transformedRHS (r false t)
        (AdaptiveAdmission.actualMismatch D m f d read false t) (z t) p.1)-
      weight p.1*((if t ≤ D+entryTime then -drift else 0)+ε)
    have hKc : Continuous K := by dsimp [K,envelope]; fun_prop
    have hKd (t : ℝ) : HasDerivWithinAt K
        ((if t ≤ D+entryTime then -drift else 0)+ε) (Iic t) t := by
      have he : HasDerivWithinAt (fun u : ℝ => ε*(1+u)) ε (Iic t) t := by
        simpa only [id_eq,mul_one] using
          ((((hasDerivAt_id t).const_add 1).const_mul ε).hasDerivWithinAt (s := Iic t))
      exact (envelope_left_deriv D t).add he
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := AdaptiveAdmission.center m)
        (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub ((hKd t).const_mul (weight i))
      · exact hd.sub ((hKd t).const_mul (weight i))
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hz 0 ⟨le_rfl,hH⟩ i)
      have he := envelope_startup hD
      have hwi := weight_pos i
      have hp := mul_nonneg (sub_nonneg.mpr (weight_ge_one i))
        (show 0 ≤ envelope D 0 by linarith)
      cases b <;> dsimp [y,K,z] <;> nlinarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      by_cases hpre : t ≤ D
      · have hs := abs_le.mp (hz t htc p.1)
        have henv := envelope_startup hpre
        have hKt : radius < K t := by dsimp [K]; nlinarith [ht.1]
        have hK0 : 0 ≤ K t := le_trans hR hKt.le
        have hp := mul_nonneg (sub_nonneg.mpr (weight_ge_one p.1)) hK0
        obtain ⟨i,b⟩ := p
        cases b <;> dsimp [y,z] at he <;> dsimp at hs hp <;>
          exfalso <;> nlinarith
      have heff : AdaptiveAdmission.actualMismatch D m f d read false t =
          mismatch (AdaptiveAdmission.center m) f d read false t := by
        simp [AdaptiveAdmission.actualMismatch,AdaptiveAdmission.actualCommand,mismatch,hpre]
      have hKt : target ≤ K t := by
        have hm : target ≤ envelope D t := le_max_left _ _
        dsimp [K]
        nlinarith [ht.1]
      have hzt (i : Fin 3) : |z t i| ≤ weight i*K t := by
        have hp := hall t ⟨ht.1.le,le_rfl⟩ (i,true)
        have hn := hall t ⟨ht.1.le,le_rfl⟩ (i,false)
        dsimp [y] at hp hn
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      obtain ⟨i,b⟩ := p
      have hface := weighted_face hKt (ex.rate false t htc).1 (ex.rate false t htc).2
        (hw false t htc) hzt i
      have hprod := mul_pos (weight_pos i) hε
      have hwd := mul_nonneg (weight_pos i).le (show 0 ≤ drift by norm_num [drift])
      cases b
      · dsimp [y] at he
        have hzi : z t i = -weight i*K t := by linarith
        have hh := hface.2 hzi
        dsimp [dy]
        rw [heff]
        split_ifs <;> nlinarith
      · dsimp [y] at he
        have hzi : z t i = weight i*K t := by linarith
        have hh := hface.1 hzi
        dsimp [dy]
        rw [heff]
        split_ifs <;> nlinarith
    have hbar := finite_prefix_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,K] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro η hη
  have htime : 0 < 1+t := by linarith [ht.1]
  have hden : 0 < weight i*(1+t) := mul_pos (weight_pos i) htime
  have hh := inflated (η/(weight i*(1+t))) (div_pos hη hden) t ht i
  have heq : weight i*(envelope D t+(η/(weight i*(1+t)))*(1+t)) =
      weight i*envelope D t+η := by
    field_simp [ne_of_gt (weight_pos i),ne_of_gt htime]
  rw [heq] at hh
  exact hh

/-- Same actual measured admission and pending/digital history. The deadline
includes D. No endpoint cube, mismatch bound, or fresh dispatch reading is a
premise. The result includes every admitted real time and dispatch boundary. -/
theorem delayed_sampled_finite_entry {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hH : D+entryTime ≤ H) (hlim : D ≤ AdaptiveAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : AdaptiveAdmission.Execution H D m f r d stamp read)
    (hs : AdaptiveAdmission.IsSchedule H D q stamp read)
    (hm : q.measurement 0=m) (hg : AdaptiveAdmission.Guard m) :
    (∀ b, stamp b D=0 ∧ read b D=m) ∧
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates (AdaptiveAdmission.center m) (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc D H, weightedRadius (coordinates (AdaptiveAdmission.center m) (f t)) ≤ envelope D t) ∧
    (∀ t ∈ Icc (D+entryTime) H,
      weightedRadius (coordinates (AdaptiveAdmission.center m) (f t)) ≤ target ∧
      |f t 0-AdaptiveAdmission.center m| ≤ 459/10000 ∧
      |f t 1| ≤ 1827/5000 ∧ |f t 2| ≤ 1818/625) := by
  have hdur : 0 ≤ entryTime := by norm_num [entryTime]
  have hDH : D ≤ H := by linarith
  have hold := AdaptiveAdmission.delayed_sampled_hold hD hDH hlim ex hs hm hg
  have hi := AdaptiveAdmission.observation_admission hD hDH ex hs hm hg
  have hb := delayed_shrinking_box hD hDH hlim ex hi
  refine ⟨hold.1,hold.2.1,?_,?_⟩
  · intro t ht
    exact weighted_radius_le (hb t ⟨hD.trans ht.1,ht.2⟩)
  · intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hz : ∀ i, |coordinates (AdaptiveAdmission.center m) (f t) i| ≤ weight i*target := by
      intro i
      simpa only [envelope_plateau ht.1] using hb t ⟨ht0,ht.2⟩ i
    exact ⟨weighted_radius_le hz,weighted_physical_bounds hz⟩

end LeanControls.DelayedEntry
