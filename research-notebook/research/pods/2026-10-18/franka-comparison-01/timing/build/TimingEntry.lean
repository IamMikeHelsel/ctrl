module
public import TimingAdmission
public import TimingClock
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.TimingEntry
open Set Filter DigitalHold WeightedEntry

def radius : ℝ := 567/10000
def drift : ℝ := 3/5000
def residual : ℝ := 283/2500
def duration (m : State) : ℝ := (ClearancePolicy.policyRadius m-target)/drift
def envelope (m : State) (D t : ℝ) : ℝ := max target (ClearancePolicy.policyRadius m-drift*(t-D))

theorem duration_nonneg (m : State) : 0 ≤ duration m := by
  exact div_nonneg (sub_nonneg.mpr (ClearancePolicy.radius_floor m)) (by norm_num [drift])

theorem envelope_startup {m : State} {D t : ℝ} (ht : t ≤ D) :
    ClearancePolicy.policyRadius m ≤ envelope m D t := by
  have hh : ClearancePolicy.policyRadius m-drift*(t-D) ≤ envelope m D t := le_max_right _ _
  dsimp [drift] at hh
  linarith

theorem envelope_after {m : State} {D t : ℝ} (ht : D ≤ t) :
    envelope m D t ≤ ClearancePolicy.policyRadius m := by
  apply max_le (ClearancePolicy.radius_floor m)
  dsimp [drift]
  linarith

theorem envelope_before {m : State} {D t : ℝ} (ht : t ≤ D+duration m) :
    envelope m D t = ClearancePolicy.policyRadius m-drift*(t-D) := by
  apply max_eq_right
  dsimp [duration,drift] at ht ⊢
  linarith

theorem envelope_plateau {m : State} {D t : ℝ} (ht : D+duration m ≤ t) : envelope m D t = target := by
  apply max_eq_left
  dsimp [duration,drift] at ht ⊢
  linarith

/-- Incoming derivative at the plateau kink; physical clocks are unchanged. -/
theorem envelope_left_deriv (m : State) (D t : ℝ) :
    HasDerivWithinAt (envelope m D) (if t ≤ D+duration m then -drift else 0) (Iic t) t := by
  by_cases ht : t ≤ D+duration m
  · rw [if_pos ht]
    have hd : HasDerivAt (fun u : ℝ => ClearancePolicy.policyRadius m-drift*(u-D)) (-drift) t := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id t).sub_const D).const_mul drift).const_sub (ClearancePolicy.policyRadius m)
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventually_mem_nhdsWithin] with u hu
      change u ≤ t at hu
      exact envelope_before (hu.trans ht)
    · exact envelope_before ht
  · rw [if_neg ht]
    have hd : HasDerivAt (envelope m D) 0 t := by
      apply (hasDerivAt_const t target).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge ht)] with u hu
      exact envelope_plateau hu.le
    exact hd.hasDerivWithinAt

/-- First use the accepted delayed invariant; then recover the exact .111
residual from its actual whole-history slope. This is a conclusion, not a
new residual or invariant premise. -/
theorem derived_history_residual {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ TimingAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : TimingAdmission.Execution H D m f r d stamp read)
    (hi : TimingAdmission.Admitted m f) :
    ∀ b t, t ∈ Icc 0 H → |mismatch (TimingAdmission.center m) f d read b t| ≤ residual := by
  have hR : 0 ≤ radius := by norm_num [radius]
  have hRmax : radius ≤ 1/16 := by norm_num [radius]
  have hz := TimingAdmission.delayed_invariant (hD.trans hDH) hD hDH hlim ex hi
  have hw := TimingAdmission.prefix_budget ex (T := H) (K := radius)
    le_rfl hR hRmax hz le_rfl hD hDH hi hlim
  have hpre : ∀ x∈Ico 0 H, x<D → |TimingAdmission.actualSlope D m f r d read true x|≤8 := by
    intro x hx hxD
    exact TimingAdmission.startup_actual_slope ex hD hDH hi hlim x ⟨hx.1,hxD⟩
  have hpost : ∀ x∈Ico 0 H, D≤x →
      |TimingAdmission.actualSlope D m f r d read true x|≤108*radius := by
    intro x hx hxD
    have hxc : x∈Icc 0 H := ⟨hx.1,hx.2.le⟩
    have hh := slope_bound (w := mismatch (TimingAdmission.center m) f d read true x)
      hR (ex.rate true x hxc) (hz x hxc)
    have hmx := hw true x hxc
    have he : TimingAdmission.actualSlope D m f r d read true x =
        slopeRHS (r true x) (mismatch (TimingAdmission.center m) f d read true x)
          (coordinates (TimingAdmission.center m) (f x)) := by
      simp [TimingAdmission.actualSlope,TimingAdmission.actualMismatch,
        TimingAdmission.actualCommand,mismatch,not_lt.mpr hxD]
    rw [he]
    linarith
  intro b t ht
  have hh := TimingAdmission.split_mismatch ex (T := H) (K := radius)
    le_rfl hRmax hz hD hlim (by norm_num [radius] : 0≤108*radius)
    (by norm_num [radius] : 108*radius≤8) hpre hpost b t ht
  norm_num [TimingBudget.age,TimingBudget.delay,radius,residual] at hh ⊢
  linarith


/-- The moving-box argument stays on [0,H]. Contact at or before D is
excluded by the derived startup weighted box and the envelope. Only strictly after D is the
incoming command rewritten as digital feedback. -/
theorem delayed_shrinking_box {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ TimingAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : TimingAdmission.Execution H D m f r d stamp read)
    (hi : TimingAdmission.Admitted m f) :
    ∀ t ∈ Icc 0 H, ∀ i,
      |coordinates (TimingAdmission.center m) (f t) i| ≤ weight i*envelope m D t := by
  let z := fun t => coordinates (TimingAdmission.center m) (f t)
  have hH := hD.trans hDH
  have hz := TimingAdmission.delayed_invariant hH hD hDH hlim ex hi
  have hw := derived_history_residual hD hDH hlim ex hi
  have hstart := TimingAdmission.startup_weighted_box ex hD hDH hi hlim
  have hR : 0 ≤ radius := by norm_num [radius]
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ weight i*(envelope m D t+ε*(1+t)) := by
    let K := fun t => envelope m D t+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-weight p.1*K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t)
        (TimingAdmission.actualMismatch D m f d read false t) (z t) p.1
       else -transformedRHS (r false t)
        (TimingAdmission.actualMismatch D m f d read false t) (z t) p.1)-
      weight p.1*((if t ≤ D+duration m then -drift else 0)+ε)
    have hKc : Continuous K := by dsimp [K,envelope]; fun_prop
    have hKd (t : ℝ) : HasDerivWithinAt K
        ((if t ≤ D+duration m then -drift else 0)+ε) (Iic t) t := by
      have he : HasDerivWithinAt (fun u : ℝ => ε*(1+u)) ε (Iic t) t := by
        simpa only [id_eq,mul_one] using
          ((((hasDerivAt_id t).const_add 1).const_mul ε).hasDerivWithinAt (s := Iic t))
      exact (envelope_left_deriv m D t).add he
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := TimingAdmission.center m)
        (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub ((hKd t).const_mul (weight i))
      · exact hd.sub ((hKd t).const_mul (weight i))
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hstart 0 ⟨le_rfl,hD⟩ i)
      have he := envelope_startup (m := m) hD
      have hwi := weight_pos i
      have hp := mul_nonneg hwi.le (sub_nonneg.mpr he)
      cases b <;> dsimp [y,K,z] <;> nlinarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      by_cases hpre : t ≤ D
      · have hs := abs_le.mp (hstart t ⟨ht.1.le,hpre⟩ p.1)
        have henv := envelope_startup (m := m) hpre
        have hKt : ClearancePolicy.policyRadius m < K t := by dsimp [K]; nlinarith [ht.1]
        have hp := mul_pos (weight_pos p.1) (sub_pos.mpr hKt)
        obtain ⟨i,b⟩ := p
        cases b <;> dsimp [y,z] at he <;> dsimp at hs hp <;>
          exfalso <;> nlinarith
      have heff : TimingAdmission.actualMismatch D m f d read false t =
          mismatch (TimingAdmission.center m) f d read false t := by
        simp [TimingAdmission.actualMismatch,TimingAdmission.actualCommand,mismatch,hpre]
      have hKt : target ≤ K t := by
        have hm : target ≤ envelope m D t := le_max_left _ _
        dsimp [K]
        nlinarith [ht.1]
      have hzt (i : Fin 3) : |z t i| ≤ weight i*K t := by
        have hp := hall t ⟨ht.1.le,le_rfl⟩ (i,true)
        have hn := hall t ⟨ht.1.le,le_rfl⟩ (i,false)
        dsimp [y] at hp hn
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      obtain ⟨i,b⟩ := p
      have hface := TimingBudget.weighted_face hKt (ex.rate false t htc).1 (ex.rate false t htc).2
        (hw false t htc) hzt i
      rw [show TimingBudget.entryDrift=drift from rfl] at hface
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
  have heq : weight i*(envelope m D t+(η/(weight i*(1+t)))*(1+t)) =
      weight i*envelope m D t+η := by
    field_simp [ne_of_gt (weight_pos i),ne_of_gt htime]
  rw [heq] at hh
  exact hh

/-- One actual admitted execution supplies both all-time clearance and the
variable-radius envelope. No invariant, residual or endpoint box is a premise. -/
theorem sampled_clearance {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ TimingAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : TimingAdmission.Execution H D m f r d stamp read)
    (hs : TimingAdmission.IsSchedule H D q stamp read)
    (hm : q.measurement 0=m) (hg : TimingAdmission.Guard m) :
    (∀ b, stamp b D=0 ∧ read b D=m) ∧
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates (TimingAdmission.center m) (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc 0 H,
      (∀ i, |coordinates (TimingAdmission.center m) (f t) i| ≤ weight i*ClearancePolicy.policyRadius m) ∧
      f t 0 ≤ 3/20-1277551/20100000000) ∧
    (∀ t ∈ Icc D H, weightedRadius (coordinates (TimingAdmission.center m) (f t)) ≤ envelope m D t) := by
  have hold := TimingAdmission.delayed_sampled_hold hD hDH hlim ex hs hm hg
  have hi := TimingAdmission.observation_admission hD hDH ex hs hm hg
  have hb := delayed_shrinking_box hD hDH hlim ex hi
  have hstart := TimingAdmission.startup_weighted_box ex hD hDH hi hlim
  refine ⟨hold.1,hold.2.1,?_,?_⟩
  · intro t ht
    have hz : ∀ i, |coordinates (TimingAdmission.center m) (f t) i| ≤ weight i*ClearancePolicy.policyRadius m := by
      intro i
      by_cases hpre : t ≤ D
      · exact hstart t ⟨ht.1,hpre⟩ i
      · exact (hb t ht i).trans (mul_le_mul_of_nonneg_left (envelope_after (le_of_not_ge hpre)) (weight_pos i).le)
    refine ⟨hz,?_⟩
    have hx := (abs_le.mp (hz 0)).2
    have hu := ClearancePolicy.clearance_margin hg
    norm_num [coordinates,weight,TimingAdmission.center] at hx
    linarith
  · intro t ht
    exact weighted_radius_le (hb t ⟨hD.trans ht.1,ht.2⟩)

/-- The entry duration depends on the actual reading's policy radius. -/
theorem sampled_variable_entry {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hH : D+duration m ≤ H) (hlim : D ≤ TimingAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : TimingAdmission.Execution H D m f r d stamp read)
    (hs : TimingAdmission.IsSchedule H D q stamp read)
    (hm : q.measurement 0=m) (hg : TimingAdmission.Guard m) :
    ∀ t ∈ Icc (D+duration m) H,
      weightedRadius (coordinates (TimingAdmission.center m) (f t)) ≤ target ∧
      |f t 0-TimingAdmission.center m| ≤ 459/10000 ∧
      |f t 1| ≤ 1827/5000 ∧ |f t 2| ≤ 1818/625 := by
  have hDH : D ≤ H := by linarith [duration_nonneg m]
  have hi := TimingAdmission.observation_admission hD hDH ex hs hm hg
  have hb := delayed_shrinking_box hD hDH hlim ex hi
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1,duration_nonneg m]
  have hz : ∀ i, |coordinates (TimingAdmission.center m) (f t) i| ≤ weight i*target := by
    intro i
    simpa only [envelope_plateau ht.1] using hb t ⟨ht0,ht.2⟩ i
  exact ⟨weighted_radius_le hz,weighted_physical_bounds hz⟩

/-- This is an actual original-clock schedule, with T and D distinct.
It supplies clock/read selection only, not a future physical execution. -/
theorem periodic_schedule (H : ℝ) (m : ℕ→State) :
    TimingAdmission.IsSchedule H TimingClock.delay (TimingClock.schedule m)
      TimingClock.stamp (fun b t => m (TimingClock.index b t)) := by
  constructor
  · norm_num [TimingClock.schedule,TimingClock.dispatch,TimingClock.sample]
  · norm_num [TimingClock.schedule,TimingClock.sample]
  · intro b t ht; exact TimingClock.startup_index b ht.2
  · exact TimingClock.sample_dispatch
  · exact TimingClock.dispatch_strict
  · exact TimingClock.dispatch_locally_finite
  · intro t ht; exact TimingClock.right_cell ht.1
  · intro t ht; exact TimingClock.left_cell ht.1
  · intro b t ht; rfl
  · intro b t ht; rfl

/-- Concrete 1 kHz clock. The supplied physical execution still has to obey
its sensor box and the unchanged lag ODE; no constructor is imported. -/
theorem one_khz_clearance {H : ℝ} {m : ℕ→State}
    {f : ℝ→State} {r d : Bool→ℝ→ℝ}
    (hH : TimingClock.delay≤H)
    (ex : TimingAdmission.Execution H TimingClock.delay (m 0) f r d
      TimingClock.stamp (fun b t => m (TimingClock.index b t)))
    (hg : ClearancePolicy.Guard (m 0)) :
    ∀ t∈Icc 0 H, f t 0≤3/20-1277551/20100000000 := by
  have hh := sampled_clearance (by norm_num [TimingClock.delay]) hH
    (by norm_num [TimingClock.delay,TimingAdmission.startupLimit]) ex
    (periodic_schedule H m) rfl hg
  exact fun t ht => (hh.2.2.1 t ht).2

end LeanControls.TimingEntry
