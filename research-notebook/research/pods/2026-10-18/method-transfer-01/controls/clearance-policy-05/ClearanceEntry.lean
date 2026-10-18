module
public import ClearanceAdmission
public import DelayedEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ClearanceEntry
open Set Filter DigitalHold WeightedEntry

def residual : ℝ := 111/1000
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
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ ClearanceAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : ClearanceAdmission.Execution H D m f r d stamp read)
    (hi : ClearanceAdmission.Admitted m f) :
    ∀ b t, t ∈ Icc 0 H → |mismatch (ClearanceAdmission.center m) f d read b t| ≤ residual := by
  have hR : 0 ≤ radius := by norm_num [radius]
  have hRmax : radius ≤ 1/16 := by norm_num [radius]
  have hz := ClearanceAdmission.delayed_invariant (hD.trans hDH) hD hDH hlim ex hi
  have hw := ClearanceAdmission.prefix_budget ex (T := H) (K := radius)
    le_rfl hR hRmax hz le_rfl hD hDH hi hlim
  have hsl : ∀ x ∈ Ico 0 H, |ClearanceAdmission.actualSlope D m f r d read true x| ≤ 8 := by
    intro x hx
    by_cases hb : x < D
    · exact ClearanceAdmission.startup_actual_slope ex hD hDH hi hlim x ⟨hx.1,hb⟩
    · have hxc : x ∈ Icc 0 H := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch (ClearanceAdmission.center m) f d read true x)
        hR (ex.rate true x hxc) (hz x hxc)
      have hmx := hw true x hxc
      have he : ClearanceAdmission.actualSlope D m f r d read true x =
          slopeRHS (r true x) (mismatch (ClearanceAdmission.center m) f d read true x)
            (coordinates (ClearanceAdmission.center m) (f x)) := by
        simp [ClearanceAdmission.actualSlope,ClearanceAdmission.actualMismatch,
          ClearanceAdmission.actualCommand,mismatch,hb]
      rw [he]
      norm_num [radius] at hh hmx
      linarith
  intro b t ht
  have hh := ClearanceAdmission.improve_mismatch ex (T := H) (K := radius)
    le_rfl hRmax hz (by norm_num : (0:ℝ) ≤ 8) hsl b t ht
  convert hh using 1 <;> norm_num [residual]

/-- The moving-box argument stays on [0,H]. Contact at or before D is
excluded by the derived startup weighted box and the envelope. Only strictly after D is the
incoming command rewritten as digital feedback. -/
theorem delayed_shrinking_box {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ ClearanceAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : ClearanceAdmission.Execution H D m f r d stamp read)
    (hi : ClearanceAdmission.Admitted m f) :
    ∀ t ∈ Icc 0 H, ∀ i,
      |coordinates (ClearanceAdmission.center m) (f t) i| ≤ weight i*envelope m D t := by
  let z := fun t => coordinates (ClearanceAdmission.center m) (f t)
  have hH := hD.trans hDH
  have hz := ClearanceAdmission.delayed_invariant hH hD hDH hlim ex hi
  have hw := derived_history_residual hD hDH hlim ex hi
  have hstart := ClearanceAdmission.startup_weighted_box ex hD hDH hi hlim
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
        (ClearanceAdmission.actualMismatch D m f d read false t) (z t) p.1
       else -transformedRHS (r false t)
        (ClearanceAdmission.actualMismatch D m f d read false t) (z t) p.1)-
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
      have hd := coordinate_deriv (c := ClearanceAdmission.center m)
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
      have heff : ClearanceAdmission.actualMismatch D m f d read false t =
          mismatch (ClearanceAdmission.center m) f d read false t := by
        simp [ClearanceAdmission.actualMismatch,ClearanceAdmission.actualCommand,mismatch,hpre]
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
      have hface := DelayedEntry.weighted_face hKt (ex.rate false t htc).1 (ex.rate false t htc).2
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
  have heq : weight i*(envelope m D t+(η/(weight i*(1+t)))*(1+t)) =
      weight i*envelope m D t+η := by
    field_simp [ne_of_gt (weight_pos i),ne_of_gt htime]
  rw [heq] at hh
  exact hh

/-- One actual admitted execution supplies both all-time clearance and the
variable-radius envelope. No invariant, residual or endpoint box is a premise. -/
theorem sampled_clearance {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ ClearanceAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : ClearanceAdmission.Execution H D m f r d stamp read)
    (hs : ClearanceAdmission.IsSchedule H D q stamp read)
    (hm : q.measurement 0=m) (hg : ClearanceAdmission.Guard m) :
    (∀ b, stamp b D=0 ∧ read b D=m) ∧
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates (ClearanceAdmission.center m) (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc 0 H,
      (∀ i, |coordinates (ClearanceAdmission.center m) (f t) i| ≤ weight i*ClearancePolicy.policyRadius m) ∧
      f t 0 ≤ 3/20-1277551/20100000000) ∧
    (∀ t ∈ Icc D H, weightedRadius (coordinates (ClearanceAdmission.center m) (f t)) ≤ envelope m D t) := by
  have hold := ClearanceAdmission.delayed_sampled_hold hD hDH hlim ex hs hm hg
  have hi := ClearanceAdmission.observation_admission hD hDH ex hs hm hg
  have hb := delayed_shrinking_box hD hDH hlim ex hi
  have hstart := ClearanceAdmission.startup_weighted_box ex hD hDH hi hlim
  refine ⟨hold.1,hold.2.1,?_,?_⟩
  · intro t ht
    have hz : ∀ i, |coordinates (ClearanceAdmission.center m) (f t) i| ≤ weight i*ClearancePolicy.policyRadius m := by
      intro i
      by_cases hpre : t ≤ D
      · exact hstart t ⟨ht.1,hpre⟩ i
      · exact (hb t ht i).trans (mul_le_mul_of_nonneg_left (envelope_after (le_of_not_ge hpre)) (weight_pos i).le)
    refine ⟨hz,?_⟩
    have hx := (abs_le.mp (hz 0)).2
    have hu := ClearancePolicy.clearance_margin hg
    norm_num [coordinates,weight,ClearanceAdmission.center] at hx
    linarith
  · intro t ht
    exact weighted_radius_le (hb t ⟨hD.trans ht.1,ht.2⟩)

/-- The entry duration depends on the actual reading's policy radius. -/
theorem sampled_variable_entry {H D : ℝ} {m : State}
    (hD : 0 ≤ D) (hH : D+duration m ≤ H) (hlim : D ≤ ClearanceAdmission.startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : ClearanceAdmission.Execution H D m f r d stamp read)
    (hs : ClearanceAdmission.IsSchedule H D q stamp read)
    (hm : q.measurement 0=m) (hg : ClearanceAdmission.Guard m) :
    ∀ t ∈ Icc (D+duration m) H,
      weightedRadius (coordinates (ClearanceAdmission.center m) (f t)) ≤ target ∧
      |f t 0-ClearanceAdmission.center m| ≤ 459/10000 ∧
      |f t 1| ≤ 1827/5000 ∧ |f t 2| ≤ 1818/625 := by
  have hDH : D ≤ H := by linarith [duration_nonneg m]
  have hi := ClearanceAdmission.observation_admission hD hDH ex hs hm hg
  have hb := delayed_shrinking_box hD hDH hlim ex hi
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1,duration_nonneg m]
  have hz : ∀ i, |coordinates (ClearanceAdmission.center m) (f t) i| ≤ weight i*target := by
    intro i
    simpa only [envelope_plateau ht.1] using hb t ⟨ht0,ht.2⟩ i
  exact ⟨weighted_radius_le hz,weighted_physical_bounds hz⟩

end LeanControls.ClearanceEntry
