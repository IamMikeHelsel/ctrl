module
public import DigitalHold

/-! Finite entry for the accepted sampled execution, using the original clock.
The old cube is proved first and supplies the mismatch estimate. A weighted
moving box then shrinks to a plateau. No smaller initial cube or mismatch
premise is introduced. The finite-family first-contact argument uses the left
ODE at dispatch and at the plateau kink. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.WeightedEntry
open Set Filter
open DigitalHold

def weight : Fin 3 → ℝ := ![51/50,101/100,1]
def target : ℝ := 9/200
def drift : ℝ := 3/1700
def entryTime : ℝ := 5
def residual : ℝ := 136350047/1250000000
def envelope (t : ℝ) : ℝ := max target (radius-drift*t)
def weightedRadius (z : State) : ℝ := max (|z 0|/(51/50)) (max (|z 1|/(101/100)) |z 2|)

theorem weighted_radius_le {z : State} {K : ℝ} (hz : ∀ i, |z i| ≤ weight i*K) :
    weightedRadius z ≤ K := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  norm_num [weight] at h0 h1 h2
  apply max_le
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<51/50)).mpr
    linarith
  · apply max_le
    · apply (div_le_iff₀ (by norm_num : (0:ℝ)<101/100)).mpr
      linarith
    · exact h2

theorem weight_ge_one (i : Fin 3) : 1 ≤ weight i := by
  fin_cases i <;> norm_num [weight]

theorem weight_pos (i : Fin 3) : 0 < weight i := lt_of_lt_of_le zero_lt_one (weight_ge_one i)

theorem envelope_initial : envelope 0 = radius := by norm_num [envelope,target,radius]

theorem envelope_before {t : ℝ} (ht : t ≤ entryTime) : envelope t = radius-drift*t := by
  apply max_eq_right
  dsimp [entryTime,drift,target,radius] at ht ⊢
  linarith

theorem envelope_plateau {t : ℝ} (ht : entryTime ≤ t) : envelope t = target := by
  apply max_eq_left
  dsimp [entryTime,drift,target,radius] at ht ⊢
  linarith

/-- The moving box has the incoming linear slope exactly at its kink. -/
theorem envelope_left_deriv (t : ℝ) :
    HasDerivWithinAt envelope (if t ≤ entryTime then -drift else 0) (Iic t) t := by
  by_cases ht : t ≤ entryTime
  · rw [if_pos ht]
    have hd : HasDerivAt (fun u : ℝ => radius-drift*u) (-drift) t := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul drift).const_sub radius
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [eventually_mem_nhdsWithin] with u hu
      change u ≤ t at hu
      exact envelope_before (hu.trans ht)
    · exact envelope_before ht
  · rw [if_neg ht]
    have hd : HasDerivAt envelope 0 t := by
      apply (hasDerivAt_const t target).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge ht)] with u hu
      exact envelope_plateau hu.le
    exact hd.hasDerivWithinAt

/-- Every face of every weighted box outside the plateau has a uniform
normalized inward drift. The residual is the old derived 1 ms budget. -/
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

/-- The old invariant is a theorem used before, rather than assumed by, the
new progress argument. Thus the mismatch premise is discharged globally. -/
theorem derived_residual {H c : ℝ} (hH : 0 ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    ∀ b t, t ∈ Icc 0 H → |mismatch c f d read b t| ≤ residual := by
  have hz := digital_invariant hH ex hi
  intro b t ht
  have hh := prefix_mismatch ex (T := H) (K := radius) le_rfl
    (by norm_num [radius]) (by norm_num [radius]) hz b t ht
  convert hh using 1 <;> norm_num [radius,residual]

/-- Uniform moving-box enclosure on the original execution horizon. The
epsilon inflation is removed after the strict first-contact proof. -/
theorem execution_shrinking_box {H c : ℝ} (hH : 0 ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ weight i*envelope t := by
  let z := fun t => coordinates c (f t)
  have hw := derived_residual hH ex hi
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ weight i*(envelope t+ε*(1+t)) := by
    let K := fun t => envelope t+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-weight p.1*K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t) (mismatch c f d read false t) (z t) p.1
       else -transformedRHS (r false t) (mismatch c f d read false t) (z t) p.1)-
      weight p.1*((if t ≤ entryTime then -drift else 0)+ε)
    have hKc : Continuous K := by dsimp [K,envelope]; fun_prop
    have hKd (t : ℝ) : HasDerivWithinAt K
        ((if t ≤ entryTime then -drift else 0)+ε) (Iic t) t := by
      have he : HasDerivWithinAt (fun u : ℝ => ε*(1+u)) ε (Iic t) t := by
        simpa only [id_eq,mul_one] using
          ((((hasDerivAt_id t).const_add 1).const_mul ε).hasDerivWithinAt (s := Iic t))
      exact (envelope_left_deriv t).add he
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := c) (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub ((hKd t).const_mul (weight i))
      · exact hd.sub ((hKd t).const_mul (weight i))
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      have hwi := weight_pos i
      have hwR := mul_nonneg (sub_nonneg.mpr (weight_ge_one i)) (show 0 ≤ radius by norm_num [radius])
      cases b <;> dsimp [y,K,z] <;> rw [envelope_initial] <;> nlinarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hKt : target ≤ K t := by
        have hm : target ≤ envelope t := le_max_left _ _
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
        split_ifs <;> nlinarith
      · dsimp [y] at he
        have hzi : z t i = weight i*K t := by linarith
        have hh := hface.1 hzi
        dsimp [dy]
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
  have heq : weight i*(envelope t+(η/(weight i*(1+t)))*(1+t)) = weight i*envelope t+η := by
    field_simp [ne_of_gt (weight_pos i),ne_of_gt htime]
  rw [heq] at hh
  exact hh

theorem weighted_physical_bounds {c : ℝ} {s : State}
    (hz : ∀ i, |coordinates c s i| ≤ weight i*target) :
    |s 0-c| ≤ 459/10000 ∧ |s 1| ≤ 1827/5000 ∧ |s 2| ≤ 1818/625 := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  norm_num [coordinates,weight,target] at h0 h1 h2
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩

/-- Same accepted initial cube and same sampled execution/clock. After the
stated time, the smaller weighted box holds at every real time, including
dispatch boundaries. No reset or new measurement is required at entry. -/
theorem sampled_finite_entry {H c : ℝ} (hH : entryTime ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (hx : IsSampledExecution H c f r d stamp read q)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius) :
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc 0 H, weightedRadius (coordinates c (f t)) ≤ envelope t) ∧
    (∀ t ∈ Icc entryTime H,
      weightedRadius (coordinates c (f t)) ≤ target ∧
      |f t 0-c| ≤ 459/10000 ∧ |f t 1| ≤ 1827/5000 ∧ |f t 2| ≤ 1818/625) := by
  have hH0 : 0 ≤ H := le_trans (by norm_num [entryTime]) hH
  have hb := execution_shrinking_box hH0 hx.1 hi
  refine ⟨digital_invariant hH0 hx.1 hi,(fun t ht => weighted_radius_le (hb t ht)),?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num [entryTime]) ht.1
  have hz : ∀ i, |coordinates c (f t) i| ≤ weight i*target := by
    intro i
    simpa only [envelope_plateau ht.1] using hb t ⟨ht0,ht.2⟩ i
  exact ⟨weighted_radius_le hz,weighted_physical_bounds hz⟩

/-- The equal-weight radius has zero outward derivative on two active faces
at this admissible algebraic state. It does not supply a strict entry rate. -/
theorem equal_weight_zero_drift :
    transformedRHS 8 0 ![target,target,target] = ![0,0,-4*target] ∧
    ¬ transformedRHS 8 0 ![target,target,target] 0 ≤ -drift := by
  constructor
  · ext i
    fin_cases i <;> norm_num [transformedRHS,target]
  · norm_num [transformedRHS,target,drift]

/-- The accepted initial cube contains states outside the target weighted
box. This is an initial-state test, not a general trajectory-existence proof. -/
theorem old_initial_not_small :
    (∀ i, |coordinates 0 ![0,0,16*radius] i| ≤ radius) ∧
    target < weightedRadius (coordinates 0 ![0,0,16*radius]) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [coordinates,radius]
  · norm_num [weightedRadius,coordinates,radius,target]

/-- The first weighted face attains the selected normalized drift exactly. -/
theorem first_face_drift_exact :
    transformedRHS 8 0 ![(51/50)*target,(101/100)*target,target] 0 / (51/50) = -drift := by
  norm_num [transformedRHS,target,drift]

/-- With only the global residual bound, shrinking the candidate plateau to
0.04 would allow an outward third face. No realizability of this extreme
aggregate residual by a sampled sensor history is asserted here. -/
theorem smaller_plateau_outward :
    0 < transformedRHS 12 residual ![-(51/50)*(1/25),(101/100)*(1/25),1/25] 2 := by
  norm_num [transformedRHS,residual]

end LeanControls.WeightedEntry
