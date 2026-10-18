module

public import LeanControls.TravelSafety
public import LeanControls.TravelExecution
public import LeanControls.Quantized

/-! Request error before saturation and held disturbance after saturation.
All statements concern exact-real held dynamics. Ideal sensor rounding below
does not model IEEE arithmetic, finite registers, or an implemented controller. -/

@[expose] public section
noncomputable section
namespace LeanControls.MeasuredTravel
open SaturatedLag (State input heldSegment)

abbrev V := TravelSafety.V

/-- The perturbed request is clipped before the physical held disturbance is added. -/
def segment (t : ℝ) (z : State) (e d : ℝ) : State :=
  heldSegment t z (RobustPD.saturate 1 (input z + e) + d)

/-- Compare two clipped commands, rather than assuming clipping is inactive. -/
def effectiveDisturbance (z : State) (e d : ℝ) : ℝ :=
  RobustPD.saturate 1 (input z + e) - RobustPD.saturate 1 (input z) + d

theorem effectiveDisturbance_bound (z : State) (e d : ℝ) :
    |effectiveDisturbance z e d| ≤ |e| + |d| := by
  exact (abs_add_le _ _).trans
    (add_le_add (SaturationSector.clamp_perturbation 1 (input z) e) le_rfl)

theorem segment_eq_effective (t : ℝ) (z : State) (e d : ℝ) :
    segment t z e d = SaturatedLag.segment t z (effectiveDisturbance z e d) := by
  unfold segment SaturatedLag.segment effectiveDisturbance
  congr 1
  ring

theorem segment_zero (z : State) (e d : ℝ) : segment 0 z e d = z :=
  SaturatedLag.heldSegment_zero z _

/-- The same exact plant is driven by the actual perturbed, clipped held input. -/
theorem segment_ode (t : ℝ) (z : State) (e d : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => segment s z e d i)
      (ActuatorLag.vectorField (RobustPD.saturate 1 (input z + e) + d)
        (segment t z e d) i) t :=
  SaturatedLag.heldSegment_ode t z _ i

theorem segment_invariant {t e d : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5)
    (hbudget : |e| + |d| ≤ 1 / 100) {z : State} (hz : V z ≤ 12) :
    V (segment t z e d) ≤ 12 := by
  rw [segment_eq_effective]
  exact TravelSafety.segment_invariant ht0 hthi
    ((effectiveDisturbance_bound z e d).trans hbudget) hz

theorem segment_position_safe {t e d : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5)
    (hbudget : |e| + |d| ≤ 1 / 100) {z : State} (hz : V z ≤ 12) :
    |segment t z e d 0| ≤ 2 :=
  TravelGeometry.position_safe (segment_invariant ht0 hthi hbudget hz)

/-- Defined execution: the request error and physical disturbance are each held
for one sample interval and may change arbitrarily at the next sample. -/
def samples (h e d : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n + 1 => segment (h n) (samples h e d z0 n) (e n) (d n)

theorem samples_zero (h e d : ℕ → ℝ) (z0 : State) : samples h e d z0 0 = z0 := rfl

theorem samples_succ (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) :
    samples h e d z0 (n + 1) = segment (h n) (samples h e d z0 n) (e n) (d n) := rfl

theorem samples_invariant (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1 / 100) (hz : V z0 ≤ 12) :
    ∀ n, V (samples h e d z0 n) ≤ 12 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => exact segment_invariant (hlo n) (hhi n) (hbudget n) ih

/-- Exact continuous-time assembly of the actual perturbed held execution. -/
def state (h e d : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  let n := SamplingClock.segmentIndex h t
  segment (t - SamplingClock.sampleTime h n) (samples h e d z0 n) (e n) (d n)

theorem state_at_sample (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state h e d z0 (SamplingClock.sampleTime h n) = samples h e d z0 n := by
  simp [state, SamplingClock.segmentIndex_at_sample h hmin0 hlo n, segment_zero]

theorem state_invariant (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1 / 100) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : V (state h e d z0 t) ≤ 12 := by
  obtain ⟨htlo, hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
  rw [SamplingClock.sampleTime_succ] at hthi
  apply segment_invariant (sub_nonneg.mpr htlo)
    (by linarith [hhi (SamplingClock.segmentIndex h t)])
    (hbudget (SamplingClock.segmentIndex h t))
  exact samples_invariant h e d z0 (fun n => hmin0.le.trans (hlo n)) hhi hbudget hz _

/-- Every admissible initial state, jitter sequence, error/disturbance sequence,
and nonnegative real time obey the same travel limit, with active clipping allowed. -/
theorem travel_limit (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1 / 100) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : |state h e d z0 t 0| ≤ 2 :=
  TravelGeometry.position_safe (state_invariant h e d z0 hmin0 hlo hhi hbudget hz ht)

/-- A nonzero request error and a nonzero physical disturbance are admitted at
an initial state where the perturbed request is still genuinely clipped. -/
theorem active_initial : V ![0, 0, 1] < 12 ∧
    |(1 / 200 : ℝ)| + |(1 / 200 : ℝ)| ≤ 1 / 100 ∧
    input ![0, 0, 1] + 1 / 200 < -1 ∧
    RobustPD.saturate 1 (input ![0, 0, 1] + 1 / 200) = -1 := by
  refine ⟨TravelSafety.active_initial.1, ?_⟩
  norm_num [input, RobustPD.saturate]

theorem active_example_travel {t : ℝ} (ht : 0 ≤ t) :
    |state (fun _ => 1 / 10) (fun _ => 1 / 200) (fun _ => 1 / 200)
      ![0, 0, 1] t 0| ≤ 2 := by
  apply travel_limit (hmin := 1 / 10) _ _ _ _
    (by norm_num) (by intro n; norm_num) (by intro n; norm_num)
    (by intro n; norm_num) TravelSafety.active_initial.1.le ht

/-- Ideal nearest-grid sensing with independent grids for the three coordinates. -/
def roundedRequest (dx dv da : ℝ) (z : State) : ℝ :=
  -Quantized.quantize dx (z 0) - 3 * Quantized.quantize dv (z 1) -
    2 * Quantized.quantize da (z 2)

def roundedRequestError (dx dv da : ℝ) (z : State) : ℝ :=
  roundedRequest dx dv da z - input z

theorem roundedRequestError_bound {dx dv da : ℝ}
    (hdx : 0 < dx) (hdv : 0 < dv) (hda : 0 < da) (z : State) :
    |roundedRequestError dx dv da z| ≤ dx / 2 + 3 * dv / 2 + da := by
  have hx := abs_le.mp (Quantized.rounding_error hdx (z 0))
  have hv := abs_le.mp (Quantized.rounding_error hdv (z 1))
  have ha := abs_le.mp (Quantized.rounding_error hda (z 2))
  apply abs_le.mpr
  dsimp [roundedRequestError, roundedRequest, input]
  constructor <;> linarith [hx.1, hx.2, hv.1, hv.2, ha.1, ha.2]

def roundedSegment (dx dv da t : ℝ) (z : State) (d : ℝ) : State :=
  segment t z (roundedRequestError dx dv da z) d

/-- This is the actual rounded request before the clamp, with no inactive-clamp premise. -/
theorem roundedSegment_eq_held (dx dv da t : ℝ) (z : State) (d : ℝ) :
    roundedSegment dx dv da t z d =
      heldSegment t z (RobustPD.saturate 1 (roundedRequest dx dv da z) + d) := by
  simp only [roundedSegment, segment, roundedRequestError, add_sub_cancel]

theorem roundedSegment_zero (dx dv da : ℝ) (z : State) (d : ℝ) :
    roundedSegment dx dv da 0 z d = z := segment_zero z _ d

theorem rounded_segment_invariant {dx dv da t d W : ℝ}
    (hdx : 0 < dx) (hdv : 0 < dv) (hda : 0 < da)
    (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5)
    (hbudget : dx / 2 + 3 * dv / 2 + da + W ≤ 1 / 100) (hd : |d| ≤ W)
    {z : State} (hz : V z ≤ 12) : V (roundedSegment dx dv da t z d) ≤ 12 :=
  segment_invariant ht0 hthi
    ((add_le_add (roundedRequestError_bound hdx hdv hda z) hd).trans hbudget) hz

/-- The sensor errors are computed from these actual recursive sample states. -/
def roundedSamples (dx dv da : ℝ) (h d : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n + 1 => roundedSegment dx dv da (h n) (roundedSamples dx dv da h d z0 n) (d n)

theorem rounded_samples_invariant {dx dv da W : ℝ}
    (hdx : 0 < dx) (hdv : 0 < dv) (hda : 0 < da)
    (hbudget : dx / 2 + 3 * dv / 2 + da + W ≤ 1 / 100)
    (h d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hd : ∀ n, |d n| ≤ W) (hz : V z0 ≤ 12) :
    ∀ n, V (roundedSamples dx dv da h d z0 n) ≤ 12 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    exact rounded_segment_invariant hdx hdv hda (hlo n) (hhi n) hbudget (hd n) ih

def roundedState (dx dv da : ℝ) (h d : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  let n := SamplingClock.segmentIndex h t
  roundedSegment dx dv da (t - SamplingClock.sampleTime h n)
    (roundedSamples dx dv da h d z0 n) (d n)

theorem rounded_state_at_sample (dx dv da : ℝ) (h d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    roundedState dx dv da h d z0 (SamplingClock.sampleTime h n) =
      roundedSamples dx dv da h d z0 n := by
  simp [roundedState, SamplingClock.segmentIndex_at_sample h hmin0 hlo n,
    roundedSegment_zero]

theorem rounded_state_invariant {dx dv da W : ℝ}
    (hdx : 0 < dx) (hdv : 0 < dv) (hda : 0 < da)
    (hbudget : dx / 2 + 3 * dv / 2 + da + W ≤ 1 / 100)
    (h d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hd : ∀ n, |d n| ≤ W) (hz : V z0 ≤ 12) {t : ℝ} (ht : 0 ≤ t) :
    V (roundedState dx dv da h d z0 t) ≤ 12 := by
  obtain ⟨htlo, hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
  rw [SamplingClock.sampleTime_succ] at hthi
  apply rounded_segment_invariant hdx hdv hda (sub_nonneg.mpr htlo)
    (by linarith [hhi (SamplingClock.segmentIndex h t)]) hbudget
    (hd (SamplingClock.segmentIndex h t))
  exact rounded_samples_invariant hdx hdv hda hbudget h d z0
    (fun n => hmin0.le.trans (hlo n)) hhi hd hz _

/-- Continuous-time travel safety for ideal nearest-grid sensors with separate
resolutions. This is an exact-real rounding model, not a finite-bit implementation. -/
theorem rounded_travel_limit {dx dv da W : ℝ}
    (hdx : 0 < dx) (hdv : 0 < dv) (hda : 0 < da)
    (hbudget : dx / 2 + 3 * dv / 2 + da + W ≤ 1 / 100)
    (h d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 5)
    (hd : ∀ n, |d n| ≤ W) (hz : V z0 ≤ 12) {t : ℝ} (ht : 0 ≤ t) :
    |roundedState dx dv da h d z0 t 0| ≤ 2 :=
  TravelGeometry.position_safe
    (rounded_state_invariant hdx hdv hda hbudget h d z0 hmin0 hlo hhi hd hz ht)

/-- A concrete positive-resolution budget leaves room for a nonzero physical
disturbance; the rounded initial command is still clipped. -/
theorem rounded_active_example :
    (1 / 1000 : ℝ) / 2 + 3 * (1 / 1000) / 2 + 1 / 1000 + 7 / 1000 ≤ 1 / 100 ∧
    roundedRequest (1 / 1000) (1 / 1000) (1 / 1000) ![0, 0, 1] = -2 ∧
    RobustPD.saturate 1
      (roundedRequest (1 / 1000) (1 / 1000) (1 / 1000) ![0, 0, 1]) = -1 := by
  norm_num [roundedRequest, Quantized.quantize, RobustPD.saturate]

/-- Express the actual measured execution through the existing nominal-clamp
API using a sequence computed from the already defined actual samples. -/
def effectiveErrors (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) : ℝ :=
  effectiveDisturbance (samples h e d z0 n) (e n) (d n)

theorem samples_eq_effective (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) :
    samples h e d z0 n = TravelSafety.samples h (effectiveErrors h e d z0) z0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [samples_succ, TravelSafety.samples_succ, ← ih, segment_eq_effective]
    rfl

theorem state_eq_effective (h e d : ℕ → ℝ) (z0 : State) (t : ℝ) :
    state h e d z0 t = TravelSafety.state h (effectiveErrors h e d z0) z0 t := by
  dsimp [state, TravelSafety.state]
  rw [← samples_eq_effective]
  exact segment_eq_effective _ _ _ _

/-- The actual perturbed execution is continuous through sample boundaries. -/
theorem state_continuousOn_nonnegative (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    ContinuousOn (state h e d z0) (Set.Ici 0) := by
  have hf : state h e d z0 = TravelSafety.state h (effectiveErrors h e d z0) z0 :=
    funext (state_eq_effective h e d z0)
  rw [hf]
  exact TravelExecution.state_continuousOn_nonnegative h _ z0 hmin0 hlo

/-- Away from update times, the assembled trajectory satisfies the ODE with
the actual erroneous request before clipping and disturbance after clipping. -/
theorem state_ode_interior (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {t : ℝ}
    (htlo : SamplingClock.sampleTime h n < t)
    (hthi : t < SamplingClock.sampleTime h (n + 1)) (i : Fin 3) :
    HasDerivAt (fun r => state h e d z0 r i)
      (ActuatorLag.vectorField
        (RobustPD.saturate 1 (input (samples h e d z0 n) + e n) + d n)
        (state h e d z0 t) i) t := by
  have hd := TravelExecution.state_ode_interior h (effectiveErrors h e d z0) z0
    hmin0 hlo n htlo hthi i
  simp only [← samples_eq_effective, ← state_eq_effective] at hd
  have hcommand : RobustPD.saturate 1 (input (samples h e d z0 n)) +
      effectiveErrors h e d z0 n =
      RobustPD.saturate 1 (input (samples h e d z0 n) + e n) + d n := by
    dsimp [effectiveErrors, effectiveDisturbance]
    ring
  rw [hcommand] at hd
  exact hd

end LeanControls.MeasuredTravel
