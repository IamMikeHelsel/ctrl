module
public import ActualStop

/-! Propagate a noisy state reading through a bounded command delay, then
certify a capture cube without resetting position, velocity or acceleration.
All positions use a common fixed reference. This is an admission test, not a
claim that a sample sequence must eventually pass that test. -/
@[expose] public section
noncomputable section
namespace LeanControls.SampledCapture
open Set
open UncertainLag (State)
open VariableResponse

theorem scalar_age_bound {H M e c : ℝ} (hH : 0 ≤ H)
    {f df : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 H))
    (hd : ∀ t ∈ Ioo 0 H, HasDerivAt f (df t) t)
    (h0 : |f 0 - c| ≤ e) (hb : ∀ t ∈ Icc 0 H, |df t| ≤ M) :
    ∀ t ∈ Icc 0 H, |f t-c| ≤ e+M*t := by
  have hu : ∀ t ∈ Icc 0 H, f t ≤ c+e+M*t := by
    apply derivative_comparison hH hf (by fun_prop) hd
      (fun t _ => by simpa using ((hasDerivAt_id t).const_mul M).const_add (c+e))
      (by have := (abs_le.mp h0).2; simpa using (show f 0 ≤ c+e by linarith))
    intro t ht
    exact (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩)).2
  have hl : ∀ t ∈ Icc 0 H, c-e-M*t ≤ f t := by
    apply derivative_comparison hH (by fun_prop) hf
      (fun t _ => by simpa using ((hasDerivAt_id t).const_mul M).const_sub (c-e)) hd
      (by have := (abs_le.mp h0).1; simpa using (show c-e ≤ f 0 by linarith))
    intro t ht
    exact (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩)).1
  intro t ht
  rw [abs_le]
  constructor <;> linarith [hu t ht, hl t ht]

structure IsCaptureTrajectory (H : ℝ) (f : ℝ → State) (j : ℝ → ℝ) : Prop where
  continuous : ContinuousOn f (Icc 0 H)
  position_deriv : ∀ t ∈ Ioo 0 H, HasDerivAt (fun s => f s 0) (f t 1) t
  velocity_deriv : ∀ t ∈ Ioo 0 H, HasDerivAt (fun s => f s 1) (f t 2) t
  acceleration_deriv : ∀ t ∈ Ioo 0 H, HasDerivAt (fun s => f s 2) (j t) t

def ageX (D A xError vError vhat : ℝ) : ℝ :=
  xError+(|vhat|+vError+A*D)*D
def ageV (D A vError : ℝ) : ℝ := vError+A*D
def ageA (D J aError : ℝ) : ℝ := aError+J*D

/-- A downward measured threshold crossing gives a two-sided velocity bound.
Unlike a narrow absolute-value band, the trigger does not require a sample
inside that band. Existence of a triggering sample is a separate obligation. -/
theorem crossing_sample_velocity {H A ev threshold previous current : ℝ}
    (hH : 0 ≤ H) {v a : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 H))
    (hd : ∀ t ∈ Ioo 0 H, HasDerivAt v (a t) t)
    (hb : ∀ t ∈ Icc 0 H, |a t| ≤ A)
    (hp : |v 0-previous| ≤ ev) (hn : |v H-current| ≤ ev)
    (hprev : threshold < previous) (hnow : current ≤ threshold) :
    threshold-ev-A*H < v H ∧ v H ≤ threshold+ev := by
  have hmove := scalar_age_bound hH hc hd
    (c := v 0) (e := 0) (by simp) hb H ⟨hH,le_rfl⟩
  have hp' := abs_le.mp hp
  have hn' := abs_le.mp hn
  have hm' := abs_le.mp hmove
  constructor <;> linarith

/-- All states during the measurement-to-command delay lie in this enlarged box.
The acceleration and jerk bounds are explicit physical assumptions. -/
theorem delayed_measurement_box {D A J ex ev ea xhat vhat ahat : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hev : 0 ≤ ev)
    {f : ℝ → State} {j : ℝ → ℝ} (hf : IsCaptureTrajectory D f j)
    (hx : |f 0 0-xhat| ≤ ex) (hv : |f 0 1-vhat| ≤ ev)
    (ha : |f 0 2-ahat| ≤ ea)
    (hab : ∀ t ∈ Icc 0 D, |f t 2| ≤ A)
    (hjb : ∀ t ∈ Icc 0 D, |j t| ≤ J) :
    ∀ t ∈ Icc 0 D,
      |f t 0-xhat| ≤ ageX D A ex ev vhat ∧
      |f t 1-vhat| ≤ ageV D A ev ∧
      |f t 2-ahat| ≤ ageA D J ea := by
  have hc (i : Fin 3) : ContinuousOn (fun t => f t i) (Icc 0 D) :=
    (continuous_apply i).comp_continuousOn hf.continuous
  have hvb := scalar_age_bound hD (hc 1) hf.velocity_deriv hv hab
  have hab' := scalar_age_bound hD (hc 2) hf.acceleration_deriv ha hjb
  have hs : ∀ t ∈ Icc 0 D, |f t 1| ≤ |vhat|+ev+A*D := by
    intro t ht
    have htri : |f t 1| ≤ |f t 1-vhat|+|vhat| := by
      convert abs_add_le (f t 1-vhat) vhat using 1; congr 1; ring
    have hmul := mul_le_mul_of_nonneg_left ht.2 hA
    linarith [hvb t ht]
  have hxb := scalar_age_bound hD (hc 0) hf.position_deriv hx hs
  intro t ht
  have hspeed : 0 ≤ |vhat|+ev+A*D := by positivity
  have hxmul := mul_le_mul_of_nonneg_left ht.2 hspeed
  have hvmul := mul_le_mul_of_nonneg_left ht.2 hA
  have hamul := mul_le_mul_of_nonneg_left ht.2 hJ
  dsimp [ageX, ageV, ageA]
  exact ⟨by linarith [hxb t ht], by linarith [hvb t ht], by linarith [hab' t ht]⟩

/-- The actual command delay may be shorter than the certified maximum. -/
theorem bounded_delay_measurement_box {d D A J ex ev ea xhat vhat ahat : ℝ}
    (hd : 0 ≤ d) (hdD : d ≤ D) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hev : 0 ≤ ev)
    {f : ℝ → State} {j : ℝ → ℝ} (hf : IsCaptureTrajectory d f j)
    (hx : |f 0 0-xhat| ≤ ex) (hv : |f 0 1-vhat| ≤ ev)
    (ha : |f 0 2-ahat| ≤ ea)
    (hab : ∀ t ∈ Icc 0 d, |f t 2| ≤ A)
    (hjb : ∀ t ∈ Icc 0 d, |j t| ≤ J) :
    ∀ t ∈ Icc 0 d,
      |f t 0-xhat| ≤ ageX D A ex ev vhat ∧
      |f t 1-vhat| ≤ ageV D A ev ∧
      |f t 2-ahat| ≤ ageA D J ea := by
  have hb := delayed_measurement_box hd hA hJ hev hf hx hv ha hab hjb
  have hD : 0 ≤ D := hd.trans hdD
  have hAd := mul_le_mul_of_nonneg_left hdD hA
  have hJd := mul_le_mul_of_nonneg_left hdD hJ
  have hp := mul_le_mul
    (show |vhat|+ev+A*d ≤ |vhat|+ev+A*D by linarith) hdD hd
    (show 0 ≤ |vhat|+ev+A*D by positivity)
  intro t ht
  obtain ⟨hx',hv',ha'⟩ := hb t ht
  dsimp [ageX,ageV,ageA] at hx' hv' ha' ⊢
  exact ⟨by linarith,by linarith,by linarith⟩

/-- Coordinates of the hold certificate, before selecting its position reference. -/
def rawCoordinates (s : State) : State :=
  ![s 0, s 0+s 1/4, s 0+s 1/2+s 2/16]

def coordinateErrors (X V A : ℝ) : State := ![X, X+V/4, X+V/2+A/16]

theorem coordinate_measurement_bound {s shat : State} {X V A : ℝ}
    (hx : |s 0-shat 0| ≤ X) (hv : |s 1-shat 1| ≤ V)
    (ha : |s 2-shat 2| ≤ A) :
    ∀ i, |rawCoordinates s i-rawCoordinates shat i| ≤ coordinateErrors X V A i := by
  have hxx := abs_le.mp hx
  have hvv := abs_le.mp hv
  have haa := abs_le.mp ha
  intro i
  fin_cases i <;> simp only [rawCoordinates, coordinateErrors, Matrix.cons_val,
    Fin.reduceFinMk] <;> rw [abs_le] <;>
    constructor <;> linarith

/-- A common cube contains the whole measurement box if each transformed
interval fits. This is a directly evaluable test, with no path-safety premise. -/
theorem capture_cube {s shat : State} {X V A c R : ℝ}
    (hx : |s 0-shat 0| ≤ X) (hv : |s 1-shat 1| ≤ V)
    (ha : |s 2-shat 2| ≤ A)
    (hlo : ∀ i, c-R ≤ rawCoordinates shat i-coordinateErrors X V A i)
    (hhi : ∀ i, rawCoordinates shat i+coordinateErrors X V A i ≤ c+R) :
    ∀ i, |rawCoordinates s i-c| ≤ R := by
  intro i
  have h := abs_le.mp (coordinate_measurement_bound hx hv ha i)
  rw [abs_le]
  constructor <;> linarith [hlo i, hhi i]

def exampleReading : State := ![7/50, -1/100, -117/100]
def exampleCenter : ℝ := 141/1600
def exampleRadius : ℝ := 2221/40000

/-- A fixed illustrative noisy reading, after up to 5 ms of command delay, enters
a hold cube wholly inside [0,0.15]. It retains acceleration uncertainty. -/
theorem concrete_capture {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1/200)
    {f : ℝ → State} {j : ℝ → ℝ}
    (hf : IsCaptureTrajectory d f j)
    (hx : |f 0 0-7/50| ≤ 1/1000)
    (hv : |f 0 1-(-1/100)| ≤ 1/100)
    (ha : |f 0 2-(-117/100)| ≤ 1/20)
    (hab : ∀ t ∈ Icc 0 d, |f t 2| ≤ 2)
    (hjb : ∀ t ∈ Icc 0 d, |j t| ≤ 48) :
    (∀ t ∈ Icc 0 d, f t 0 ≤ 3/20) ∧
    (∀ i, |rawCoordinates (f d) i-exampleCenter| ≤ exampleRadius) ∧
    0 ≤ exampleCenter-exampleRadius ∧ exampleCenter+exampleRadius ≤ 3/20 := by
  have hb := bounded_delay_measurement_box (D := 1/200) (A := 2) (J := 48)
    (ex := 1/1000) (ev := 1/100) (ea := 1/20)
    (xhat := 7/50) (vhat := -1/100) (ahat := -117/100)
    hd hdmax (by norm_num) (by norm_num) (by norm_num) hf hx hv ha hab hjb
  have ht : d ∈ Icc 0 d := ⟨hd,le_rfl⟩
  obtain ⟨hxe, hve, hae⟩ := hb d ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have h := (abs_le.mp (hb t ht).1).2
    norm_num [ageX] at h
    linarith
  · apply capture_cube (shat := exampleReading) (X := ageX (1/200) 2 (1/1000) (1/100) (-1/100))
      (V := ageV (1/200) 2 (1/100)) (A := ageA (1/200) 48 (1/20))
    · simpa [exampleReading] using hxe
    · simpa [exampleReading] using hve
    · simpa [exampleReading] using hae
    · intro i; fin_cases i <;>
        norm_num [exampleCenter, exampleRadius, rawCoordinates, exampleReading,
          coordinateErrors, ageX, ageV, ageA]
    · intro i; fin_cases i <;>
        norm_num [exampleCenter, exampleRadius, rawCoordinates, exampleReading,
          coordinateErrors, ageX, ageV, ageA]
  · norm_num [exampleCenter, exampleRadius]
  · norm_num [exampleCenter, exampleRadius]

end LeanControls.SampledCapture
