module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-! Causal reference admission from bounded jerk and bounded right snap.
Time zero is the arrival of the new request. This file concerns reference
kinematics only. It does not state a tracking or hardware result. -/
@[expose] public section
noncomputable section
namespace CausalAdmission
open Set MeasureTheory Filter
open scoped Topology

def rampTime (J S : ℝ) : ℝ := 2 * J / S
def deadline (a0 J S : ℝ) : ℝ := a0 / J + rampTime J S
def leastJerk (J S t : ℝ) : ℝ := max (J - S * t) (-J)
def leastAccel (a0 J S t : ℝ) : ℝ :=
  a0 + ∫ x in (0 : ℝ)..t, leastJerk J S x
def leastSnap (J S t : ℝ) : ℝ := if t < rampTime J S then -S else 0

/-- Snap is the right derivative of jerk. This permits a finite switch from a
linear jerk ramp to constant jerk. No almost-everywhere regularity is claimed. -/
structure IsAdmissible (a0 J S T : ℝ) (a j s : ℝ → ℝ) : Prop where
  acceleration_continuous : ContinuousOn a (Icc 0 T)
  acceleration_initial : a 0 = a0
  acceleration_derivative : ∀ t ∈ Ioo 0 T, HasDerivAt a (j t) t
  jerk_continuous : ContinuousOn j (Icc 0 T)
  jerk_initial : j 0 = J
  jerk_bound : ∀ t ∈ Icc 0 T, |j t| ≤ J
  snap_derivative : ∀ t ∈ Ico 0 T, HasDerivWithinAt j (s t) (Ici t) t
  snap_bound : ∀ t ∈ Ico 0 T, |s t| ≤ S

theorem leastJerk_continuous (J S : ℝ) : Continuous (leastJerk J S) := by
  unfold leastJerk
  fun_prop

theorem leastJerk_before {J S t : ℝ} (hS : 0 < S)
    (ht : t ≤ rampTime J S) : leastJerk J S t = J - S * t := by
  apply max_eq_left
  have := (le_div_iff₀ hS).mp ht
  nlinarith

theorem leastJerk_after {J S t : ℝ} (hS : 0 < S)
    (ht : rampTime J S ≤ t) : leastJerk J S t = -J := by
  apply max_eq_right
  have := (div_le_iff₀ hS).mp ht
  nlinarith

/-- The lower jerk envelope is derived from the supplied snap derivative.
It is not an assumed integrated inequality. -/
theorem jerk_lower {a0 J S T : ℝ} {a j s : ℝ → ℝ}
    (h : IsAdmissible a0 J S T a j s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    leastJerk J S t ≤ j t := by
  have hb := norm_image_sub_le_of_norm_deriv_right_le_segment
    h.jerk_continuous h.snap_derivative
    (fun x hx => by simpa only [Real.norm_eq_abs] using h.snap_bound x hx) t ht
  rw [Real.norm_eq_abs, h.jerk_initial, sub_zero] at hb
  exact max_le (by linarith [(abs_le.mp hb).1]) (abs_le.mp (h.jerk_bound t ht)).1

theorem leastAccel_before {a0 J S t : ℝ} (hS : 0 < S)
    (ht0 : 0 ≤ t) (ht : t ≤ rampTime J S) :
    leastAccel a0 J S t = a0 + J * t - S * t ^ 2 / 2 := by
  have hi : (∫ x in (0 : ℝ)..t, leastJerk J S x) =
      ∫ x in (0 : ℝ)..t, J - S * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact leastJerk_before hS ((uIcc_of_le ht0 ▸ hx).2.trans ht)
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => J*y-S*y^2/2) (J-S*x) x := by
    convert ((hasDerivAt_id x).const_mul J).sub
      (((hasDerivAt_id x).pow 2).const_mul S |>.div_const 2) using 1
    · ext y
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc (0 : ℝ) t) => hd x)
    (show IntervalIntegrable (fun x : ℝ => J-S*x) volume 0 t from by
      apply Continuous.intervalIntegrable
      fun_prop)
  unfold leastAccel
  rw [hi, hf]
  ring

theorem leastAccel_after {a0 J S t : ℝ} (hJ : 0 < J) (hS : 0 < S)
    (ht : rampTime J S ≤ t) :
    leastAccel a0 J S t = a0 - J * (t - rampTime J S) := by
  have hL : 0 ≤ rampTime J S := by unfold rampTime; positivity
  have hfirst : (∫ x in (0 : ℝ)..rampTime J S, leastJerk J S x) = 0 := by
    have hf := leastAccel_before (a0 := 0) hS hL le_rfl
    dsimp [leastAccel, rampTime] at hf ⊢
    rw [zero_add] at hf
    rw [hf]
    field_simp
    ring
  have hlast : (∫ x in rampTime J S..t, leastJerk J S x) =
      (t - rampTime J S) * (-J) := by
    calc
      _ = ∫ x in rampTime J S..t, (-J) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact leastJerk_after hS (uIcc_of_le ht ▸ hx).1
      _ = _ := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((leastJerk_continuous J S).intervalIntegrable (a := 0) (b := rampTime J S))
    ((leastJerk_continuous J S).intervalIntegrable (a := rampTime J S) (b := t))
  unfold leastAccel
  rw [← hsplit, hfirst, hlast]
  ring

/-- Every admissible acceleration lies above the integrated jerk envelope. -/
theorem acceleration_lower {a0 J S T : ℝ} {a j s : ℝ → ℝ}
    (h : IsAdmissible a0 J S T a j s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    leastAccel a0 J S t ≤ a t := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable j volume 0 t :=
    (h.jerk_continuous.mono hsub).intervalIntegrable_of_Icc ht.1
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (h.acceleration_continuous.mono hsub)
    (fun x hx => h.acceleration_derivative x ⟨hx.1, hx.2.trans_le ht.2⟩) hint
  have hmono := intervalIntegral.integral_mono_on ht.1
    ((leastJerk_continuous J S).intervalIntegrable (a := 0) (b := t)) hint
    (fun x hx => jerk_lower h (hsub hx))
  unfold leastAccel
  rw [h.acceleration_initial] at hft
  linarith

/-- With positive initial acceleration and incoming jerk +J, any zero
acceleration endpoint needs the ramp time plus the constant-jerk time. -/
theorem nonpositive_acceleration_deadline {a0 J S T : ℝ} {a j s : ℝ → ℝ}
    (ha0 : 0 < a0) (hJ : 0 < J) (hS : 0 < S) (hT : 0 ≤ T)
    (h : IsAdmissible a0 J S T a j s) (hz : a T ≤ 0) :
    deadline a0 J S + J / S ≤ T := by
  have hlo := (acceleration_lower h ⟨hT, le_rfl⟩).trans hz
  by_cases hTL : T ≤ rampTime J S
  · rw [leastAccel_before hS hT hTL] at hlo
    have hST : S*T ≤ 2*J := by
      have := (le_div_iff₀ hS).mp hTL
      nlinarith
    have := mul_nonneg hT (sub_nonneg.mpr hST)
    nlinarith
  · rw [leastAccel_after hJ hS (le_of_not_ge hTL)] at hlo
    unfold deadline
    have hdiv : a0 / J ≤ T - rampTime J S :=
      (div_le_iff₀ hJ).mpr (by nlinarith)
    linarith

theorem leastAccel_derivative (a0 J S t : ℝ) :
    HasDerivAt (leastAccel a0 J S) (leastJerk J S t) t := by
  have hc := leastJerk_continuous J S
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (a := 0) (b := t))
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  simpa [leastAccel] using! (hasDerivAt_const t a0).add hd

theorem leastJerk_right_derivative {J S : ℝ} (hS : 0 < S) (t : ℝ) :
    HasDerivWithinAt (leastJerk J S) (leastSnap J S t) (Ici t) t := by
  by_cases ht : t < rampTime J S
  · simp only [leastSnap, ite_eq_left ht]
    have hd : HasDerivAt (fun x : ℝ => J - S*x) (-S) t := by
      simpa using! (hasDerivAt_const t J).sub ((hasDerivAt_id t).const_mul S)
    apply HasDerivAt.hasDerivWithinAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact leastJerk_before hS hx.le
  · simp only [leastSnap, ite_eq_right ht]
    apply (hasDerivAt_const t (-J)).hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact leastJerk_after hS ((le_of_not_gt ht).trans hx)
    · exact le_rfl

/-- The lower envelope itself meets every stated motion assumption. -/
theorem least_isAdmissible (a0 T : ℝ) {J S : ℝ} (hJ : 0 < J) (hS : 0 < S) :
    IsAdmissible a0 J S T (leastAccel a0 J S) (leastJerk J S) (leastSnap J S) := by
  constructor
  · exact (continuous_iff_continuousAt.mpr fun t =>
      (leastAccel_derivative a0 J S t).continuousAt).continuousOn
  · simp [leastAccel]
  · intro t _
    exact leastAccel_derivative a0 J S t
  · exact (leastJerk_continuous J S).continuousOn
  · simp [leastJerk, max_eq_left (by linarith : -J ≤ J)]
  · intro t ht
    apply abs_le.mpr
    constructor
    · exact le_max_right _ _
    · apply max_le
      · nlinarith [mul_nonneg hS.le ht.1]
      · linarith
  · intro t _
    exact leastJerk_right_derivative hS t
  · intro t _
    by_cases ht : t < rampTime J S <;> simp [leastSnap, ht, abs_of_pos hS, hS.le]

/-- This proves sharpness for every positive a0, J and S. -/
theorem least_reaches_zero {a0 J S : ℝ} (ha0 : 0 < a0) (hJ : 0 < J) (hS : 0 < S) :
    leastAccel a0 J S (deadline a0 J S) = 0 := by
  have hlate : rampTime J S ≤ deadline a0 J S := by
    unfold deadline
    have : 0 ≤ a0/J := by positivity
    linarith
  rw [leastAccel_after hJ hS hlate]
  unfold deadline
  field_simp
  ring

/-- The original 250 ms deadline cannot remove 2.5 m/s^2 with incoming
jerk +10 m/s^3, |jerk| <= 10 and |right snap| <= 400 m/s^4. -/
theorem original_deadline_impossible {a j s : ℝ → ℝ}
    (h : IsAdmissible (5/2) 10 400 (1/4) a j s) : a (1/4) ≠ 0 := by
  intro hz
  have hf := nonpositive_acceleration_deadline (by norm_num : (0 : ℝ) < 5/2)
    (by norm_num : (0 : ℝ) < 10) (by norm_num : (0 : ℝ) < 400)
    (by norm_num : (0 : ℝ) ≤ 1/4) h hz.le
  norm_num [deadline, rampTime] at hf

theorem exact_earliest_deadline : deadline (5/2) 10 400 = (3/10 : ℝ) := by
  norm_num [deadline, rampTime]

theorem exact_acceleration_residual {a j s : ℝ → ℝ}
    (h : IsAdmissible (5/2) 10 400 (1/4) a j s) : (1/2 : ℝ) ≤ a (1/4) := by
  have hf := acceleration_lower h (t := 1/4) ⟨by norm_num, le_rfl⟩
  rw [leastAccel_after (by norm_num : (0 : ℝ) < 10)
    (by norm_num : (0 : ℝ) < 400) (by norm_num [rampTime])] at hf
  norm_num [rampTime] at hf ⊢
  exact hf

def leastVelocity (v0 a0 J S t : ℝ) : ℝ :=
  v0 + ∫ x in (0 : ℝ)..t, leastAccel a0 J S x

private theorem integral_quadratic (A B C l r : ℝ) :
    (∫ x in l..r, (A + B*x + C*x^2)) =
      A*(r-l) + B*(r^2-l^2)/2 + C*(r^3-l^3)/3 := by
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => A*y+B*y^2/2+C*y^3/3) (A+B*x+C*x^2) x := by
    convert (((hasDerivAt_id x).const_mul A).add
      ((hasDerivAt_pow 2 x).const_mul B |>.div_const 2)).add
      ((hasDerivAt_pow 3 x).const_mul C |>.div_const 3) using 1
    · rfl
    · ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc l r) => hd x)
    (show IntervalIntegrable (fun x : ℝ => A+B*x+C*x^2) volume l r from by
      apply Continuous.intervalIntegrable
      fun_prop)]
  ring

theorem leastVelocity_after {v0 a0 J S t : ℝ} (hJ : 0 < J) (hS : 0 < S)
    (ht : rampTime J S ≤ t) :
    leastVelocity v0 a0 J S t = v0 + a0*t - J*t^2/2 +
      (2*J^2/S)*t - 4*J^3/(3*S^2) := by
  have hL : 0 ≤ rampTime J S := by unfold rampTime; positivity
  have hc : Continuous (leastAccel a0 J S) :=
    continuous_iff_continuousAt.mpr fun x => (leastAccel_derivative a0 J S x).continuousAt
  have hfirst : (∫ x in (0 : ℝ)..rampTime J S, leastAccel a0 J S x) =
      a0*(rampTime J S) + J*(rampTime J S)^2/2 - S*(rampTime J S)^3/6 := by
    calc
      _ = ∫ x in (0 : ℝ)..rampTime J S, (a0+J*x+(-S/2)*x^2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [leastAccel_before hS (uIcc_of_le hL ▸ hx).1 (uIcc_of_le hL ▸ hx).2]
        ring
      _ = _ := by rw [integral_quadratic]; ring
  have hlast : (∫ x in rampTime J S..t, leastAccel a0 J S x) =
      (a0+J*rampTime J S)*(t-rampTime J S) - J*(t^2-(rampTime J S)^2)/2 := by
    calc
      _ = ∫ x in rampTime J S..t, ((a0+J*rampTime J S)+(-J)*x+0*x^2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [leastAccel_after hJ hS (uIcc_of_le ht ▸ hx).1]
        ring
      _ = _ := by rw [integral_quadratic]; ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (a := 0) (b := rampTime J S))
    (hc.intervalIntegrable (a := rampTime J S) (b := t))
  unfold leastVelocity
  rw [← hsplit, hfirst, hlast]
  unfold rampTime
  field_simp
  ring

/-- Integrating the acceleration comparison preserves the lower bound for an
actual classical velocity trajectory with the same initial velocity. -/
theorem velocity_lower {v0 a0 J S T : ℝ} {v a j s : ℝ → ℝ}
    (h : IsAdmissible a0 J S T a j s)
    (hv : ContinuousOn v (Icc 0 T)) (hv0 : v 0 = v0)
    (hvd : ∀ t ∈ Ioo 0 T, HasDerivAt v (a t) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) : leastVelocity v0 a0 J S t ≤ v t := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable a volume 0 t :=
    (h.acceleration_continuous.mono hsub).intervalIntegrable_of_Icc ht.1
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hv.mono hsub) (fun x hx => hvd x ⟨hx.1, hx.2.trans_le ht.2⟩) hint
  have hc : Continuous (leastAccel a0 J S) :=
    continuous_iff_continuousAt.mpr fun x => (leastAccel_derivative a0 J S x).continuousAt
  have hmono := intervalIntegral.integral_mono_on ht.1
    (hc.intervalIntegrable (a := 0) (b := t)) hint
    (fun x hx => acceleration_lower h (hsub hx))
  unfold leastVelocity
  rw [hv0] at hft
  linarith

/-- Even 50 ms extra time cannot preserve the old velocity endpoint 5/8 m/s.
This is a bound on all admissible trajectories, not just the attaining ramp. -/
theorem exact_velocity_residual {v a j s : ℝ → ℝ}
    (h : IsAdmissible (5/2) 10 400 (3/10) a j s)
    (hv : ContinuousOn v (Icc 0 (3/10))) (hv0 : v 0 = 5/16)
    (hvd : ∀ t ∈ Ioo 0 (3/10), HasDerivAt v (a t) t) :
    (31/240 : ℝ) ≤ v (3/10) - 5/8 := by
  have hf := velocity_lower h hv hv0 hvd (t := 3/10) ⟨by norm_num, le_rfl⟩
  rw [leastVelocity_after (by norm_num : (0 : ℝ) < 10)
    (by norm_num : (0 : ℝ) < 400) (by norm_num [rampTime])] at hf
  norm_num at hf
  linarith

end CausalAdmission
