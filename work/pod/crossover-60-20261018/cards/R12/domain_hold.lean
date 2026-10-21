import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section
namespace R12Hold

/-- Four-box density on the first unit interval. -/
theorem density_outer_bound (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 1) :
    0 ≤ x^3/6 ∧ x^3/6 ≤ 2/3 := by
  have h1 := mul_nonneg hx (sq_nonneg x)
  have h2 := mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg x)
  have h3 := mul_nonneg hx (sub_nonneg.mpr hu)
  constructor <;> nlinarith

/-- Four-box density on the second interval; remaining intervals reflect these. -/
theorem density_inner_bound (x : ℝ) (hx : 1 ≤ x) (hu : x ≤ 2) :
    0 ≤ (-3*x^3+12*x^2-12*x+4)/6 ∧
    (-3*x^3+12*x^2-12*x+4)/6 ≤ 2/3 := by
  have h1 := mul_nonneg (sq_nonneg (x-1)) (sub_nonneg.mpr hu)
  have h2 := mul_nonneg (by linarith : 0 ≤ x) (sq_nonneg (x-2))
  constructor <;> nlinarith

theorem derivative_outer_bound (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 1) :
    |x^2/2| ≤ 2/3 := by
  have h := mul_nonneg hx (sub_nonneg.mpr hu)
  rw [abs_of_nonneg (by positivity)]
  nlinarith

theorem derivative_inner_bound (x : ℝ) (hx : 1 ≤ x) (hu : x ≤ 2) :
    |(-3*x^2+8*x-4)/2| ≤ 2/3 := by
  have h1 := mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ 3*x-2)
  have h2 := sq_nonneg (3*x-4)
  rw [abs_le]
  constructor <;> nlinarith

/-- Opposite-signed retained increments: use positivity of the density, not a loose sum. -/
theorem queued_velocity_bound (a b : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 2/3) (hb : 0 ≤ b ∧ b ≤ 2/3) :
    |(1/5:ℝ)*a-(3/10:ℝ)*b| ≤ 1/5 := by
  rw [abs_le]
  constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]

theorem queued_acceleration_bound (a b : ℝ)
    (ha : |a| ≤ 2/3) (hb : |b| ≤ 2/3) :
    |a-(3/2:ℝ)*b| ≤ 5/3 := by
  have h := abs_sub_le a 0 ((3/2:ℝ)*b)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul] at h
  norm_num at h
  linarith

/-- Continuous-time MVT bound for the sampled velocity-lead command. Derivative binding
and envelopes are explicit hypotheses, not claims about floating-point Python evaluation. -/
theorem led_hold_budget (qd vd ad : ℝ → ℝ) (a t : ℝ)
    (ht : a ≤ t) (hage : t-a ≤ 1/1000)
    (hq : ∀ x ∈ Set.Icc a t, HasDerivAt qd (vd x) x)
    (hv : ∀ x ∈ Set.Icc a t, HasDerivAt vd (ad x) x)
    (hs : ∀ x ∈ Set.Icc a t, |vd x| ≤ 1/5)
    (ha : ∀ x ∈ Set.Icc a t, |ad x| ≤ 5/3) :
    |(qd t+(1/10:ℝ)*vd t)-(qd a+(1/10:ℝ)*vd a)| ≤ 11/30000 := by
  have hder : ∀ x ∈ Set.Icc a t,
      HasDerivWithinAt (fun y => qd y+(1/10:ℝ)*vd y)
        (vd x+(1/10:ℝ)*ad x) (Set.Icc a t) x := by
    intro x hx
    exact ((hq x hx).add ((hv x hx).const_mul (1/10))).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico a t, ‖vd x+(1/10:ℝ)*ad x‖ ≤ (11/30:ℝ) := by
    intro x hx
    have hx' : x ∈ Set.Icc a t := ⟨hx.1, le_of_lt hx.2⟩
    have hvb := hs x hx'
    have hab := ha x hx'
    have hsum := abs_add_le (vd x) ((1/10:ℝ)*ad x)
    rw [abs_mul] at hsum
    norm_num at hsum ⊢
    linarith
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hder hb t ⟨ht,le_rfl⟩
  norm_num [Real.norm_eq_abs] at h
  linarith

#print axioms density_outer_bound
#print axioms density_inner_bound
#print axioms derivative_outer_bound
#print axioms derivative_inner_bound
#print axioms queued_velocity_bound
#print axioms queued_acceleration_bound
#print axioms led_hold_budget
end R12Hold
