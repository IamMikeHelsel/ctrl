import Mathlib

open Real

namespace ControlsLean.Controls.Overshoot

variable {ζ ω : ℝ}

/-- Damped frequency ratio `β = √(1-ζ²)`, so `ω_d = ω β`. -/
noncomputable def β (ζ : ℝ) : ℝ := √(1 - ζ ^ 2)

/-- Unit-step response of `ω² / (s² + 2ζω s + ω²)` (underdamped, zero initial conditions). -/
noncomputable def y (ζ ω t : ℝ) : ℝ :=
  1 - exp (-(ζ * ω) * t) * (cos (ω * β ζ * t) + ζ / β ζ * sin (ω * β ζ * t))

/-- Closed-form derivative of the step response. -/
noncomputable def y' (ζ ω t : ℝ) : ℝ :=
  ω / β ζ * exp (-(ζ * ω) * t) * sin (ω * β ζ * t)

lemma β_pos (h0 : 0 < ζ) (h1 : ζ < 1) : 0 < β ζ := by
  unfold β; apply Real.sqrt_pos.2; nlinarith

lemma β_sq (h0 : 0 < ζ) (h1 : ζ < 1) : β ζ ^ 2 = 1 - ζ ^ 2 := by
  unfold β; rw [Real.sq_sqrt]; nlinarith

lemma y_zero : y ζ ω 0 = 0 := by simp [y]

theorem hasDerivAt_y (h0 : 0 < ζ) (h1 : ζ < 1) (t : ℝ) :
    HasDerivAt (y ζ ω) (y' ζ ω t) t := by
  unfold y y'
  have hb := β_pos h0 h1
  have hb2 := β_sq h0 h1
  set b := β ζ
  have he : HasDerivAt (fun t => exp (-(ζ * ω) * t)) (exp (-(ζ * ω) * t) * (-(ζ * ω))) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(ζ * ω))).exp
  have hc : HasDerivAt (fun t => cos (ω * b * t)) (-sin (ω * b * t) * (ω * b)) t := by
    simpa using ((hasDerivAt_id t).const_mul (ω * b)).cos
  have hs : HasDerivAt (fun t => sin (ω * b * t)) (cos (ω * b * t) * (ω * b)) t := by
    simpa using ((hasDerivAt_id t).const_mul (ω * b)).sin
  have := ((he.mul (hc.add (hs.const_mul (ζ / b)))).const_sub 1)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · simp only [Pi.add_apply]
    field_simp
    linear_combination (ω * sin (ω * t * b)) * hb2
  · simp

/-- The formula really is the step response: `ÿ + 2ζω ẏ + ω² y = ω²`. -/
theorem y_ode (h0 : 0 < ζ) (h1 : ζ < 1) (t : ℝ) :
    HasDerivAt (y' ζ ω)
      (ω ^ 2 - 2 * ζ * ω * y' ζ ω t - ω ^ 2 * y ζ ω t) t := by
  unfold y y'
  have hb := β_pos h0 h1
  have hb2 := β_sq h0 h1
  set b := β ζ
  have he : HasDerivAt (fun t => exp (-(ζ * ω) * t)) (exp (-(ζ * ω) * t) * (-(ζ * ω))) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(ζ * ω))).exp
  have hs : HasDerivAt (fun t => sin (ω * b * t)) (cos (ω * b * t) * (ω * b)) t := by
    simpa using ((hasDerivAt_id t).const_mul (ω * b)).sin
  have := (he.mul hs).const_mul (ω / b)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  swap
  · simp only [Pi.mul_apply]; ring
  · field_simp
    ring

/-- Peak time `T_p = π / ω_d`. -/
noncomputable def Tp (ζ ω : ℝ) : ℝ := π / (ω * β ζ)

lemma y'_Tp (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) : y' ζ ω (Tp ζ ω) = 0 := by
  have hb := β_pos h0 h1
  unfold y' Tp
  rw [mul_div_cancel₀ _ (by positivity)]; simp

/-- **Peak overshoot**: `y(T_p) = 1 + exp(-ζπ/√(1-ζ²))`. -/
theorem y_Tp (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) :
    y ζ ω (Tp ζ ω) = 1 + exp (-(ζ * π / √(1 - ζ ^ 2))) := by
  have hb := β_pos h0 h1
  unfold y Tp
  rw [mul_div_cancel₀ _ (by positivity)]
  simp only [cos_pi, sin_pi, mul_zero, add_zero, mul_neg, mul_one, sub_neg_eq_add]
  congr 2
  unfold β; field_simp

lemma y'_pos (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) {t : ℝ} (ht0 : 0 < t)
    (ht : t < Tp ζ ω) : 0 < y' ζ ω t := by
  have hb := β_pos h0 h1
  unfold y'
  have : ω * β ζ * t < π := by
    unfold Tp at ht; rwa [lt_div_iff₀ (by positivity), mul_comm] at ht
  have := sin_pos_of_pos_of_lt_pi (by positivity) this
  positivity

lemma y'_neg (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) {t : ℝ} (ht0 : Tp ζ ω < t)
    (ht : t < 2 * Tp ζ ω) : y' ζ ω t < 0 := by
  have hb := β_pos h0 h1
  unfold y'
  unfold Tp at ht0 ht
  have hl : π < ω * β ζ * t := by rwa [div_lt_iff₀ (by positivity), mul_comm] at ht0
  have hu : ω * β ζ * t < 2 * π := by
    rw [mul_div_assoc', lt_div_iff₀ (by positivity), mul_comm] at ht; linarith
  have hs : sin (ω * β ζ * t) < 0 := by
    have := sin_pos_of_pos_of_lt_pi (x := ω * β ζ * t - π) (by linarith) (by linarith)
    rw [sin_sub_pi] at this; linarith
  have : 0 < ω / β ζ * exp (-(ζ * ω) * t) := by positivity
  nlinarith

/-- Envelope bound `y(t) ≤ 1 + e^{-ζωt}/β`. -/
lemma y_le_envelope (h0 : 0 < ζ) (h1 : ζ < 1) (t : ℝ) :
    y ζ ω t ≤ 1 + exp (-(ζ * ω) * t) / β ζ := by
  have hb := β_pos h0 h1
  have hb2 := β_sq h0 h1
  unfold y
  set b := β ζ
  set C := cos (ω * b * t)
  set S := sin (ω * b * t)
  have hCS : S ^ 2 + C ^ 2 = 1 := sin_sq_add_cos_sq _
  have hsq : (b * C + ζ * S) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (b * S - ζ * C)]
  have hm : -1 ≤ b * C + ζ * S := by nlinarith
  have key : -(1 / b) ≤ C + ζ / b * S := by
    rw [show C + ζ / b * S = (b * C + ζ * S) / b by field_simp, ← neg_div]
    exact div_le_div_of_nonneg_right hm hb.le
  have he := exp_pos (-(ζ * ω) * t)
  have := mul_le_mul_of_nonneg_left key he.le
  have : exp (-(ζ * ω) * t) / b = exp (-(ζ * ω) * t) * (1 / b) := by ring
  linarith

lemma exp_neg_le_beta (h0 : 0 < ζ) (h1 : ζ < 1) :
    exp (-(ζ * π / β ζ)) ≤ β ζ := by
  have hb := β_pos h0 h1
  have hb2 := β_sq h0 h1
  have hb1 : β ζ ≤ 1 := by nlinarith
  have hx : 0 ≤ ζ * π / β ζ := by positivity
  have h1' : 1 ≤ β ζ * (1 + ζ * π / β ζ) := by
    rw [mul_add, mul_div_cancel₀ _ hb.ne']
    nlinarith [pi_gt_three]
  have h := add_one_le_exp (ζ * π / β ζ)
  rw [exp_neg]
  calc (exp (ζ * π / β ζ))⁻¹ ≤ (1 + ζ * π / β ζ)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
    _ ≤ β ζ := by
        rw [inv_le_iff_one_le_mul₀ (by positivity)]; linarith

/-- **Maximum overshoot**: the first peak is the global maximum of the step response,
`y(t) ≤ 1 + exp(-ζπ/√(1-ζ²))` for all `t ≥ 0`, with equality at `t = T_p`. -/
theorem y_le_peak (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    y ζ ω t ≤ y ζ ω (Tp ζ ω) := by
  have hb := β_pos h0 h1
  have hT : 0 < Tp ζ ω := by unfold Tp; positivity
  have hd : ∀ s, deriv (y ζ ω) s = y' ζ ω s := fun s => (hasDerivAt_y h0 h1 s).deriv
  have hcont : Continuous (y ζ ω) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_y h0 h1 s).continuousAt
  rcases le_or_gt t (Tp ζ ω) with h | h
  · have hm := strictMonoOn_of_deriv_pos (convex_Icc 0 (Tp ζ ω)) hcont.continuousOn
      (fun s hs => by rw [interior_Icc] at hs; rw [hd]; exact y'_pos h0 h1 hω hs.1 hs.2)
    exact hm.monotoneOn ⟨ht, h⟩ ⟨hT.le, le_rfl⟩ h
  rcases le_or_gt t (2 * Tp ζ ω) with h' | h'
  · have hm := strictAntiOn_of_deriv_neg (convex_Icc (Tp ζ ω) (2 * Tp ζ ω)) hcont.continuousOn
      (fun s hs => by rw [interior_Icc] at hs; rw [hd]; exact y'_neg h0 h1 hω hs.1 hs.2)
    exact hm.antitoneOn ⟨le_rfl, by linarith⟩ ⟨h.le, h'⟩ h.le
  · rw [y_Tp h0 h1 hω]
    have hx := exp_neg_le_beta h0 h1
    set x := ζ * π / β ζ
    have h2 : exp (-(ζ * ω) * t) ≤ exp (-x) * exp (-x) := by
      rw [← exp_add, exp_le_exp]
      have : ζ * ω * (2 * Tp ζ ω) = 2 * x := by
        unfold Tp; simp only [x]; field_simp
      nlinarith [mul_lt_mul_of_pos_left h' (by positivity : 0 < ζ * ω)]
    calc y ζ ω t ≤ 1 + exp (-(ζ * ω) * t) / β ζ := y_le_envelope h0 h1 t
      _ ≤ 1 + exp (-x) * exp (-x) / β ζ := by gcongr
      _ ≤ 1 + exp (-x) := by
        rw [mul_div_assoc]
        have : exp (-x) / β ζ ≤ 1 := (div_le_one hb).2 hx
        nlinarith [exp_pos (-x)]
      _ = 1 + exp (-(ζ * π / √(1 - ζ ^ 2))) := rfl

/-- Percent-overshoot formula as a statement about `sup`. -/
theorem overshoot_isGreatest (h0 : 0 < ζ) (h1 : ζ < 1) (hω : 0 < ω) :
    IsGreatest (y ζ ω '' Set.Ici 0) (1 + exp (-(ζ * π / √(1 - ζ ^ 2)))) := by
  have hT : 0 < Tp ζ ω := by unfold Tp; have := β_pos h0 h1; positivity
  refine ⟨⟨Tp ζ ω, hT.le, y_Tp h0 h1 hω⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [← y_Tp h0 h1 hω]; exact y_le_peak h0 h1 hω ht

end ControlsLean.Controls.Overshoot
