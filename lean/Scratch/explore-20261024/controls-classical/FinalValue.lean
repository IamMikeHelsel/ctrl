import Mathlib

open Real Filter Topology MeasureTheory Set

namespace ControlsLean.Controls.FinalValue

/-- One-sided Laplace transform on the real axis. -/
noncomputable def laplace (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Ioi 0, exp (-s * t) * f t

lemma integral_exp_neg_mul {s : ℝ} (hs : 0 < s) : ∫ t in Ioi (0 : ℝ), exp (-s * t) = 1 / s := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hs)]; simp only [mul_zero, exp_zero]; field_simp

lemma integrable_exp_mul_bdd {f : ℝ → ℝ} {M s : ℝ} (hs : 0 < s) (hf : Continuous f)
    (hM : ∀ t, |f t| ≤ M) : IntegrableOn (fun t => exp (-s * t) * f t) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0).mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa using hM t)

/-- **Final value theorem (scalar, Abelian direction).** If a bounded continuous signal
converges, `s F(s) → lim f` as `s → 0⁺`. -/
theorem final_value {f : ℝ → ℝ} {L M : ℝ} (hf : Continuous f) (hM : ∀ t, |f t| ≤ M)
    (hL : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun s => s * laplace f s) (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 hL (ε / 2) (by positivity)
  set T := max T₀ 0
  set C := M + |L|
  have hC : 0 ≤ C := by linarith [hM 0, abs_nonneg (f 0), abs_nonneg L]
  set K := C * exp T
  refine ⟨ε / (2 * (K + 1)), by positivity, fun s hs hsd => ?_⟩
  have hs : (0 : ℝ) < s := hs
  rw [Real.dist_eq, sub_zero, abs_of_pos hs] at hsd
  have hI := integral_exp_neg_mul hs
  have hint := integrable_exp_mul_bdd hs hf hM
  have hie : IntegrableOn (fun t => exp (-s * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0
  have hie1 : IntegrableOn (fun t => exp (-(s + 1) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  -- rewrite `s F(s) - L` as `s ∫ e^{-st} (f t - L)`
  have hrw : s * laplace f s - L = s * ∫ t in Ioi 0, exp (-s * t) * (f t - L) := by
    simp_rw [mul_sub]
    rw [integral_sub hint (hie.mul_const L), integral_mul_const, hI, laplace]
    field_simp
  -- pointwise bound
  have hbd : ∀ t ∈ Ioi (0 : ℝ),
      ‖exp (-s * t) * (f t - L)‖ ≤ (ε / 2) * exp (-s * t) + K * exp (-(s + 1) * t) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have hfl : |f t - L| ≤ C := by
      calc |f t - L| ≤ |f t| + |L| := abs_sub _ _
        _ ≤ C := by linarith [hM t]
    have hK : K * exp (-(s + 1) * t) = exp (-s * t) * (C * exp (T - t)) := by
      have : exp T * exp (-(s + 1) * t) = exp (-s * t) * exp (T - t) := by
        rw [← exp_add, ← exp_add]; ring_nf
      simp only [K]; linear_combination C * this
    rw [hK]
    rcases le_or_gt T t with h | h
    · have := hT₀ t (le_trans (le_max_left _ _) h)
      rw [Real.dist_eq] at this
      have : 0 ≤ C * exp (T - t) := by positivity
      nlinarith [exp_pos (-s * t)]
    · have : C ≤ C * exp (T - t) := le_mul_of_one_le_right hC (one_le_exp (by linarith))
      nlinarith [exp_pos (-s * t), abs_nonneg (f t - L)]
  have hgi : IntegrableOn (fun t => (ε / 2) * exp (-s * t) + K * exp (-(s + 1) * t)) (Ioi 0) :=
    (hie.const_mul _).add (hie1.const_mul _)
  have hnorm := norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall hbd))
  rw [integral_add (hie.const_mul _) (hie1.const_mul _), integral_const_mul, integral_const_mul,
    hI, integral_exp_neg_mul (by linarith : (0 : ℝ) < s + 1)] at hnorm
  rw [Real.dist_eq, hrw, abs_mul, abs_of_pos hs]
  rw [Real.norm_eq_abs] at hnorm
  have hK0 : 0 ≤ K := by positivity
  calc s * |∫ t in Ioi 0, exp (-s * t) * (f t - L)|
      ≤ s * (ε / 2 * (1 / s) + K * (1 / (s + 1))) := mul_le_mul_of_nonneg_left hnorm hs.le
    _ = ε / 2 + s * K / (s + 1) := by field_simp
    _ ≤ ε / 2 + s * K := by
        gcongr; exact div_le_self (by positivity) (by linarith)
    _ < ε := by
        have : s * (K + 1) < ε / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hsd; linarith
        nlinarith

/-- Example: the P-loop trajectory `x* + (x0 - x*) e^{-λt}` has `s X(s) → x*`. -/
example {lam xs x0 : ℝ} (hlam : 0 < lam) :
    Tendsto (fun s => s * laplace (fun t => xs + (x0 - xs) * exp (-lam * |t|)) s)
      (𝓝[>] 0) (𝓝 xs) := by
  refine final_value (M := |xs| + |x0 - xs|) (by fun_prop) (fun t => ?_) ?_
  · have he : exp (-lam * |t|) ≤ 1 := exp_le_one_iff.2 (by nlinarith [abs_nonneg t])
    calc |xs + (x0 - xs) * exp (-lam * |t|)| ≤ |xs| + |(x0 - xs) * exp (-lam * |t|)| :=
          abs_add_le _ _
      _ = |xs| + |x0 - xs| * exp (-lam * |t|) := by rw [abs_mul, abs_of_pos (exp_pos _)]
      _ ≤ |xs| + |x0 - xs| := by
          have := mul_le_of_le_one_right (abs_nonneg (x0 - xs)) he; linarith
  · have : Tendsto (fun t : ℝ => exp (-lam * |t|)) atTop (𝓝 0) := by
      have h1 := tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_abs_atTop_atTop).const_mul_atTop hlam)
      simpa [Function.comp_def, neg_mul] using h1
    simpa using (this.const_mul (x0 - xs)).const_add xs

end ControlsLean.Controls.FinalValue
