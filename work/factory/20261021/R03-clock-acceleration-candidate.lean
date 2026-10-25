import Mathlib
set_option maxHeartbeats 400000
namespace Factory
def statement : Prop :=
  ∀ (v c rate : ℝ → ℝ) (a acc V A S R t : ℝ),
    HasDerivAt v a (c t) → HasDerivAt c (rate t) t → HasDerivAt rate acc t →
    |v (c t)| ≤ V → |a| ≤ A → |rate t| ≤ S → |acc| ≤ R →
    0 ≤ V → 0 ≤ A → 0 ≤ S → 0 ≤ R →
    HasDerivAt (fun x => v (c x) * rate x)
      (a * (rate t)^2 + v (c t) * acc) t ∧
    |a * (rate t)^2 + v (c t) * acc| ≤ A * S^2 + V * R
theorem solution : statement := by
  unfold statement
  intro v c rate a acc V A S R t hv hcv hrate hvV haA hrateS haccR hVpos hApos hSpos hRpos
  have hvc : HasDerivAt (fun x => v (c x)) (a * rate t) t := hv.comp t hcv
  have hprod : HasDerivAt (fun x => v (c x) * rate x)
      ((a * rate t) * rate t + v (c t) * acc) t := hvc.mul hrate
  have hderiv : HasDerivAt (fun x => v (c x) * rate x)
      (a * (rate t) ^ 2 + v (c t) * acc) t := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hprod
  have h_abs_le : |a * (rate t) ^ 2 + v (c t) * acc| ≤ A * S ^ 2 + V * R := by
    have h1 : |a * (rate t) ^ 2 + v (c t) * acc| ≤
        |a * (rate t) ^ 2| + |v (c t) * acc| := by
      simpa using abs_add_le (a * (rate t) ^ 2) (v (c t) * acc)
    have h2 : |a * (rate t) ^ 2| ≤ A * S ^ 2 := by
      have h_rate_sq : |rate t| ^ 2 ≤ S ^ 2 := by
        have := mul_le_mul hrateS hrateS (abs_nonneg _) (pow_two_nonneg _)
        simpa [pow_two] using this
      have := mul_le_mul haA h_rate_sq (abs_nonneg _) (pow_two_nonneg _)
      simpa [abs_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    have h3 : |v (c t) * acc| ≤ V * R := by
      simpa [abs_mul] using mul_le_mul hvV haccR (abs_nonneg _) hRpos
    have h4 : |a * (rate t) ^ 2| + |v (c t) * acc| ≤ A * S ^ 2 + V * R :=
      add_le_add h2 h3
    exact le_trans h1 h4
  exact ⟨hderiv, h_abs_le⟩
example : statement := solution
#print axioms solution
end Factory
