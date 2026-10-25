import ControlsLean.Controls.DiscreteLyapunov

open Matrix Filter Topology

namespace ControlsLean.Controls.Repair

open ControlsLean.Controls

variable {n : Type*} [Fintype n] [DecidableEq n] {A P : Matrix n n ℝ}

/-- **Global exponential stability**: there are `M > 0` and `0 ≤ ρ < 1` with
`‖Aᵏ x₀‖² ≤ M ρᵏ ‖x₀‖²` for all `k` and `x₀`. -/
theorem exists_exp_bound (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) :
    ∃ M > 0, ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (k : ℕ) (x₀ : n → ℝ),
      ‖(A ^ k) *ᵥ x₀‖ ^ 2 ≤ M * ρ ^ k * ‖x₀‖ ^ 2 := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_lyapunov_contraction hP hQ
  obtain ⟨c, hc, hcP⟩ := exists_quad_lower hP
  obtain ⟨C, hC, hCP⟩ := exists_quad_upper P
  refine ⟨C / c, div_pos hC hc, ρ, hρ0, hρ1, fun k x₀ => ?_⟩
  have hV : quad P ((A ^ k) *ᵥ x₀) ≤ ρ ^ k * quad P x₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec]
      calc _ ≤ ρ * quad P ((A ^ k) *ᵥ x₀) := hρ _
        _ ≤ ρ * (ρ ^ k * quad P x₀) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * quad P x₀ := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
  calc ‖(A ^ k) *ᵥ x₀‖ ^ 2 * c = c * ‖(A ^ k) *ᵥ x₀‖ ^ 2 := by ring
    _ ≤ quad P ((A ^ k) *ᵥ x₀) := hcP _
    _ ≤ ρ ^ k * quad P x₀ := hV
    _ ≤ ρ ^ k * (C * ‖x₀‖ ^ 2) := by gcongr; exact hCP x₀
    _ = C * ρ ^ k * ‖x₀‖ ^ 2 := by ring

/-- Uniform boundedness: `‖Aᵏ x₀‖ ≤ L ‖x₀‖` for all `k`. -/
theorem exists_uniform_bound (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) :
    ∃ L > 0, ∀ (k : ℕ) (x₀ : n → ℝ), ‖(A ^ k) *ᵥ x₀‖ ≤ L * ‖x₀‖ := by
  obtain ⟨M, hM, ρ, hρ0, hρ1, h⟩ := exists_exp_bound hP hQ
  refine ⟨Real.sqrt M, Real.sqrt_pos.2 hM, fun k x₀ => ?_⟩
  have hk : ‖(A ^ k) *ᵥ x₀‖ ^ 2 ≤ (Real.sqrt M * ‖x₀‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hM.le]
    calc _ ≤ M * ρ ^ k * ‖x₀‖ ^ 2 := h k x₀
      _ ≤ M * 1 * ‖x₀‖ ^ 2 := by gcongr; exact pow_le_one₀ hρ0 hρ1.le
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hk

/-- **Lyapunov stability (ε–δ)** of the origin for `x_{k+1} = A x_k`. -/
theorem lyapunov_stable (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₀ : n → ℝ, ‖x₀‖ < δ → ∀ k : ℕ, ‖(A ^ k) *ᵥ x₀‖ < ε := by
  intro ε hε
  obtain ⟨L, hL, h⟩ := exists_uniform_bound hP hQ
  refine ⟨ε / L, div_pos hε hL, fun x₀ hx k => ?_⟩
  calc ‖(A ^ k) *ᵥ x₀‖ ≤ L * ‖x₀‖ := h k x₀
    _ < L * (ε / L) := by gcongr
    _ = ε := by field_simp

/-- **Discrete-time Lyapunov theorem (full statement)**: the origin is Lyapunov stable and
globally attractive, i.e. globally asymptotically stable. -/
theorem globally_asymptotically_stable (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) :
    (∀ ε > 0, ∃ δ > 0, ∀ x₀ : n → ℝ, ‖x₀‖ < δ → ∀ k : ℕ, ‖(A ^ k) *ᵥ x₀‖ < ε) ∧
      ∀ x₀ : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) atTop (𝓝 0) :=
  ⟨lyapunov_stable hP hQ, tendsto_pow_mulVec_zero hP hQ⟩

end ControlsLean.Controls.Repair
