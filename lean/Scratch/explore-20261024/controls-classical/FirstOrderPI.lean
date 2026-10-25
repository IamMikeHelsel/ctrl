import ControlsLean.Controls.Hurwitz2
import Mathlib

/-!
Plant `ẋ = -a x + k u + d` (DC gain `k/a`), reference `r`, constant disturbance `d`.
-/

open Real Filter Topology

namespace ControlsLean.Controls.FirstOrderPI

/-- Every solution of `ẋ = -λ (x - x*)` is `x* + (x(0) - x*) e^{-λt}`. -/
theorem linear_ode_unique {x : ℝ → ℝ} {lam xs : ℝ}
    (hx : ∀ t, HasDerivAt x (-lam * (x t - xs)) t) (t : ℝ) :
    x t = xs + (x 0 - xs) * exp (-lam * t) := by
  set g : ℝ → ℝ := fun t => (x t - xs) * exp (lam * t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun t => exp (lam * t)) (exp (lam * t) * lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).exp
    exact (((hx t).sub_const xs).mul he).congr_deriv (by ring)
  have hc : g t = g 0 := is_const_of_deriv_eq_zero
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  simp only [g, mul_zero, exp_zero, mul_one] at hc
  have : exp (-lam * t) * exp (lam * t) = 1 := by rw [← exp_add]; simp
  calc x t = xs + (x t - xs) * exp (lam * t) * exp (-lam * t) := by
        rw [mul_assoc, mul_comm (exp _), this]; ring
    _ = _ := by rw [hc]

theorem linear_ode_tendsto {x : ℝ → ℝ} {lam xs : ℝ} (hlam : 0 < lam)
    (hx : ∀ t, HasDerivAt x (-lam * (x t - xs)) t) : Tendsto x atTop (𝓝 xs) := by
  have h := funext (linear_ode_unique hx)
  rw [h]
  have : Tendsto (fun t => exp (-lam * t)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam)
    simpa [Function.comp_def, neg_mul] using this
  simpa using (this.const_mul (x 0 - xs)).const_add xs

/-- **P control, type-0 plant**: every closed-loop trajectory of
`ẋ = -a x + k K (r - x)` converges, and the steady-state error is `r / (1 + K k/a)`. -/
theorem p_control_steady_state_error {a k K r : ℝ} (ha : 0 < a) (hkK : 0 < k * K)
    {x : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (-a * x t + k * (K * (r - x t))) t) :
    Tendsto (fun t => r - x t) atTop (𝓝 (r / (1 + K * (k / a)))) := by
  have hl : 0 < a + k * K := by linarith
  have hl' : a + k * K ≠ 0 := hl.ne'
  have ha' : a ≠ 0 := ha.ne'
  set xs := k * K * r / (a + k * K)
  have hx' : ∀ t, HasDerivAt x (-(a + k * K) * (x t - xs)) t := by
    intro t; convert hx t using 1; simp only [xs]; field_simp; ring
  have := (linear_ode_tendsto hl hx').const_sub r
  convert this using 2
  have h1 : 1 + K * (k / a) = (a + k * K) / a := by field_simp
  rw [h1, div_div_eq_mul_div, eq_sub_iff_add_eq]
  simp only [xs]; rw [← add_div, div_eq_iff hl']; ring

/-- With a constant disturbance, P control leaves error `(a r - d)/(a + kK)`: it is
zero iff the disturbance happens to equal `a r`. -/
theorem p_control_disturbance_error {a k K r d : ℝ} (ha : 0 < a) (hkK : 0 < k * K)
    {x : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (-a * x t + k * (K * (r - x t)) + d) t) :
    Tendsto (fun t => r - x t) atTop (𝓝 ((a * r - d) / (a + k * K))) := by
  have hl : 0 < a + k * K := by linarith
  have hl' : a + k * K ≠ 0 := hl.ne'
  have ha' : a ≠ 0 := ha.ne'
  set xs := (k * K * r + d) / (a + k * K)
  have hx' : ∀ t, HasDerivAt x (-(a + k * K) * (x t - xs)) t := by
    intro t; convert hx t using 1; simp only [xs]; field_simp; ring
  have := (linear_ode_tendsto hl hx').const_sub r
  convert this using 2
  simp only [xs]; field_simp; ring

/-! ### PI control `u = Kp e + Ki ξ`, `ξ̇ = e = r - x`. -/

/-- PI closed-loop vector field on `(x, ξ)`. -/
def piField (a k d r Kp Ki : ℝ) (x ξ : ℝ) : ℝ × ℝ :=
  (-a * x + k * (Kp * (r - x) + Ki * ξ) + d, r - x)

/-- **Integral action**: at *any* equilibrium, the tracking error is zero, whatever
the plant parameters, gains or constant disturbance. -/
theorem pi_equilibrium_zero_error {a k d r Kp Ki x ξ : ℝ}
    (h : piField a k d r Kp Ki x ξ = 0) : r - x = 0 := by
  simpa [piField] using congrArg Prod.snd h

/-- The equilibrium exists (and is unique) when `k Ki ≠ 0`. -/
theorem pi_equilibrium_exists {a k d r Kp Ki : ℝ} (h : k * Ki ≠ 0) :
    ∃! p : ℝ × ℝ, piField a k d r Kp Ki p.1 p.2 = 0 := by
  obtain ⟨hk, hKi⟩ := mul_ne_zero_iff.1 h
  refine ⟨(r, (a * r - d) / (k * Ki)), ?_, ?_⟩
  · simp only [piField, Prod.mk_eq_zero, sub_self, and_true]
    field_simp; ring
  · rintro ⟨x, ξ⟩ hp
    simp only [piField, Prod.mk_eq_zero] at hp
    obtain ⟨h1, h2⟩ := hp
    have hx : x = r := by linarith
    subst hx
    simp only [Prod.mk.injEq, true_and]
    field_simp
    linear_combination h1

/-- Closed-loop characteristic polynomial is `s² + (a + k Kp) s + k Ki`; the
PI loop is Hurwitz iff `a + k Kp > 0` and `k Ki > 0`. -/
theorem pi_charpoly (a k Kp Ki : ℝ) :
    (!![-a - k * Kp, k * Ki; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).charpoly =
      Polynomial.X ^ 2 + Polynomial.C (a + k * Kp) * Polynomial.X +
        Polynomial.C (k * Ki) := by
  rw [Matrix.charpoly_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.trace_fin_two,
    Matrix.det_fin_two]
  simp only [map_sub, map_neg, map_mul, map_add, map_zero, map_one]
  ring

theorem pi_hurwitz_iff (a k Kp Ki : ℝ) :
    IsHurwitz2 (a + k * Kp) (k * Ki) ↔ 0 < a + k * Kp ∧ 0 < k * Ki :=
  isHurwitz2_iff _ _

end ControlsLean.Controls.FirstOrderPI
