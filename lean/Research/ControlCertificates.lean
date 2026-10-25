import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Exploratory control certificate lemmas

AI-assisted work by OpenAI Codex, 2026-10-18. These are explicit mathematical lemmas,
not approved physical-plant challenges or an implementation of a robot controller.
No existing challenge or solution depends on these declarations.
-/

namespace Research.ControlCertificates

/-- A simulation relation transfers an invariant to every step of an actual anchor trace.
The transfer hypothesis must cover EVERY realized anchor successor, including disturbances.
Template progress alone is insufficient. -/
theorem simulation_invariant
    {X Z : Type*} (R : X → Z → Prop) (safeX : X → Prop) (safeZ : Z → Prop)
    (stepX : X → X → Prop) (stepZ : Z → Z → Prop)
    (transfer : ∀ x z x', R x z → safeZ z → stepX x x' →
      ∃ z', stepZ z z' ∧ R x' z')
    (preserve : ∀ z z', safeZ z → stepZ z z' → safeZ z')
    (output : ∀ x z, R x z → safeZ z → safeX x)
    (x : ℕ → X) (z₀ : Z) (initial : R (x 0) z₀) (initialSafe : safeZ z₀)
    (trace : ∀ n, stepX (x n) (x (n + 1))) : ∀ n, safeX (x n) := by
  have lifted : ∀ n, ∃ z, R (x n) z ∧ safeZ z := by
    intro n
    induction n with
    | zero => exact ⟨z₀, initial, initialSafe⟩
    | succ n ih =>
      obtain ⟨z, hr, hs⟩ := ih
      obtain ⟨z', hz', hr'⟩ := transfer (x n) z (x (n + 1)) hr hs (trace n)
      exact ⟨z', hr', preserve z z' hs hz'⟩
  intro n
  obtain ⟨z, hr, hs⟩ := lifted n
  exact output (x n) z hr hs

/-- A scalar barrier loses at most `L * ε` under an already-proved output-error bound.
Deriving this bound from a physical model is a separate obligation. -/
theorem robust_margin (anchor template L ε : ℝ)
    (error : |anchor - template| ≤ L * ε) (margin : L * ε ≤ template) :
    0 ≤ anchor := by
  have := (abs_le.mp error).1
  linarith

/-- Exact robust ENDPOINT feasibility for a held-input scalar double integrator.
`δ` bounds a constant acceleration disturbance over this step. This does not assert
intersample safety, nor that the next state is recursively feasible. -/
theorem endpoint_feasible_iff (q v dt lo hi δ : ℝ)
    (bounds : lo ≤ hi) (uncertainty : 0 ≤ δ) :
    (∃ u : ℝ, lo ≤ u ∧ u ≤ hi ∧
      ∀ d : ℝ, -δ ≤ d → d ≤ δ → 0 ≤ q + dt * v + dt ^ 2 / 2 * (u + d)) ↔
      0 ≤ q + dt * v + dt ^ 2 / 2 * (hi - δ) := by
  have ht : 0 ≤ dt ^ 2 / 2 := by positivity
  constructor
  · rintro ⟨u, _, hu, h⟩
    have hw := h (-δ) (le_refl _) (by linarith)
    have hm := mul_nonneg ht (sub_nonneg.mpr hu)
    nlinarith
  · intro h
    refine ⟨hi, bounds, le_refl _, ?_⟩
    intro d hd _
    have hm := mul_nonneg ht (by linarith : 0 ≤ d + δ)
    nlinarith

/-- Endpoint checks can miss an intersample collision, even with exact dynamics. -/
theorem endpoint_checks_miss_collision :
    (0 : ℝ) ≤ 1 - 6 * 0 + 6 * 0 ^ 2 ∧
    (0 : ℝ) ≤ 1 - 6 * 1 + 6 * 1 ^ 2 ∧
    (1 : ℝ) - 6 * (1 / 2) + 6 * (1 / 2) ^ 2 < 0 := by
  norm_num

/-- Sharp all-time nonnegativity criterion for the constant-braking trajectory.
For a bounded-acceleration plant this is the familiar stopping-distance condition.
This theorem proves the polynomial trajectory property, not ODE existence or model fidelity. -/
theorem braking_safe_iff (q v a : ℝ) (ha : 0 < a) :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ q + t * v + a / 2 * t ^ 2) ↔
      0 ≤ q ∧ (0 ≤ v ∨ v ^ 2 ≤ 2 * a * q) := by
  constructor
  · intro h
    have hq : 0 ≤ q := by simpa using h 0 (le_refl _)
    refine ⟨hq, ?_⟩
    by_cases hv : 0 ≤ v
    · exact Or.inl hv
    · right
      have ht : 0 ≤ -v / a := div_nonneg (by linarith) (le_of_lt ha)
      have hw := h (-v / a) ht
      have hid : 2 * a * (q + (-v / a) * v + a / 2 * (-v / a) ^ 2) =
          2 * a * q - v ^ 2 := by
        field_simp
        ring
      have hm := mul_nonneg (by linarith : 0 ≤ 2 * a) hw
      nlinarith
  · rintro ⟨hq, hv | hv⟩ t ht
    · positivity
    · have hs := sq_nonneg (a * t + v)
      have hid : 2 * a * (q + t * v + a / 2 * t ^ 2) =
          (a * t + v) ^ 2 + (2 * a * q - v ^ 2) := by ring
      have hp : 0 ≤ 2 * a * (q + t * v + a / 2 * t ^ 2) := by nlinarith
      exact nonneg_of_mul_nonneg_right hp (by linarith)

/-- The braking certificate is recursively preserved by the exact maximum-braking step. -/
theorem braking_certificate_preserved (q v a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hv : 0 ≤ v ∨ v ^ 2 ≤ 2 * a * q) :
    0 ≤ q + t * v + a / 2 * t ^ 2 ∧
      (0 ≤ v + a * t ∨ (v + a * t) ^ 2 ≤
        2 * a * (q + t * v + a / 2 * t ^ 2)) := by
  refine ⟨(braking_safe_iff q v a ha).mpr ⟨hq, hv⟩ t ht, ?_⟩
  rcases hv with hv | hv
  · left
    positivity
  · right
    nlinarith

/-- A differentiable scalar signal with nonnegative derivative on nonnegative times
cannot fall below its initial value. -/
theorem initial_le_of_derivative_nonneg (f f' : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ f' t) (t : ℝ) (ht : 0 ≤ t) : f 0 ≤ f t := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hd s (Set.mem_of_mem_of_subset hs interior_subset)).hasDerivWithinAt)
      (fun s hs ↦ hn s (Set.mem_of_mem_of_subset hs interior_subset))
  exact hm (by simp) ht ht

/-- Continuous-time comparison for the actual double-integrator equations.
Every differentiable trajectory whose acceleration is at least `a` stays above
the constant-acceleration polynomial. No sampled approximation is used. -/
theorem acceleration_lower_envelope (q v acc : ℝ → ℝ) (a : ℝ)
    (position : ∀ t, 0 ≤ t → HasDerivAt q (v t) t)
    (velocity : ∀ t, 0 ≤ t → HasDerivAt v (acc t) t)
    (lower : ∀ t, 0 ≤ t → a ≤ acc t) (t : ℝ) (ht : 0 ≤ t) :
    q 0 + t * v 0 + a / 2 * t ^ 2 ≤ q t := by
  have hv : ∀ s, 0 ≤ s → v 0 + a * s ≤ v s := by
    intro s hs
    have h := initial_le_of_derivative_nonneg
      (fun r ↦ v r - a * r) (fun r ↦ acc r - a)
      (fun r hr ↦ by
        convert! (velocity r hr).sub ((hasDerivAt_id r).const_mul a) using 1
        simp)
      (fun r hr ↦ sub_nonneg.mpr (lower r hr)) s hs
    simp only [mul_zero, sub_zero] at h
    linarith
  have hd : ∀ s, 0 ≤ s →
      HasDerivAt (fun r ↦ q r - (q 0 + r * v 0 + a / 2 * r ^ 2))
        (v s - (v 0 + a * s)) s := by
    intro s hs
    convert! (position s hs).sub
      (((hasDerivAt_const s (q 0)).add ((hasDerivAt_id s).mul_const (v 0))).add
        (((hasDerivAt_id s).pow 2).const_mul (a / 2))) using 1
    simp only [id_eq, mul_one, zero_add, Nat.cast_ofNat]
    ring
  have h := initial_le_of_derivative_nonneg
    (fun r ↦ q r - (q 0 + r * v 0 + a / 2 * r ^ 2))
    (fun r ↦ v r - (v 0 + a * r)) hd
    (fun r hr ↦ sub_nonneg.mpr (hv r hr)) t ht
  simp only [zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, sub_self] at h
  nlinarith

/-- Maximum braking `u = U` is safe for every differentiable disturbance realization
bounded below by `-δ`, from the stopping-distance safe set with `U > δ`.
The actual ODEs and input realization appear explicitly as hypotheses. -/
theorem robust_braking_safe (q v d : ℝ → ℝ) (U δ : ℝ) (authority : δ < U)
    (position : ∀ t, 0 ≤ t → HasDerivAt q (v t) t)
    (velocity : ∀ t, 0 ≤ t → HasDerivAt v (U + d t) t)
    (disturbance : ∀ t, 0 ≤ t → -δ ≤ d t)
    (initial : 0 ≤ q 0 ∧ (0 ≤ v 0 ∨ (v 0) ^ 2 ≤ 2 * (U - δ) * q 0)) :
    ∀ t, 0 ≤ t → 0 ≤ q t := by
  intro t ht
  have comparison := acceleration_lower_envelope q v (fun s ↦ U + d s) (U - δ)
    position velocity (fun s hs ↦ by have := disturbance s hs; linarith) t ht
  have safe := (braking_safe_iff (q 0) (v 0) (U - δ) (by linarith)).mpr initial t ht
  linarith

/-- Upper comparison, obtained by negating the lower comparison theorem. -/
theorem acceleration_upper_envelope (q v acc : ℝ → ℝ) (a : ℝ)
    (position : ∀ t, 0 ≤ t → HasDerivAt q (v t) t)
    (velocity : ∀ t, 0 ≤ t → HasDerivAt v (acc t) t)
    (upper : ∀ t, 0 ≤ t → acc t ≤ a) (t : ℝ) (ht : 0 ≤ t) :
    q t ≤ q 0 + t * v 0 + a / 2 * t ^ 2 := by
  have comparison := acceleration_lower_envelope
    (fun s ↦ -q s) (fun s ↦ -v s) (fun s ↦ -acc s) (-a)
    (fun s hs ↦ (position s hs).neg) (fun s hs ↦ (velocity s hs).neg)
    (fun s hs ↦ neg_le_neg (upper s hs)) t ht
  nlinarith

/-- No bounded-input controller can recover a state outside the stopping-distance set
against the admissible constant worst disturbance. This is a trajectory theorem:
classical solutions satisfying the displayed ODEs and input bound must hit `q < 0`.
Together with `robust_braking_safe`, it gives matching sufficiency and necessity. -/
theorem robust_braking_impossible_outside (q v u : ℝ → ℝ) (U δ : ℝ)
    (authority : δ < U)
    (position : ∀ t, 0 ≤ t → HasDerivAt q (v t) t)
    (velocity : ∀ t, 0 ≤ t → HasDerivAt v (u t - δ) t)
    (input : ∀ t, 0 ≤ t → u t ≤ U)
    (outside : ¬ (0 ≤ q 0 ∧ (0 ≤ v 0 ∨ (v 0) ^ 2 ≤ 2 * (U - δ) * q 0))) :
    ∃ t : ℝ, 0 ≤ t ∧ q t < 0 := by
  by_contra h
  push Not at h
  apply outside
  apply (braking_safe_iff (q 0) (v 0) (U - δ) (by linarith)).mp
  intro t ht
  have comparison := acceleration_upper_envelope q v (fun s ↦ u s - δ) (U - δ)
    position velocity (fun s hs ↦ sub_le_sub_right (input s hs) δ) t ht
  exact le_trans (h t ht) comparison

/-- At a fixed task, symmetric actuator headroom is bounded by the centered allocation.
For `u₁+u₂=1`, actuators in `[0,1]`, a radius `r` box around the allocation requires
all four displayed inequalities. The optimum radius is exactly 1/2. -/
theorem fiber_headroom_bound (u₁ u₂ r : ℝ) (task : u₁ + u₂ = 1)
    (h₁ : r ≤ u₁) (h₂ : r ≤ u₂) : r ≤ 1 / 2 := by
  linarith

theorem centered_fiber_certificate :
    (1 / 2 : ℝ) + 1 / 2 = 1 ∧
    ∀ e₁ e₂ : ℝ, |e₁| ≤ 1 / 2 → |e₂| ≤ 1 / 2 →
      0 ≤ 1 / 2 + e₁ ∧ 1 / 2 + e₁ ≤ 1 ∧
      0 ≤ 1 / 2 + e₂ ∧ 1 / 2 + e₂ ≤ 1 := by
  constructor
  · norm_num
  · intro e₁ e₂ h₁ h₂
    obtain ⟨h₁l, h₁u⟩ := abs_le.mp h₁
    obtain ⟨h₂l, h₂u⟩ := abs_le.mp h₂
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> linarith

/-- Internal power cancels only up to its proved residual bound. -/
theorem interconnection_budget (dH₁ dH₂ ext₁ ext₂ loss₁ loss₂ p₁ p₂ ε : ℝ)
    (h₁ : dH₁ ≤ ext₁ + p₁ - loss₁) (h₂ : dH₂ ≤ ext₂ + p₂ - loss₂)
    (port : p₁ + p₂ ≤ ε) :
    dH₁ + dH₂ ≤ ext₁ + ext₂ - (loss₁ + loss₂) + ε := by
  linarith

/-- A safety budget survives arbitrary discrete events only when EACH event is bounded.
An impact/reset can be one of these events; it is not silently treated as a smooth flow. -/
theorem event_budget (H B : ℕ → ℝ) (initial : H 0 ≤ B 0)
    (event : ∀ n, H (n + 1) - H n ≤ B (n + 1) - B n) :
    ∀ n, H n ≤ B n := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih => have := event n; linarith

/-- Feasible endpoint allocations interpolate through any affine inequality.
Apply once per row of a FIXED actuator/contact polytope; changing mode needs new rows. -/
theorem affine_certificate_interpolation (a b u₀ u₁ θ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (h₀ : a * u₀ ≤ b) (h₁ : a * u₁ ≤ b) :
    a * ((1 - θ) * u₀ + θ * u₁) ≤ b := by
  have hleft := mul_nonneg (by linarith : 0 ≤ 1 - θ) (sub_nonneg.mpr h₀)
  have hright := mul_nonneg hθ (sub_nonneg.mpr h₁)
  nlinarith

#print axioms simulation_invariant
#print axioms robust_margin
#print axioms endpoint_feasible_iff
#print axioms endpoint_checks_miss_collision
#print axioms braking_safe_iff
#print axioms braking_certificate_preserved
#print axioms initial_le_of_derivative_nonneg
#print axioms acceleration_lower_envelope
#print axioms robust_braking_safe
#print axioms acceleration_upper_envelope
#print axioms robust_braking_impossible_outside
#print axioms fiber_headroom_bound
#print axioms centered_fiber_certificate
#print axioms interconnection_budget
#print axioms event_budget
#print axioms affine_certificate_interpolation

end Research.ControlCertificates
