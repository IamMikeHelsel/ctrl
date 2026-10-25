import Mathlib

/-!
# Horn 1987: closed-form absolute orientation — the translation step

B. K. P. Horn, "Closed-form solution of absolute orientation using unit quaternions",
J. Opt. Soc. Am. A 4(4), 629–642, 1987, §2.C ("Centroids of the sets of measurements").

For a fixed linear part `R` (any continuous linear map, in particular any rotation, or a
scaled rotation `s R`), the least-squares translation for
`J(t) = Σᵢ ‖R pᵢ + t - qᵢ‖²` is `t⋆ = q̄ - R p̄` (centroid difference), with the exact
"bias–variance" identity `J(t) = J(t⋆) + n ‖t - t⋆‖²`.
We also prove Horn's reduction of the rotation step: for an isometry `R`, after centring,
`J(R, t⋆) = Σ‖p'ᵢ‖² + Σ‖q'ᵢ‖² - 2 Σ ⟪q'ᵢ, R p'ᵢ⟫`, so the optimal rotation maximises the
cross-correlation `Σ ⟪q'ᵢ, R p'ᵢ⟫` (which Horn then solves with the quaternion eigenproblem).
-/

open Finset RealInnerProductSpace

namespace HornCentroid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- Centroid of `n` points. -/
noncomputable def centroid (x : Fin n → E) : E := (n : ℝ)⁻¹ • ∑ i, x i

lemma sum_sub_centroid (hn : 0 < n) (x : Fin n → E) : ∑ i, (x i - centroid x) = 0 := by
  have : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hn.ne')
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, centroid,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, this, one_smul, sub_self]

/-- **Parallel-axis / bias–variance identity.** `Σ‖xᵢ - c‖² = Σ‖xᵢ - x̄‖² + n‖x̄ - c‖²`. -/
theorem sum_norm_sub_sq (hn : 0 < n) (x : Fin n → E) (c : E) :
    ∑ i, ‖x i - c‖ ^ 2 = ∑ i, ‖x i - centroid x‖ ^ 2 + n * ‖centroid x - c‖ ^ 2 := by
  have h : ∀ i, ‖x i - c‖ ^ 2 =
      ‖x i - centroid x‖ ^ 2 + 2 * ⟪x i - centroid x, centroid x - c⟫
        + ‖centroid x - c‖ ^ 2 := fun i => by
    rw [← norm_add_sq_real]; congr 1; abel_nf
  simp_rw [h, sum_add_distrib, ← mul_sum, ← sum_inner, sum_sub_centroid hn, inner_zero_left,
    mul_zero, add_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

variable (R : E →L[ℝ] E) (p q : Fin n → E)

/-- Horn's registration cost for a fixed linear part `R` and translation `t`. -/
noncomputable def cost (t : E) : ℝ := ∑ i, ‖R (p i) + t - q i‖ ^ 2

/-- Horn's optimal translation: difference of centroids. -/
noncomputable def tStar : E := centroid q - R (centroid p)

lemma centroid_map : centroid (fun i => R (p i)) = R (centroid p) := by
  simp [centroid, map_sum, map_smul]

lemma centroid_sub (x y : Fin n → E) : centroid (fun i => x i - y i) = centroid x - centroid y := by
  simp [centroid, sum_sub_distrib, smul_sub]

/-- **Horn 1987, translation step (exact form).** `J(t) = J(t⋆) + n ‖t - t⋆‖²`. -/
theorem cost_eq (hn : 0 < n) (t : E) :
    cost R p q t = cost R p q (tStar R p q) + n * ‖t - tStar R p q‖ ^ 2 := by
  set x : Fin n → E := fun i => q i - R (p i)
  have hx : centroid x = tStar R p q := by
    simp only [x, centroid_sub, centroid_map, tStar]
  have h1 : ∀ s, cost R p q s = ∑ i, ‖x i - s‖ ^ 2 := fun s => by
    unfold cost; congr 1; ext i; rw [← norm_neg]; congr 2; simp only [x]; abel
  rw [h1, h1, sum_norm_sub_sq hn x t, sum_norm_sub_sq hn x (tStar R p q), hx, sub_self,
    norm_zero, norm_sub_rev]
  ring

/-- The centroid difference minimises the cost. -/
theorem cost_tStar_le (hn : 0 < n) (t : E) : cost R p q (tStar R p q) ≤ cost R p q t := by
  rw [cost_eq R p q hn t]; nlinarith [norm_nonneg (t - tStar R p q), (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- … and it is the *unique* minimiser. -/
theorem cost_eq_min_iff (hn : 0 < n) (t : E) :
    cost R p q t = cost R p q (tStar R p q) ↔ t = tStar R p q := by
  rw [cost_eq R p q hn t]
  constructor
  · intro h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : ‖t - tStar R p q‖ ^ 2 = 0 := by
      have := mul_eq_zero.1 (show (n : ℝ) * ‖t - tStar R p q‖ ^ 2 = 0 by linarith)
      exact this.resolve_left hn'.ne'
    simpa [sub_eq_zero] using this
  · rintro rfl; simp

/-- **Horn's reduction of the rotation step.** For a linear isometry `R`, the cost at the
optimal translation depends on `R` only through the cross-correlation of the centred clouds. -/
theorem cost_tStar_isometry (R : E →ₗᵢ[ℝ] E) :
    cost R.toContinuousLinearMap p q (tStar R.toContinuousLinearMap p q) =
      ∑ i, ‖p i - centroid p‖ ^ 2 + ∑ i, ‖q i - centroid q‖ ^ 2
        - 2 * ∑ i, ⟪q i - centroid q, R (p i - centroid p)⟫ := by
  unfold cost tStar
  have h : ∀ i, ‖R.toContinuousLinearMap (p i) + (centroid q - R.toContinuousLinearMap
      (centroid p)) - q i‖ ^ 2 = ‖p i - centroid p‖ ^ 2 + ‖q i - centroid q‖ ^ 2
        - 2 * ⟪q i - centroid q, R (p i - centroid p)⟫ := fun i => by
    have : R.toContinuousLinearMap (p i) + (centroid q - R.toContinuousLinearMap (centroid p))
        - q i = R (p i - centroid p) - (q i - centroid q) := by
      simp [map_sub]; abel
    rw [this, norm_sub_sq_real, LinearIsometry.norm_map, real_inner_comm]; ring
  simp_rw [h, sum_sub_distrib, sum_add_distrib, mul_sum]

end HornCentroid
