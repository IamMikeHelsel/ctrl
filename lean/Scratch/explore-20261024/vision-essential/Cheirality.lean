import ControlsLean.Vision.EightPoint
import Mathlib

/-!
Uniqueness of the essential-matrix decomposition: `[t]ₓ R = [t']ₓ R'` with `R, R'` orthogonal of
the *same determinant* forces `(R', t') = (R, t)` or the twisted pair `(halfTurn t * R, -t)`.
Without the determinant condition there are extra (reflection) solutions: see `reflection_pair`.
-/

open Matrix

namespace ControlsLean.Vision.Explore

variable {K : Type*} [Field K]

noncomputable def halfTurn (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (2 / (t ⬝ᵥ t)) • vecMulVec t t - 1

/-- Householder reflection in the plane `⊥ t`. -/
noncomputable def householder (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  1 - (2 / (t ⬝ᵥ t)) • vecMulVec t t

theorem skew_mul_vecMulVec_self (t u : Fin 3 → K) : skew t * vecMulVec t u = 0 := by
  rw [mul_vecMulVec, skew_mulVec, cross_self]; ext i j; simp [vecMulVec_apply]

theorem skew_mul_halfTurn (t : Fin 3 → K) : skew t * halfTurn t = -skew t := by
  rw [halfTurn, Matrix.mul_sub, Matrix.mul_smul, skew_mul_vecMulVec_self, smul_zero, zero_sub,
    Matrix.mul_one]

theorem skew_mul_householder (t : Fin 3 → K) : skew t * householder t = skew t := by
  rw [householder, Matrix.mul_sub, Matrix.mul_smul, skew_mul_vecMulVec_self, smul_zero, sub_zero,
    Matrix.mul_one]

theorem halfTurn_sq {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : halfTurn t * halfTurn t = 1 := by
  rw [halfTurn, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  have : 2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 * (2 / (t ⬝ᵥ t)) := by field_simp
  rw [this, mul_smul, two_smul]; abel

theorem householder_mul_transpose {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    householder t * (householder t)ᵀ = 1 := by
  rw [householder, transpose_sub, transpose_smul, transpose_vecMulVec, transpose_one, sub_mul,
    mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  have : 2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 * (2 / (t ⬝ᵥ t)) := by field_simp
  rw [this, mul_smul, two_smul]; abel

theorem det_householder {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (householder t).det = -1 := by
  have ht' : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using ht
  simp only [householder, det_fin_three, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three, smul_eq_mul]
  simp only [one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne]
  ring_nf
  field_simp
  ring

/-- **Reflection ambiguity**: if only `R Rᵀ = 1` is assumed (as in `ControlsLean.Vision.essential`,
which allows any `R`), `(householder t * R, t)` is a further decomposition of the same `E`, with
`det` of the opposite sign. So over `O(3)` there are 8 (not 4) sign-normalised decompositions. -/
theorem reflection_pair (t : Fin 3 → K) (R : Matrix (Fin 3) (Fin 3) K) :
    essential (householder t * R) t = essential R t := by
  rw [essential, essential, ← Matrix.mul_assoc, skew_mul_householder]

/-- `[t]ₓ² = t tᵀ - ‖t‖² I`. -/
theorem skew_mul_skew (t : Fin 3 → K) :
    skew t * skew t = vecMulVec t t - (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

/-- Kernel of `M ↦ [t]ₓ M`: such `M` are `t uᵀ`. -/
theorem eq_vecMulVec_of_skew_mul {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (h : skew t * M = 0) : M = vecMulVec t ((t ⬝ᵥ t)⁻¹ • (t ᵥ* M)) := by
  have h2 : skew t * skew t * M = 0 := by rw [Matrix.mul_assoc, h, Matrix.mul_zero]
  rw [skew_mul_skew, sub_mul, smul_mul_assoc, Matrix.one_mul, sub_eq_zero, vecMulVec_mul] at h2
  rw [vecMulVec_smul, h2, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem det_one_add_vecMulVec (t u : Fin 3 → K) :
    (1 + vecMulVec t u).det = 1 + u ⬝ᵥ t := by
  simp [det_fin_three, vecMulVec_apply, dotProduct, Fin.sum_univ_three, one_apply]; ring

/-- Key rigidity: an orthogonal `D` with `det D = 1` fixing `[t]ₓ` from the right is `1`. -/
theorem eq_one_of_skew_mul {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {D : Matrix (Fin 3) (Fin 3) K}
    (hD : D * Dᵀ = 1) (hdet : D.det = 1) (h : skew t * D = skew t) : D = 1 := by
  set u := (t ⬝ᵥ t)⁻¹ • (t ᵥ* (D - 1))
  have hM := eq_vecMulVec_of_skew_mul ht (M := D - 1) (by rw [Matrix.mul_sub, h, Matrix.mul_one,
    sub_self])
  have hDu : D = 1 + vecMulVec t u := by rw [← hM]; abel
  have hut : u ⬝ᵥ t = 0 := by
    have := det_one_add_vecMulVec t u
    rw [← hDu, hdet] at this; linear_combination -this
  have hDD : Dᵀ * D = 1 := mul_eq_one_comm.mp hD
  rw [hDu, transpose_add, transpose_one, transpose_vecMulVec, add_mul, mul_add, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, vecMulVec_mul_vecMulVec] at hDD
  have hv := congrArg (· *ᵥ t) hDD
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hut,
    dotProduct_comm t u] at hv
  have hu0 : (t ⬝ᵥ t) • u = 0 := by
    simpa [smul_dotProduct, hut, op_smul_eq_smul] using hv
  have : u = 0 := by
    rw [← one_smul K u, ← inv_mul_cancel₀ ht, mul_smul, hu0, smul_zero]
  rw [hDu, this]; ext i j; simp [vecMulVec_apply]

theorem eq_or_eq_neg_of_vecMulVec {t t' : Fin 3 → K} (h : vecMulVec t t = vecMulVec t' t') :
    t' = t ∨ t' = -t := by
  have hij : ∀ i j, t i * t j = t' i * t' j := fun i j => by
    simpa [vecMulVec_apply] using congrFun (congrFun h i) j
  by_cases ht : t = 0
  · left
    subst ht
    funext i
    have := hij i i
    simp only [Pi.zero_apply, zero_mul] at this ⊢
    exact mul_self_eq_zero.mp this.symm
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra hc; push Not at hc; exact ht (funext hc)
  have hii := hij i i
  have hsq : (t' i - t i) * (t' i + t i) = 0 := by linear_combination -hii
  rcases mul_eq_zero.mp hsq with h1 | h1
  · left; funext j
    have hj := hij i j
    have : t' i = t i := sub_eq_zero.mp h1
    rw [this] at hj
    exact (mul_left_cancel₀ hi hj).symm
  · right; funext j
    have hj := hij i j
    have : t' i = -t i := eq_neg_of_add_eq_zero_left h1
    rw [this] at hj
    have : t i * t j = t i * (-t' j) := by rw [hj]; ring
    have := mul_left_cancel₀ hi this
    simp only [Pi.neg_apply]
    linear_combination this

theorem det_halfTurn {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (halfTurn t).det = 1 := by
  have ht' : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using ht
  simp only [halfTurn, det_fin_three, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three, smul_eq_mul]
  simp only [one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne]
  ring_nf
  field_simp
  ring

theorem halfTurn_transpose (t : Fin 3 → K) : (halfTurn t)ᵀ = halfTurn t := by
  rw [halfTurn, transpose_sub, transpose_smul, transpose_vecMulVec, transpose_one]

theorem skew_mul_transpose' (t : Fin 3 → K) :
    skew t * (skew t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

/-- Same translation ⇒ same rotation (given equal determinants). -/
theorem eq_of_skew_mul_eq {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {R R' : Matrix (Fin 3) (Fin 3) K}
    (hR : R * Rᵀ = 1) (hR' : R' * R'ᵀ = 1) (hdet : R'.det = R.det)
    (h : skew t * R = skew t * R') : R' = R := by
  have hRR : Rᵀ * R = 1 := mul_eq_one_comm.mp hR
  have hD : skew t * (R' * Rᵀ) = skew t := by
    rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hDD : (R' * Rᵀ) * (R' * Rᵀ)ᵀ = 1 := by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRR,
      Matrix.one_mul, hR']
  have hdetD : (R' * Rᵀ).det = 1 := by
    have := congrArg det hR
    rw [det_mul, det_transpose, det_one] at this
    rw [det_mul, det_transpose, hdet, this]
  have h1 := eq_one_of_skew_mul ht hDD hdetD hD
  calc R' = R' * Rᵀ * R := by rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
    _ = R := by rw [h1, Matrix.one_mul]

/-- **Exactly two decompositions** of a nonzero essential matrix with fixed `‖t‖`-normalisation
up to the twisted pair: if `[t]ₓ R = [t']ₓ R'` with `R, R'` orthogonal of equal determinant,
then `(R', t') = (R, t)` or `(R', t') = (halfTurn t * R, -t)`. Together with `E ↦ -E`
(`t ↦ -t`) this gives the classical four solutions. -/
theorem decomposition_unique (h2 : (2 : K) ≠ 0) {t t' : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0)
    {R R' : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1) (hR' : R' * R'ᵀ = 1)
    (hdet : R'.det = R.det) (h : essential R t = essential R' t') :
    (t' = t ∧ R' = R) ∨ (t' = -t ∧ R' = halfTurn t * R) := by
  have hEE : skew t * (skew t)ᵀ = skew t' * (skew t')ᵀ := by
    have := congrArg (fun E => E * Eᵀ) h
    simp only [essential, transpose_mul, Matrix.mul_assoc] at this
    rwa [← Matrix.mul_assoc R, hR, ← Matrix.mul_assoc R', hR', Matrix.one_mul,
      Matrix.one_mul] at this
  rw [skew_mul_transpose', skew_mul_transpose'] at hEE
  have hs : t ⬝ᵥ t = t' ⬝ᵥ t' := by
    have := congrArg trace hEE
    simp only [trace_sub, trace_smul, trace_one, Fintype.card_fin, trace_vecMulVec,
      smul_eq_mul] at this
    have : (2 : K) * (t ⬝ᵥ t - t' ⬝ᵥ t') = 0 := by push_cast at this; linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  rw [hs] at hEE
  have hv : vecMulVec t t = vecMulVec t' t' := by
    have := congrArg (fun M => (t' ⬝ᵥ t') • (1 : Matrix (Fin 3) (Fin 3) K) - M) hEE
    simpa using this
  rcases eq_or_eq_neg_of_vecMulVec hv with rfl | rfl
  · exact Or.inl ⟨rfl, eq_of_skew_mul_eq ht hR hR' hdet h⟩
  · right
    refine ⟨rfl, ?_⟩
    have hneg : skew (-t) = -skew t := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
    have hR'' : (halfTurn t * R') * (halfTurn t * R')ᵀ = 1 := by
      rw [transpose_mul, halfTurn_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc R', hR',
        Matrix.one_mul, halfTurn_sq ht]
    have hdet'' : (halfTurn t * R').det = R.det := by rw [det_mul, det_halfTurn ht, one_mul, hdet]
    have hE : skew t * R = skew t * (halfTurn t * R') := by
      rw [← Matrix.mul_assoc, skew_mul_halfTurn]
      simpa [essential, hneg] using h
    have := eq_of_skew_mul_eq ht hR hR'' hdet'' hE
    rw [← this, ← Matrix.mul_assoc, halfTurn_sq ht, Matrix.one_mul]

/-! ## Cheirality (H&Z Result 9.19 depth-sign table)

True pose: `λ₂ x₂ = λ₁ R x₁ + t`. A candidate `(R̃, t̃)` reconstructs depths `(μ₁, μ₂)` with
`μ₂ x₂ = μ₁ R̃ x₁ + t̃`. Generic position: `x₂` and `R x₁` linearly independent. -/

section Cheirality

variable {R : Matrix (Fin 3) (Fin 3) ℝ} {t x₁ x₂ : Fin 3 → ℝ} {l₁ l₂ μ₁ μ₂ : ℝ}

theorem halfTurn_mulVec (s y : Fin 3 → ℝ) :
    halfTurn s *ᵥ y = ((2 / (s ⬝ᵥ s)) * (s ⬝ᵥ y)) • s - y := by
  rw [halfTurn, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

/-- Generic position also makes `R x₁` and `t` independent (baseline not along the ray). -/
theorem indep_ray_baseline (hind : LinearIndependent ℝ ![x₂, R *ᵥ x₁]) (hl₂ : l₂ ≠ 0)
    (h : l₂ • x₂ = l₁ • (R *ᵥ x₁) + t) : LinearIndependent ℝ ![R *ᵥ x₁, t] := by
  rw [LinearIndependent.pair_iff] at hind ⊢
  intro a b hab
  have ht : t = l₂ • x₂ - l₁ • (R *ᵥ x₁) := by rw [h]; abel
  rw [ht] at hab
  have := hind (b * l₂) (a - b * l₁) (by rw [← hab]; module)
  obtain ⟨h1, h2⟩ := this
  have hb : b = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hl₂
  subst hb; simp at h2; exact ⟨h2, rfl⟩

/-- Same rotation, baseline scaled by `ε`: depths scale by `ε`. -/
theorem depths_scaled (hind : LinearIndependent ℝ ![x₂, R *ᵥ x₁])
    (h : l₂ • x₂ = l₁ • (R *ᵥ x₁) + t) (ε : ℝ) (h' : μ₂ • x₂ = μ₁ • (R *ᵥ x₁) + ε • t) :
    μ₁ = ε * l₁ ∧ μ₂ = ε * l₂ := by
  rw [LinearIndependent.pair_iff] at hind
  obtain ⟨h1, h2⟩ := hind (μ₂ - ε * l₂) (ε * l₁ - μ₁)
    (by linear_combination (norm := module) h' - ε • h)
  exact ⟨by linarith, by linarith⟩

/-- Rotation twisted by any `H` with `H (R x₁) = k t - R x₁` (e.g. `halfTurn t`), baseline `ε t`
with `ε ≠ 0`: every reconstruction has depths of **opposite sign**. -/
theorem depths_twisted (hind : LinearIndependent ℝ ![x₂, R *ᵥ x₁]) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (h : l₂ • x₂ = l₁ • (R *ᵥ x₁) + t) {H : Matrix (Fin 3) (Fin 3) ℝ} {k : ℝ}
    (hH : H *ᵥ (R *ᵥ x₁) = k • t - R *ᵥ x₁) {ε : ℝ} (hε : ε ≠ 0)
    (h' : μ₂ • x₂ = μ₁ • ((H * R) *ᵥ x₁) + ε • t) : μ₁ * μ₂ < 0 := by
  have hyt := indep_ray_baseline hind hl₂.ne' h
  rw [LinearIndependent.pair_iff] at hyt
  rw [← mulVec_mulVec, hH] at h'
  obtain ⟨h1, h2⟩ := hyt (μ₂ * l₁ + l₂ * μ₁) (μ₂ - l₂ * μ₁ * k - ε * l₂)
    (by linear_combination (norm := module) l₂ • h' - μ₂ • h)
  have hμ₂ : μ₂ ≠ 0 := by
    intro h0
    have : μ₁ = 0 := by
      rw [h0] at h1
      rcases mul_eq_zero.mp (by linarith : l₂ * μ₁ = 0) with h | h
      · linarith
      · exact h
    rw [h0, this] at h2
    have : ε * l₂ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hε h
    · linarith
  have : μ₁ * μ₂ * l₂ = -(μ₂ ^ 2 * l₁) := by linear_combination μ₂ * h1
  have hp : 0 < μ₂ ^ 2 * l₁ := mul_pos (by positivity) hl₁
  nlinarith

/-- **Depth-sign table** for the four candidates `(R, ±t)`, `(halfTurn t * R, ±t)`. -/
theorem cheirality_table (hind : LinearIndependent ℝ ![x₂, R *ᵥ x₁]) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (h : l₂ • x₂ = l₁ • (R *ᵥ x₁) + t) :
    -- `(R, -t)`: both depths negative
    (∀ μ₁ μ₂ : ℝ, μ₂ • x₂ = μ₁ • (R *ᵥ x₁) + (-t) → μ₁ < 0 ∧ μ₂ < 0) ∧
    -- `(R', t)`: opposite signs
    (∀ μ₁ μ₂ : ℝ, μ₂ • x₂ = μ₁ • ((halfTurn t * R) *ᵥ x₁) + t → μ₁ * μ₂ < 0) ∧
    -- `(R', -t)`: opposite signs
    (∀ μ₁ μ₂ : ℝ, μ₂ • x₂ = μ₁ • ((halfTurn t * R) *ᵥ x₁) + (-t) → μ₁ * μ₂ < 0) := by
  have hH := halfTurn_mulVec t (R *ᵥ x₁)
  refine ⟨fun μ₁ μ₂ h' => ?_, fun μ₁ μ₂ h' => ?_, fun μ₁ μ₂ h' => ?_⟩
  · obtain ⟨e1, e2⟩ := depths_scaled hind h (-1) (by simpa using h')
    constructor <;> linarith
  · exact depths_twisted hind hl₁ hl₂ h hH one_ne_zero (by simpa using h')
  · exact depths_twisted hind hl₁ hl₂ h hH (by norm_num : (-1 : ℝ) ≠ 0) (by simpa using h')

/-- **Exactly one of the four candidates** admits a reconstruction with both depths positive. -/
theorem cheirality_unique (hind : LinearIndependent ℝ ![x₂, R *ᵥ x₁]) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (h : l₂ • x₂ = l₁ • (R *ᵥ x₁) + t) {R₀ : Matrix (Fin 3) (Fin 3) ℝ} {ε : ℝ}
    (hR₀ : R₀ = R ∨ R₀ = halfTurn t * R) (hε : ε = 1 ∨ ε = -1)
    (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (h' : μ₂ • x₂ = μ₁ • (R₀ *ᵥ x₁) + ε • t) :
    R₀ = R ∧ ε = 1 := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  rcases hR₀ with rfl | rfl
  · obtain ⟨e1, -⟩ := depths_scaled hind h ε h'
    refine ⟨rfl, ?_⟩
    rcases hε with rfl | rfl
    · rfl
    · linarith
  · have := depths_twisted hind hl₁ hl₂ h (halfTurn_mulVec t (R *ᵥ x₁)) hε0 h'
    nlinarith

end Cheirality

/-! ## Pose from 8 points + one positive-depth point -/

theorem skew_eq_zero_iff {t : Fin 3 → ℝ} (h : skew t = 0) : t = 0 := by
  have h0 := congrFun (congrFun h 2) 1
  have h1 := congrFun (congrFun h 0) 2
  have h2 := congrFun (congrFun h 1) 0
  simp [skew] at h0 h1 h2
  funext i; fin_cases i <;> simp [h0, h1, h2]

theorem essential_ne_zero {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R * Rᵀ = 1) {t : Fin 3 → ℝ}
    (ht : t ≠ 0) : essential R t ≠ 0 := by
  intro h
  apply ht; apply skew_eq_zero_iff
  have := congrArg (· * Rᵀ) h
  simpa [essential, Matrix.mul_assoc, hR] using this

theorem essential_smul' (R : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (t : Fin 3 → ℝ) :
    c • essential R t = essential R (c • t) := by
  have : skew (c • t) = c • skew t := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  rw [essential, essential, this, smul_mul_assoc]

/-- **Pose from eight points + one positive-depth point.** Data generated by a true pose
`(R, t)` (`R ∈ SO(3)`, `t ≠ 0`) with rank-8 constraint matrix. Any candidate pose `(R₀, t₀)`
(`R₀ ∈ SO(3)`, `t₀ ≠ 0`) whose essential matrix satisfies all epipolar constraints, and which
reconstructs one generic point (seen in front of both true cameras) with positive depths, is the
true pose up to a *positive* scale of `t`. -/
theorem pose_unique {n : ℕ} {R R₀ : Matrix (Fin 3) (Fin 3) ℝ} {t t₀ : Fin 3 → ℝ}
    (hR : R * Rᵀ = 1) (hRd : R.det = 1) (hR₀ : R₀ * R₀ᵀ = 1) (hR₀d : R₀.det = 1)
    (ht : t ≠ 0) (ht₀ : t₀ ≠ 0)
    {x₁ x₂ : Fin n → Fin 3 → ℝ} {d₁ d₂ : Fin n → ℝ} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t)
    (hrank : (constraintMatrix x₁ x₂).rank = 8)
    (hE₀ : ∀ i, x₂ i ⬝ᵥ (essential R₀ t₀ *ᵥ x₁ i) = 0)
    (k : Fin n) (hk : LinearIndependent ℝ ![x₂ k, R *ᵥ x₁ k]) (hd₁k : 0 < d₁ k) (hd₂k : 0 < d₂ k)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hμ : μ₂ • x₂ k = μ₁ • (R₀ *ᵥ x₁ k) + t₀) :
    R₀ = R ∧ ∃ c : ℝ, 0 < c ∧ t₀ = c • t := by
  obtain ⟨c, hc0, hc⟩ := eq_smul_essential R t hd₂ hscene hrank (essential_ne_zero hR ht)
    (essential_ne_zero hR₀ ht₀) hE₀
  rw [essential_smul'] at hc
  have htt : (c • t) ⬝ᵥ (c • t) ≠ 0 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero hc0 (mul_ne_zero hc0 (fun h => ht (dotProduct_self_eq_zero.mp h)))
  have hk' : d₂ k • x₂ k = d₁ k • (R *ᵥ x₁ k) + t := by rw [hscene k, mulVec_smul]
  rcases decomposition_unique two_ne_zero htt hR hR₀ (by rw [hRd, hR₀d]) hc.symm with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h2
    rw [h1] at hμ
    obtain ⟨e1, -⟩ := depths_scaled hk hk' c hμ
    refine ⟨rfl, c, ?_, h1⟩
    by_contra hneg; push Not at hneg
    nlinarith
  · exfalso
    have hH : halfTurn (c • t) *ᵥ (R *ᵥ x₁ k) =
        ((2 / ((c • t) ⬝ᵥ (c • t)) * ((c • t) ⬝ᵥ (R *ᵥ x₁ k))) * c) • t - R *ᵥ x₁ k := by
      rw [halfTurn_mulVec, smul_smul]
    rw [h1, h2, show -(c • t) = (-c) • t by rw [neg_smul]] at hμ
    have := depths_twisted hk hd₁k hd₂k hk' hH (neg_ne_zero.mpr hc0) hμ
    nlinarith

end ControlsLean.Vision.Explore
