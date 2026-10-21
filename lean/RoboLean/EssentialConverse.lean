import RoboLean.Epipolar

/-!
# Converse of the Huang–Faugeras constraint

A real `3 × 3` matrix `E` is an essential matrix `[t]× R` (`R ∈ SO(3)`) if and only if it
satisfies the cubic constraint `E Eᵀ E = ½ tr(E Eᵀ) E`. No separate `det E = 0` hypothesis is
needed: the cubic alone implies it (`det_eq_zero_of_cubic`).

The proof avoids the SVD. With `S = E Eᵀ` and `c = ½ tr S`, the cubic gives `S² = c S`, so for
`c ≠ 0` the matrix `1 - S/c` is a symmetric idempotent of trace `1`, hence equals `u uᵀ` for a unit
`u` (`symm_idem_trace_one`). With `t = √c u`, `K = [t]×` satisfies `K Kᵀ = S`, and
`R = Kᵀ E / c ± u vᵀ` (with `1 - EᵀE/c = v vᵀ`) is orthogonal with `K R = E`; the two sign
choices have opposite determinants, so one of them lies in `SO(3)`.

## Main results

* `symm_idem_trace_one`: symmetric idempotent of trace one is `u uᵀ`, `‖u‖ = 1`.
* `mul_transpose_eq_of_cubic`: the cubic gives `E Eᵀ = c (1 - u uᵀ)`.
* `exists_essential_of_cubic`, `essential_iff_cubic`: the characterization.
* `det_eq_zero_of_cubic`.
* `essential_iff_eigen`: `E` essential iff `E Eᵀ U = U diag(s², s², 0)` for an orthogonal `U`.
-/

open Matrix

namespace RoboLean.Epipolar

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

theorem eq_zero_of_mul_transpose_self {A : M3} (h : trace (A * Aᵀ) = 0) : A = 0 := by
  have := (trace_mul_conjTranspose_self_eq_zero_iff (A := A)).mp
  simpa [conjTranspose_eq_transpose_of_trivial] using
    this (by simpa [conjTranspose_eq_transpose_of_trivial] using h)

theorem eq_zero_of_symm_idem_trace {M : M3} (hs : Mᵀ = M) (hi : M * M = M)
    (ht : trace M = 0) : M = 0 := by
  apply eq_zero_of_mul_transpose_self
  rw [hs, hi, ht]

theorem trace_mul_transpose_nonneg (A : M3) : 0 ≤ trace (A * Aᵀ) := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-- A symmetric idempotent `3 × 3` matrix of trace `1` is a rank-one projector `u uᵀ`. -/
theorem symm_idem_trace_one {Q : M3} (hs : Qᵀ = Q) (hi : Q * Q = Q) (ht : trace Q = 1) :
    ∃ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 ∧ Q = vecMulVec u u := by
  have hdiag : ∀ j, Q j j = ∑ k, Q k j * Q k j := by
    intro j
    have := congrFun (congrFun hi j) j
    rw [mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hs k) j
    simp only [transpose_apply] at this
    rw [this]
  have hpos : ∀ j, 0 ≤ Q j j := fun j => by
    rw [hdiag j]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  obtain ⟨j, hj⟩ : ∃ j, 0 < Q j j := by
    by_contra hcon
    push Not at hcon
    have h0 := le_antisymm (hcon 0) (hpos 0)
    have h1 := le_antisymm (hcon 1) (hpos 1)
    have h2 := le_antisymm (hcon 2) (hpos 2)
    simp [trace, Fin.sum_univ_three, h0, h1, h2] at ht
  set a := Q j j
  set q : Fin 3 → ℝ := fun k => Q k j
  have hqq : q ⬝ᵥ q = a := by simp only [dotProduct, q, a]; exact (hdiag j).symm
  have hQq : Q *ᵥ q = q := by
    ext i
    have := congrFun (congrFun hi i) j
    rw [mul_apply] at this
    simpa [mulVec, dotProduct, q] using this
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt hj.le
  have hsa0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  set u := (Real.sqrt a)⁻¹ • q
  have huu : u ⬝ᵥ u = 1 := by
    simp only [u, smul_dotProduct, dotProduct_smul, hqq, smul_eq_mul]
    field_simp
    rw [hsa]
  have hQu : Q *ᵥ u = u := by simp [u, mulVec_smul, hQq]
  have huQ : u ᵥ* Q = u := by
    rw [← hs, vecMul_transpose]; exact hQu
  refine ⟨u, huu, ?_⟩
  have hM := eq_zero_of_symm_idem_trace (M := Q - vecMulVec u u) ?_ ?_ ?_
  · exact sub_eq_zero.mp hM
  · rw [transpose_sub, hs, transpose_vecMulVec]
  · rw [sub_mul, mul_sub, mul_sub, hi, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul_vecMulVec,
      hQu, huQ, huu, one_smul]
    abel
  · rw [trace_sub, ht, trace_vecMulVec, huu, sub_self]


theorem det_add_vecMulVec_neg (A : M3) (u w : Fin 3 → ℝ) :
    (A + vecMulVec u w).det + (A + vecMulVec u (-w)).det = 2 * A.det := by
  simp [det_fin_three, vecMulVec_apply]; ring

theorem transpose_mul_self_symm (E : M3) : (E * Eᵀ)ᵀ = E * Eᵀ := by
  rw [transpose_mul, transpose_transpose]

/-- From the cubic: `E Eᵀ = c (1 - u uᵀ)` for a unit `u`, `c = ½ tr(E Eᵀ)`. -/
theorem mul_transpose_eq_of_cubic {E : M3}
    (h : E * Eᵀ * E = ((1 / 2 : ℝ) * trace (E * Eᵀ)) • E) :
    ∃ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 ∧
      E * Eᵀ = ((1 / 2 : ℝ) * trace (E * Eᵀ)) • (1 - vecMulVec u u) := by
  set c := (1 / 2 : ℝ) * trace (E * Eᵀ) with hc
  rcases eq_or_ne c 0 with h0 | h0
  · have hE : E = 0 := eq_zero_of_mul_transpose_self (by linarith)
    refine ⟨Pi.single 0 1, by simp, ?_⟩
    rw [h0, zero_smul, hE, Matrix.zero_mul]
  set S := E * Eᵀ with hS
  have hSS : S * S = c • S := by
    rw [hS, ← Matrix.mul_assoc, h, smul_mul_assoc]
  obtain ⟨u, hu, hQ⟩ := symm_idem_trace_one (Q := 1 - c⁻¹ • S)
    (by rw [transpose_sub, transpose_one, transpose_smul, hS, transpose_mul_self_symm])
    (by
      rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
        smul_mul_smul_comm, hSS, smul_smul]
      have : c⁻¹ * c⁻¹ * c = c⁻¹ := by field_simp
      rw [this]; abel)
    (by
      rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
      have : trace S = 2 * c := by rw [hc]; ring
      rw [this]; field_simp; norm_num)
  refine ⟨u, hu, ?_⟩
  rw [← hQ, smul_sub, smul_sub, smul_smul, mul_inv_cancel₀ h0, one_smul]
  abel


/-- **Converse of Huang–Faugeras**: any real `3 × 3` matrix satisfying the cubic constraint
is an essential matrix `[t]× R` with `R ∈ SO(3)`. -/
theorem exists_essential_of_cubic {E : M3}
    (h : E * Eᵀ * E = ((1 / 2 : ℝ) * trace (E * Eᵀ)) • E) :
    ∃ t : Fin 3 → ℝ, ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, E = essential R t := by
  set c := (1 / 2 : ℝ) * trace (E * Eᵀ) with hc
  have hc0 : 0 ≤ c := by have := trace_mul_transpose_nonneg E; rw [hc]; linarith
  rcases eq_or_ne c 0 with h0 | h0
  · have hE : E = 0 := eq_zero_of_mul_transpose_self (by linarith)
    refine ⟨0, 1, one_mem _, ?_⟩
    rw [hE, essential, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm h0)
  obtain ⟨u, hu, hS⟩ := mul_transpose_eq_of_cubic h
  rw [← hc] at hS
  -- the second (right) projector from `T = Eᵀ E`
  have hT : Eᵀ * E * (Eᵀ * E) = c • (Eᵀ * E) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, ← Matrix.mul_assoc Eᵀ, Matrix.mul_assoc Eᵀ, h,
      Matrix.mul_smul]
  have hTtr : trace (Eᵀ * E) = 2 * c := by rw [trace_mul_comm, hc]; ring
  obtain ⟨v, hv, hQ'⟩ := symm_idem_trace_one (Q := 1 - c⁻¹ • (Eᵀ * E))
    (by rw [transpose_sub, transpose_one, transpose_smul, transpose_mul, transpose_transpose])
    (by
      rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
        smul_mul_smul_comm, hT, smul_smul]
      have : c⁻¹ * c⁻¹ * c = c⁻¹ := by field_simp
      rw [this]; abel)
    (by
      rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hTtr]
      field_simp; norm_num)
  have hTc : c⁻¹ • (Eᵀ * E) = 1 - vecMulVec v v := by rw [← hQ']; abel
  -- the translation
  set t := Real.sqrt c • u with ht
  set K := skew t with hK
  have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  have hKK : K * Kᵀ = E * Eᵀ := by
    rw [hK, skew_mul_transpose, hS, ht, smul_dotProduct, dotProduct_smul, hu, smul_vecMulVec,
      vecMulVec_smul, smul_smul]
    simp only [smul_smul, hsc, smul_sub, smul_eq_mul, mul_one]
  have hKu : K *ᵥ u = 0 := by
    ext i; fin_cases i <;> simp [hK, ht, skew, mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have huK : u ᵥ* Kᵀ = 0 := by rw [vecMul_transpose, hKu]
  set A := c⁻¹ • (Kᵀ * E) with hA
  have hAdet : A.det = 0 := by
    rw [hA, det_smul, det_mul, det_transpose, hK, det_skew]; ring
  have key : ∀ w : Fin 3 → ℝ, vecMulVec w w = vecMulVec v v →
      A + vecMulVec u w ∈ orthogonalGroup (Fin 3) ℝ ∧ K * (A + vecMulVec u w) = E := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [mem_orthogonalGroup_iff' (Fin 3) ℝ]
      show (A + vecMulVec u w)ᵀ * (A + vecMulVec u w) = 1
      rw [transpose_add, transpose_vecMulVec, hA, transpose_smul, transpose_mul,
        transpose_transpose]
      have p1 : Eᵀ * K * (Kᵀ * E) = c • (Eᵀ * E) := by
        rw [show Eᵀ * K * (Kᵀ * E) = Eᵀ * (K * Kᵀ * E) by simp only [Matrix.mul_assoc], hKK, h,
          Matrix.mul_smul]
      have p2 : Eᵀ * K * vecMulVec u w = 0 := by
        rw [mul_vecMulVec, ← mulVec_mulVec, hKu, mulVec_zero]
        ext; simp [vecMulVec_apply]
      have p3 : vecMulVec w u * (Kᵀ * E) = 0 := by
        rw [vecMulVec_mul, ← vecMul_vecMul, huK, zero_vecMul]
        ext; simp [vecMulVec_apply]
      have p4 : vecMulVec w u * vecMulVec u w = vecMulVec w w := by
        rw [vecMulVec_mul_vecMulVec, hu, one_smul]
      rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_assoc, Matrix.mul_smul, p1, p2,
        p3, p4, hw, smul_zero, add_zero, zero_add, smul_smul]
      have : c⁻¹ * c⁻¹ * c = c⁻¹ := by field_simp
      rw [this, hTc]; abel
    · rw [mul_add, mul_vecMulVec, hKu, hA, Matrix.mul_smul, ← Matrix.mul_assoc, hKK, h,
        smul_smul, inv_mul_cancel₀ h0, one_smul]
      have h1 : vecMulVec (0 : Fin 3 → ℝ) w = 0 := by ext; simp [vecMulVec_apply]
      rw [h1, add_zero]
  have hdetsq : ∀ R ∈ orthogonalGroup (Fin 3) ℝ, R.det = 1 ∨ R.det = -1 := by
    intro R hR
    have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR
    have h2 := congrArg det h1
    rw [det_mul, det_transpose, det_one] at h2
    rcases mul_self_eq_one_iff.mp h2 with h3 | h3 <;> simp [h3]
  obtain ⟨hO1, hE1⟩ := key v rfl
  obtain ⟨hO2, hE2⟩ := key (-v) (by ext i j; simp [vecMulVec_apply])
  have hsum := det_add_vecMulVec_neg A u v
  rw [hAdet, mul_zero] at hsum
  rcases hdetsq _ hO1 with hd | hd
  · exact ⟨t, _, mem_specialOrthogonalGroup_iff.mpr ⟨hO1, hd⟩, hE1.symm⟩
  · exact ⟨t, _, mem_specialOrthogonalGroup_iff.mpr ⟨hO2, by linarith⟩, hE2.symm⟩


/-- **Characterization of essential matrices** by the Huang–Faugeras cubic constraint alone. -/
theorem essential_iff_cubic (E : M3) :
    (∃ t : Fin 3 → ℝ, ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, E = essential R t) ↔
      E * Eᵀ * E = ((1 / 2 : ℝ) * trace (E * Eᵀ)) • E := by
  constructor
  · rintro ⟨t, R, hR, rfl⟩
    exact huang_faugeras (mem_specialOrthogonalGroup_iff.mp hR).1 t
  · exact exists_essential_of_cubic

/-- The cubic constraint alone forces `det E = 0`. -/
theorem det_eq_zero_of_cubic {E : M3}
    (h : E * Eᵀ * E = ((1 / 2 : ℝ) * trace (E * Eᵀ)) • E) : E.det = 0 := by
  obtain ⟨t, R, -, rfl⟩ := exists_essential_of_cubic h
  exact det_essential R t

/-- A symmetric involution (Householder reflection, or `1`) sending `e₂` to a given unit `u`. -/
theorem exists_householder {u : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) :
    ∃ H : M3, Hᵀ = H ∧ H * H = 1 ∧ H *ᵥ Pi.single 2 1 = u := by
  set e : Fin 3 → ℝ := Pi.single 2 1 with he
  by_cases hue : u = e
  · exact ⟨1, transpose_one, Matrix.one_mul 1, by rw [one_mulVec, hue]⟩
  set w := u - e with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hue
  have hww : w ⬝ᵥ w ≠ 0 := fun h => hw0 (dotProduct_self_eq_zero.mp h)
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hww' : w ⬝ᵥ w = -2 * (w ⬝ᵥ e) := by
    simp only [hw, sub_dotProduct, dotProduct_sub, hu, hee, dotProduct_comm e u]; ring
  have hwe : w ⬝ᵥ e ≠ 0 := by intro h; apply hww; rw [hww', h, mul_zero]
  set a := 2 / (w ⬝ᵥ w) with ha
  refine ⟨1 - a • vecMulVec w w, ?_, ?_, ?_⟩
  · rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  · rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
    have : a * a * (w ⬝ᵥ w) = 2 * a := by rw [ha]; field_simp
    rw [this, mul_smul, two_smul]; abel
  · rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
    have : a • (MulOpposite.op (w ⬝ᵥ e) • w) = (-1 : ℝ) • w := by
      rw [op_smul_eq_smul, smul_smul]
      congr 1
      rw [ha, hww']; field_simp
    rw [this, neg_one_smul, sub_neg_eq_add, hw]; abel

/-- **Spectral characterization**: `E` is essential iff `E Eᵀ` has an orthonormal eigenbasis
(the columns of an orthogonal `U`) with eigenvalues `s², s², 0`. -/
theorem essential_iff_eigen (E : M3) :
    (∃ t : Fin 3 → ℝ, ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, E = essential R t) ↔
      ∃ s : ℝ, ∃ U ∈ orthogonalGroup (Fin 3) ℝ,
        E * Eᵀ * U = U * diagonal ![s ^ 2, s ^ 2, 0] := by
  rw [essential_iff_cubic]
  constructor
  · intro h
    set c := (1 / 2 : ℝ) * trace (E * Eᵀ) with hc
    have hc0 : 0 ≤ c := by have := trace_mul_transpose_nonneg E; rw [hc]; linarith
    obtain ⟨u, hu, hS⟩ := mul_transpose_eq_of_cubic h
    rw [← hc] at hS
    obtain ⟨H, hHs, hHH, hHe⟩ := exists_householder hu
    refine ⟨Real.sqrt c, H, ?_, ?_⟩
    · rw [mem_orthogonalGroup_iff' (Fin 3) ℝ]
      show Hᵀ * H = 1
      rw [hHs, hHH]
    · have hD : diagonal ![Real.sqrt c ^ 2, Real.sqrt c ^ 2, 0] =
          c • (1 - vecMulVec (Pi.single 2 1) (Pi.single 2 1)) := by
        rw [Real.sq_sqrt hc0]
        ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply]
      have huH : u ᵥ* H = Pi.single 2 1 := by
        rw [← hHs, vecMul_transpose, ← hHe, mulVec_mulVec, hHH, one_mulVec]
      rw [hD, hS, Matrix.mul_smul, smul_mul_assoc, sub_mul, mul_sub, Matrix.one_mul,
        Matrix.mul_one, vecMulVec_mul, huH, mul_vecMulVec, hHe]
  · rintro ⟨s, U, hU, hEU⟩
    have hU1 : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU
    have hU2 : U * Uᵀ = 1 := (mem_orthogonalGroup_iff (Fin 3) ℝ).mp hU
    set D := diagonal ![s ^ 2, s ^ 2, 0] with hD
    set S := E * Eᵀ with hS
    have hSU : S = U * D * Uᵀ := by
      rw [← hEU, Matrix.mul_assoc, hU2, Matrix.mul_one]
    have htr : trace S = 2 * s ^ 2 := by
      rw [hSU, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hU1, Matrix.mul_one, hD,
        trace_diagonal]
      simp [Fin.sum_univ_three]; ring
    have hDD : D * D = s ^ 2 • D := by
      rw [hD]; ext i j; fin_cases i <;> fin_cases j <;> simp
    have hSS : S * S = s ^ 2 • S := by
      rw [hSU, show U * D * Uᵀ * (U * D * Uᵀ) = U * D * (Uᵀ * U) * D * Uᵀ by
        simp only [Matrix.mul_assoc], hU1, Matrix.mul_one, Matrix.mul_assoc U D D, hDD,
        Matrix.mul_smul, smul_mul_assoc]
    have hSt : Sᵀ = S := transpose_mul_self_symm E
    set F := (S - s ^ 2 • 1) * E with hF
    have hF0 : F = 0 := by
      apply eq_zero_of_mul_transpose_self
      have h1 : (S - s ^ 2 • 1) * S = 0 := by
        rw [sub_mul, hSS, smul_mul_assoc, Matrix.one_mul, sub_self]
      rw [hF, transpose_mul, show (S - s ^ 2 • 1) * E * (Eᵀ * (S - s ^ 2 • 1)ᵀ) =
        (S - s ^ 2 • 1) * S * (S - s ^ 2 • 1)ᵀ by simp only [hS, Matrix.mul_assoc], h1,
        Matrix.zero_mul, trace_zero]
    have hc : (1 / 2 : ℝ) * trace S = s ^ 2 := by rw [htr]; ring
    rw [hc]
    rw [hF, sub_mul, smul_mul_assoc, Matrix.one_mul, sub_eq_zero] at hF0
    exact hF0

end RoboLean.Epipolar
