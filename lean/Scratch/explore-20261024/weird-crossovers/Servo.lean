import Mathlib

/-! Visual servoing, tracker observability, pan-tilt gimbal controllability. -/

open Matrix

namespace WeirdCrossovers

/-! ## IBVS: `v = -λ L⁺ e` gives `ė = -λ L L⁺ e`. -/

/-- Right pseudo-inverse for full-row-rank `L` (m × n): `L⁺ = Lᵀ (L Lᵀ)⁻¹`. -/
noncomputable def rpinv {m n : ℕ} (L : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Lᵀ * (L * Lᵀ)⁻¹

theorem mul_rpinv {m n : ℕ} (L : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (L * Lᵀ).det) :
    L * rpinv L = 1 := by
  rw [rpinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h]

/-- Full row rank: the closed loop is `ė = -λ e`, so `e(t) = exp(-λ t) e₀` solves it. -/
theorem ibvs_fullrank_solution {m n : ℕ} (L : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (L * Lᵀ).det)
    (lam : ℝ) (e₀ : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-lam * s) • e₀)
      (-lam • (L * rpinv L) *ᵥ (Real.exp (-lam * t) • e₀)) t := by
  rw [mul_rpinv L h, one_mulVec, smul_smul]
  have := ((hasDerivAt_id t).const_mul (-lam)).exp
  simp only [id, mul_one] at this
  have h2 := this.smul_const e₀
  rwa [mul_comm (Real.exp _)] at h2

/-- Exponential decay of the norm. -/
theorem ibvs_decay (lam : ℝ) (e₀ : Fin 2 → ℝ) (t : ℝ) :
    ‖Real.exp (-lam * t) • e₀‖ = Real.exp (-lam * t) * ‖e₀‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Redundant features (2 features, 1 dof): `L = [1;1]` column, `L⁺ = Lᵀ/(LᵀL)`.
Then `e = (1,-1) ≠ 0` gives `L L⁺ e = 0`: an IBVS equilibrium with nonzero error
(local minimum of ‖e‖²). -/
def Lred : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

noncomputable def lpinv (L : Matrix (Fin 2) (Fin 1) ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  (Lᵀ * L)⁻¹ * Lᵀ

theorem ibvs_local_minimum :
    ∃ e : Fin 2 → ℝ, e ≠ 0 ∧ (Lred * lpinv Lred) *ᵥ e = 0 ∧ Lred * lpinv Lred ≠ 1 := by
  refine ⟨![1, -1], ?_, ?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · ext i; fin_cases i <;>
      simp [Lred, lpinv, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have := congrFun (congrFun h 0) 0
    have h2 : (Lredᵀ * Lred) = !![2] := by
      ext i j; fin_cases i; fin_cases j; simp [Lred, Matrix.mul_apply]; norm_num
    simp [lpinv, Lred, Matrix.mul_apply] at this

/-- Any nonzero `e` in `ker Lᵀ` is such an equilibrium (general left-pinv form). -/
theorem ibvs_ker_transpose_equilibrium {m n : ℕ} (L : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ)
    (he : Lᵀ *ᵥ e = 0) : (L * ((Lᵀ * L)⁻¹ * Lᵀ)) *ᵥ e = 0 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, he, mulVec_zero, mulVec_zero]

/-! ## Constant-velocity tracker: observability from position only -/

def Acv (dt : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, dt; 0, 1]

/-- Observability matrix `[C; C A]` for `C = [1, 0]`. -/
def Ocv (dt : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, dt]

theorem Ocv_rows (dt : ℝ) : (Ocv dt) 1 = (Acv dt)ᵀ *ᵥ ![1, 0] := by
  ext j; fin_cases j <;> simp [Ocv, Acv, mulVec, dotProduct, Fin.sum_univ_two]

theorem Ocv_det (dt : ℝ) : (Ocv dt).det = dt := by simp [Ocv, det_fin_two]

theorem Ocv_rank (dt : ℝ) (hdt : dt ≠ 0) : (Ocv dt).rank = 2 := by
  have : IsUnit (Ocv dt).det := by rw [Ocv_det]; exact hdt.isUnit
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 this)]; simp

/-- Velocity-only measurement `C = [0,1]`: unobservable; same translation gauge as 1D SLAM. -/
theorem cv_velocity_only_unobservable (dt : ℝ) (k : ℕ) :
    ((Acv dt) ^ k) *ᵥ ![1, 0] = ![1, 0] ∧ ![(0 : ℝ), 1] ⬝ᵥ (((Acv dt) ^ k) *ᵥ ![1, 0]) = 0 := by
  have hA : Acv dt *ᵥ ![1, 0] = ![1, 0] := by
    ext i; fin_cases i <;> simp [Acv, mulVec, dotProduct, Fin.sum_univ_two]
  have hk : ((Acv dt) ^ k) *ᵥ ![1, 0] = ![1, 0] := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hA, ih]
  exact ⟨hk, by rw [hk]; simp [dotProduct, Fin.sum_univ_two]⟩

/-! ## Pan-tilt gimbal: two decoupled double integrators (pan, pan-rate, tilt, tilt-rate) -/

def Bg : Matrix (Fin 4) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 0; 0, 1]
def Ag : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]

/-- Kalman controllability matrix `[B, A B]` as an explicit 4×4. -/
def Cg : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0]

theorem Cg_cols (i : Fin 4) (j : Fin 2) :
    Cg i (Fin.castAdd 2 j) = Bg i j ∧ Cg i (Fin.natAdd 2 j) = (Ag * Bg) i j := by
  fin_cases i <;> fin_cases j <;> simp [Cg, Ag, Bg, Matrix.mul_apply, Fin.sum_univ_four]

theorem Cg_det : Cg.det = -1 := by
  simp [Cg, det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Cg_rank : Cg.rank = 4 := by
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [Cg_det]; norm_num))]
  simp

end WeirdCrossovers
