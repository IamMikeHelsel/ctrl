import ControlsLean.Controls.Hurwitz2
import ControlsLean.Controls.Jury2
import ControlsLean.Controls.Reachability
import ControlsLean.Controls.PolePlacement
import ControlsLean.Controls.DAREDetectable
import ControlsLean.Controls.BoundedRealHInf

open ControlsLean.Controls Matrix Filter Topology

/-! ## 1. Definitions reject known non-examples -/

/-- Undamped oscillator `ÿ + y = 0` is NOT Hurwitz. -/
example : ¬ IsHurwitz2 0 1 := by
  rw [isHurwitz2_iff]; norm_num

/-- Discrete oscillator `z² + 1` (roots ±i on unit circle) is NOT Schur. -/
example : ¬ IsSchur2 0 1 := by
  rw [isSchur2_iff]; norm_num

/-- Identity matrix is not `IsSchurStable`. -/
example : ¬ IsSchurStable (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have := h ![1, 0]
  simp only [one_pow, one_mulVec] at this
  have h0 := tendsto_nhds_unique this tendsto_const_nhds
  have := congrFun h0 0
  simp at this

/-- Rotation by 90° is not `IsSchurStable` (norm-preserving). -/
example : ¬ IsSchurStable !![(0:ℝ), -1; 1, 0] := by
  intro h
  set R : Matrix (Fin 2) (Fin 2) ℝ := !![(0:ℝ), -1; 1, 0]
  have hR4 : R ^ 4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, pow_succ, mul_apply, Fin.sum_univ_two]
  have hsub := (h ![1, 0]).comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 4))
  have : (fun k : ℕ => (R ^ (4 * k)) *ᵥ ![1, 0]) = fun _ => ![1, 0] := by
    funext k; rw [pow_mul, hR4, one_pow, one_mulVec]
  have h' : Tendsto (fun _ : ℕ => (![1, 0] : Fin 2 → ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, this] using hsub
  have h0 := tendsto_nhds_unique tendsto_const_nhds h'
  have := congrFun h0 0
  simp at this

/-- An uncontrollable pair `(A,B) = (I, e₀)` in ℝ² fails `Controllable`. -/
example : ¬ Controllable (Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (Matrix.toLin' (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)) := by
  rw [controllable_iff_forall_exists, Matrix.toLin'_one]
  intro h
  obtain ⟨k, u, hk⟩ := h ![0, 1]
  have key : ∀ k, traj (LinearMap.id)
      (Matrix.toLin' (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)) 0 u k 1 = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [traj_succ, LinearMap.id_apply, Pi.add_apply, ih]
      simp [mulVec, dotProduct]
  have := key k
  rw [hk] at this
  simp at this

/-! ## 2. `hurwitz_stabilization` (Audit headline) is `isHurwitz2_iff` in disguise:
its statement never mentions any matrix; `a₀,a₁` cancel by `ring`. -/
example (a₀ a₁ d₀ d₁ : ℝ) :
    IsHurwitz2 (a₁ + (d₁ - a₁)) (a₀ + (d₀ - a₀)) ↔ IsHurwitz2 d₁ d₀ := by
  ring_nf

/-! ## 3. Non-degenerate witness for `dare_schur_of_detectable`:
scalar A = 1 (marginally stable, NOT Schur), B = 1, C = 1, R = 2, P = 2.
DARE: P = Q + A²P − (A P B)²/(R + B²P) = 1 + 2 − 4/4 = 2. -/

section DareWitness
abbrev A1 : Matrix (Fin 1) (Fin 1) ℝ := !![1]
abbrev P1 : Matrix (Fin 1) (Fin 1) ℝ := !![2]
abbrev R1 : Matrix (Fin 1) (Fin 1) ℝ := !![2]

lemma inv_four : (!![4] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1/4] := by
  rw [Matrix.inv_eq_left_inv]
  ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num

lemma gain1 : riccatiGain A1 A1 R1 P1 = !![1/2] := by
  unfold riccatiGain lqrHessian
  have : R1 + A1ᵀ * P1 * A1 = !![4] := by
    ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num
  rw [this, inv_four]
  ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num

lemma fix1 : riccatiMap A1 A1 (A1ᵀ * A1) R1 P1 = P1 := by
  unfold riccatiMap
  rw [gain1]
  unfold lqrJosephUpdate lqrClosedLoop
  ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num

lemma sym1 : SymPSD P1 := by
  refine ⟨by ext i j; fin_cases i; fin_cases j; rfl, fun x => ?_⟩
  simp [quad, dotProduct, mulVec, P1]; nlinarith [sq_nonneg (x 0)]

lemma posR1 : R1.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by ext i j; fin_cases i; fin_cases j; rfl, fun x hx => ?_⟩
  have : x 0 ≠ 0 := fun h => hx (by ext i; fin_cases i; exact h)
  simp [dotProduct, mulVec, R1]; have := mul_self_pos.2 this; nlinarith

lemma det1 : IsDetectable A1 A1 := by
  refine ⟨!![1], fun x => ?_⟩
  have : A1 - !![1] * A1 = 0 := by ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num
  rw [this]
  refine tendsto_atTop_of_eventually_const (i₀ := 1) fun k hk => ?_
  rw [zero_pow (by omega), zero_mulVec]

/-- The theorem fires on a system whose open loop is not Schur. -/
example : IsSchurStable (lqrClosedLoop A1 A1 (riccatiGain A1 A1 R1 P1)) :=
  dare_schur_of_detectable posR1 sym1 det1 fix1

example : ¬ IsSchurStable A1 := by
  intro h
  have := h ![1]
  have hA : ∀ k, A1 ^ k = 1 := fun k => by
    have : A1 = 1 := by ext i j; fin_cases i; fin_cases j; rfl
    rw [this, one_pow]
  simp only [hA, one_mulVec] at this
  have := congrFun (tendsto_nhds_unique this tendsto_const_nhds) 0
  simp at this

/-- The "stabilizable/detectable LQG" headline also fires on this instance, but note it
needs `P` and `L` handed in: no existence is proved. -/
example (x₀ xh₀ : Fin 1 → ℝ) : True := by
  have := lqg_closed_loop_stable_of_stabilizable_detectable (Cq := A1)
    (B := A1) (C := A1) (L := !![1]) posR1 sym1 det1 fix1 (by
      have : A1 - !![1] * A1 = 0 := by ext i j; fin_cases i; fin_cases j; (try simp [Matrix.mul_apply, A1, P1, R1]) <;> norm_num
      rw [this]; intro x
      exact tendsto_atTop_of_eventually_const (i₀ := 1) fun k hk => by
        rw [zero_pow (by omega), zero_mulVec])
  trivial

end DareWitness
