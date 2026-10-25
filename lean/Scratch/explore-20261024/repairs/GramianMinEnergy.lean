import ControlsLean.Controls.Gramian

namespace ControlsLean.Controls.Repair

open Matrix BigOperators ControlsLean.Controls

variable {n m : ℕ}

/-- Terminal state reached from `x₀ = 0` after `k` steps of `x_{i+1} = A x_i + B u_i`. -/
def reachState (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ)
    (u : Fin k → Fin m → ℝ) : Fin n → ℝ :=
  ∑ i : Fin k, (A ^ (k - 1 - (i : ℕ))) *ᵥ (B *ᵥ u i)

/-- Input energy `∑ᵢ ‖uᵢ‖²`. -/
def energy {k : ℕ} (u : Fin k → Fin m → ℝ) : ℝ := ∑ i : Fin k, u i ⬝ᵥ u i

private lemma dot_transpose_mulVec {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : Fin q → ℝ) (w : Fin p → ℝ) : v ⬝ᵥ (Mᵀ *ᵥ w) = (M *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- Pairing any input with the Gramian input only sees the terminal state. -/
theorem sum_dot_steerControl (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (x₁ : Fin n → ℝ) (u : Fin k → Fin m → ℝ) :
    ∑ i : Fin k, u i ⬝ᵥ steerControl A B k W_inv x₁ i =
      reachState A B k u ⬝ᵥ (W_inv *ᵥ x₁) := by
  unfold reachState steerControl
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dot_transpose_mulVec, dot_transpose_mulVec]

/-- **Minimum-energy steering (discrete time, finite horizon).**
If `W_inv` is a right inverse of the `k`-step Gramian, then among all input sequences `u`
steering `0` to `x₁` in `k` steps, the Gramian input `u*ᵢ = Bᵀ (Aᵀ)^{k-1-i} W⁻¹ x₁` has
minimal energy, and the excess energy is exactly `∑ᵢ ‖uᵢ - u*ᵢ‖²`. -/
theorem energy_eq_add_of_reach (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (hinv : gramian A B k * W_inv = 1)
    (x₁ : Fin n → ℝ) (u : Fin k → Fin m → ℝ) (hu : reachState A B k u = x₁) :
    energy u = energy (steerControl A B k W_inv x₁) +
      energy (u - steerControl A B k W_inv x₁) := by
  set us := steerControl A B k W_inv x₁
  have hs : reachState A B k us = x₁ := gramian_steer A B k W_inv hinv x₁
  have h1 := sum_dot_steerControl A B k W_inv x₁ u
  have h2 := sum_dot_steerControl A B k W_inv x₁ us
  rw [hu] at h1
  rw [hs] at h2
  have horth : ∑ i : Fin k, u i ⬝ᵥ us i = ∑ i : Fin k, us i ⬝ᵥ us i := by rw [h1, h2]
  unfold energy
  simp only [Pi.sub_apply, sub_dotProduct, dotProduct_sub, Finset.sum_sub_distrib,
    dotProduct_comm (us _) (u _), horth]
  ring

theorem energy_nonneg {k : ℕ} (u : Fin k → Fin m → ℝ) : 0 ≤ energy u :=
  Finset.sum_nonneg fun i _ => dotProduct_self_nonneg (u i)

/-- **Minimum-energy property**: `energy u* ≤ energy u` for every steering input `u`. -/
theorem steerControl_min_energy (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (hinv : gramian A B k * W_inv = 1)
    (x₁ : Fin n → ℝ) (u : Fin k → Fin m → ℝ) (hu : reachState A B k u = x₁) :
    energy (steerControl A B k W_inv x₁) ≤ energy u := by
  rw [energy_eq_add_of_reach A B k W_inv hinv x₁ u hu]
  linarith [energy_nonneg (u - steerControl A B k W_inv x₁)]

/-- **Uniqueness of the minimizer**: a steering input with minimal energy equals `u*`. -/
theorem eq_steerControl_of_energy_le (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ)
    (hinv : gramian A B k * W_inv = 1) (x₁ : Fin n → ℝ) (u : Fin k → Fin m → ℝ)
    (hu : reachState A B k u = x₁) (hle : energy u ≤ energy (steerControl A B k W_inv x₁)) :
    u = steerControl A B k W_inv x₁ := by
  have h := energy_eq_add_of_reach A B k W_inv hinv x₁ u hu
  set d := u - steerControl A B k W_inv x₁ with hd
  have hd0 : energy d = 0 := le_antisymm (by linarith) (energy_nonneg d)
  have hall : ∀ i ∈ Finset.univ, d i ⬝ᵥ d i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => dotProduct_self_nonneg (d i)).1 hd0
  have : d = 0 := funext fun i => dotProduct_self_eq_zero.1 (hall i (Finset.mem_univ _))
  exact sub_eq_zero.1 this

/-- The minimal energy equals `x₁ᵀ W⁻¹ x₁` (when `W_inv` is a right inverse of the Gramian). -/
theorem energy_steerControl (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (hinv : gramian A B k * W_inv = 1)
    (x₁ : Fin n → ℝ) :
    energy (steerControl A B k W_inv x₁) = x₁ ⬝ᵥ (W_inv *ᵥ x₁) := by
  unfold energy
  rw [sum_dot_steerControl]
  exact congrArg (· ⬝ᵥ (W_inv *ᵥ x₁)) (gramian_steer A B k W_inv hinv x₁)

end ControlsLean.Controls.Repair
