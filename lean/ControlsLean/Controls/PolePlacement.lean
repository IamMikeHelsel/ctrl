/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ControlsLean.Controls.Hurwitz2

/-!
# State-Feedback Pole Placement, Deadbeat Nilpotence, and Continuous Stabilization

This module formalizes state-feedback control synthesis for canonical second-order linear
systems. While reachability analysis (`ControlsLean.Controls.Reachability`) establishes
the existence of control inputs steering states across subspaces, and stability analysis
(`ControlsLean.Controls.Hurwitz2`, `ControlsLean.Controls.DiscreteLyapunov`) certifies
autonomous decay, state-feedback synthesis actively constructs control laws $u = -K x$
that shape closed-loop dynamics.

### System Formulation
Consider a canonical second-order controllable companion system over a field $K$:
$$\dot{x} = A x + B u \quad \text{or} \quad x_{t+1} = A x_t + B u_t$$
where
$$A = \begin{bmatrix} 0 & 1 \\ -a_0 & -a_1 \end{bmatrix}, \quad
  B = \begin{bmatrix} 0 \\ 1 \end{bmatrix}, \quad
  K = \begin{bmatrix} k_0 & k_1 \end{bmatrix}.$$

The closed-loop matrix under state feedback $u = -K x$ is:
$$A_{cl} = A - B K = \begin{bmatrix} 0 & 1 \\ -(a_0 + k_0) & -(a_1 + k_1) \end{bmatrix}.$$

### Main Results
1. `closedLoop_eq`: Explicit computation of closed-loop matrix $A_{cl} = A - B K$.
2. `closedLoop_mulVec`: Explicit matrix-vector multiplication $(A - B K) x$.
3. `state_feedback_update`: The algebraic equivalence $A x + B (-K x) = (A - B K) x$.
4. `deadbeat_gain`: Choosing $k_0 = -a_0, k_1 = -a_1$ gives shift matrix `!![0, 1; 0, 0]`.
5. `deadbeat_nilpotent`: Deadbeat closed-loop matrix is nilpotent of degree 2: $A_{cl}^2 = 0$.
6. `deadbeat_trajectory_zero`: Every state $x_0$ reaches 0 in 2 steps: $A_{cl}^2 x_0 = 0$.
7. `deadbeat_trajectory_zero_ge`: For all $k \ge 2$, $A_{cl}^k x_0 = 0$.
8. `det_sI_sub_closedLoop`: Characteristic polynomial $\det(s I - A_{cl}) = s^2 + (a_1+k_1)s + (a_0+k_0)$.
9. `pole_placement_charpoly`: Setting $k_0 = d_0-a_0, k_1 = d_1-a_1$ gives $s^2 + d_1 s + d_0$.
10. `hurwitz_stabilization`: Setting $k_0 = d_0-a_0, k_1 = d_1-a_1$ for $d_0, d_1 > 0$ yields
    Hurwitz stability via `isHurwitz2_iff`.
11. `closedLoop_eigenvalues_hurwitz`: Every complex root of $\det(z I - A_{cl})$ has $\mathrm{Re}(z) < 0$.

### References
- Ackermann, J. (1972). *Der Entwurf linearer Regelungssysteme im Zustandsraum*.
  Regelungstechnik und Prozess-Datenverarbeitung 20(7):297–300.
- Åström, K. J., & Murray, R. M. (2021). *Feedback Systems: An Introduction for
  Scientists and Engineers* (2nd ed.). Princeton University Press, Chapter 8.
- Franklin, G. F., Powell, J. D., & Workman, M. L. (1998). *Digital Control of Dynamic
  Systems* (3rd ed.). Addison-Wesley, Chapter 6.
-/

open Matrix

namespace ControlsLean.Controls

variable {K : Type*} [Field K]

/-- Canonical second-order companion matrix in controllable canonical form:
`A = !![0, 1; -a₀, -a₁]`. -/
def canonicalA (a₀ a₁ : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; -a₀, -a₁]

/-- Canonical input matrix for a single control input:
`B = !![0; 1]`. -/
def canonicalB : Matrix (Fin 2) (Fin 1) K :=
  !![0; 1]

/-- State-feedback gain row vector:
`K = !![k₀, k₁]`. -/
def feedbackGain (k₀ k₁ : K) : Matrix (Fin 1) (Fin 2) K :=
  !![k₀, k₁]

/-- The closed-loop state matrix under state feedback `u = -K x`:
`A_cl = A - B * K`. -/
def closedLoop (a₀ a₁ k₀ k₁ : K) : Matrix (Fin 2) (Fin 2) K :=
  canonicalA a₀ a₁ - canonicalB * feedbackGain k₀ k₁

/-- **Closed-Loop System Structure**:
The closed-loop matrix under state feedback has the explicit companion form:
`A_cl = !![0, 1; -(a₀ + k₀), -(a₁ + k₁)]`. -/
theorem closedLoop_eq (a₀ a₁ k₀ k₁ : K) :
    closedLoop a₀ a₁ k₀ k₁ = !![0, 1; -(a₀ + k₀), -(a₁ + k₁)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [closedLoop, canonicalA, canonicalB, feedbackGain] <;> ring

/-- **Closed-Loop Action on States**:
Explicit formula for $(A - B K) x$. -/
theorem closedLoop_mulVec (a₀ a₁ k₀ k₁ : K) (x : Fin 2 → K) :
    closedLoop a₀ a₁ k₀ k₁ *ᵥ x = ![x 1, -(a₀ + k₀) * x 0 - (a₁ + k₁) * x 1] := by
  rw [closedLoop_eq]
  ext i
  fin_cases i
  · simp [mulVec, dotProduct, Fin.sum_univ_two]
  · simp [mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- **State Feedback Dynamics Equivalence**:
The linear combination `A x + B (-K x)` equals `(A - B K) x`. -/
theorem state_feedback_update (a₀ a₁ k₀ k₁ : K) (x : Fin 2 → K) :
    canonicalA a₀ a₁ *ᵥ x + canonicalB *ᵥ (- (feedbackGain k₀ k₁ *ᵥ x)) =
      closedLoop a₀ a₁ k₀ k₁ *ᵥ x := by
  rw [mulVec_neg, ← sub_eq_add_neg, closedLoop, sub_mulVec, mulVec_mulVec]

/-- **Deadbeat Gain Selection**:
Setting `k₀ = -a₀` and `k₁ = -a₁` eliminates the bottom row of the closed-loop matrix,
yielding a pure nilpotent shift matrix `!![0, 1; 0, 0]`. -/
theorem deadbeat_gain (a₀ a₁ : K) :
    closedLoop a₀ a₁ (-a₀) (-a₁) = !![0, 1; 0, 0] := by
  rw [closedLoop_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Deadbeat Nilpotence**:
The closed-loop matrix under deadbeat feedback gains is nilpotent of degree 2:
`(A - B K_db)² = 0`. -/
theorem deadbeat_nilpotent (a₀ a₁ : K) :
    (closedLoop a₀ a₁ (-a₀) (-a₁)) ^ 2 = 0 := by
  rw [deadbeat_gain, sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- **Deadbeat Finite-Time Trajectory Extinction (2 steps)**:
For every initial condition `x₀`, the closed-loop trajectory is driven to exactly zero
in $\dim(V) = 2$ steps: `A_cl² x₀ = 0`. -/
theorem deadbeat_trajectory_zero (a₀ a₁ : K) (x₀ : Fin 2 → K) :
    ((closedLoop a₀ a₁ (-a₀) (-a₁)) ^ 2) *ᵥ x₀ = 0 := by
  rw [deadbeat_nilpotent, zero_mulVec]

/-- **Deadbeat Trajectory Extinction for all $k \ge 2$**:
Once extinguished at step 2, the state remains identically zero for all future time steps. -/
theorem deadbeat_trajectory_zero_ge (a₀ a₁ : K) (x₀ : Fin 2 → K) (k : ℕ) (hk : 2 ≤ k) :
    ((closedLoop a₀ a₁ (-a₀) (-a₁)) ^ k) *ᵥ x₀ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hk
  rw [pow_add, deadbeat_nilpotent, zero_mul, zero_mulVec]

/-- **Closed-Loop Characteristic Polynomial**:
The characteristic polynomial $\det(s I - A_{cl})$ has coefficients directly parameterized
by the sums `a₁ + k₁` and `a₀ + k₀`. -/
theorem det_sI_sub_closedLoop (a₀ a₁ k₀ k₁ s : K) :
    (s • (1 : Matrix (Fin 2) (Fin 2) K) - closedLoop a₀ a₁ k₀ k₁).det =
      s ^ 2 + (a₁ + k₁) * s + (a₀ + k₀) := by
  rw [closedLoop_eq, det_fin_two]
  simp
  ring

/-- **Ackermann Pole Placement Identity**:
For any target polynomial coefficients `d₀, d₁`, choosing feedback gains `k₀ = d₀ - a₀`
and `k₁ = d₁ - a₁` matches the closed-loop characteristic polynomial determinant
identically to `s² + d₁ s + d₀`. -/
theorem pole_placement_charpoly (a₀ a₁ d₀ d₁ s : K) :
    (s • (1 : Matrix (Fin 2) (Fin 2) K) - closedLoop a₀ a₁ (d₀ - a₀) (d₁ - a₁)).det =
      s ^ 2 + d₁ * s + d₀ := by
  rw [det_sI_sub_closedLoop]
  ring

/-- **Hurwitz Continuous-Time Stabilization**:
Continuous-time state-feedback pole placement: for any desired Hurwitz polynomial
`s² + d₁ s + d₀` with `d₀, d₁ > 0`, choosing `k₀ = d₀ - a₀` and `k₁ = d₁ - a₁`
renders the closed-loop system Hurwitz asymptotically stable via `isHurwitz2_iff`. -/
theorem hurwitz_stabilization (a₀ a₁ d₀ d₁ : ℝ) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) :
    IsHurwitz2 (a₁ + (d₁ - a₁)) (a₀ + (d₀ - a₀)) := by
  have h₁ : a₁ + (d₁ - a₁) = d₁ := by ring
  have h₀ : a₀ + (d₀ - a₀) = d₀ := by ring
  rw [h₁, h₀]
  exact (isHurwitz2_iff d₁ d₀).2 ⟨hd₁, hd₀⟩

/-- **Hurwitz Stabilization with Explicit Gain Variables**:
Equivalently, if `k₀ = d₀ - a₀` and `k₁ = d₁ - a₁` with `0 < d₀` and `0 < d₁`,
then `IsHurwitz2 (a₁ + k₁) (a₀ + k₀)`. -/
theorem hurwitz_stabilization_of_gains (a₀ a₁ d₀ d₁ k₀ k₁ : ℝ)
    (hk₀ : k₀ = d₀ - a₀) (hk₁ : k₁ = d₁ - a₁)
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) :
    IsHurwitz2 (a₁ + k₁) (a₀ + k₀) := by
  rw [hk₀, hk₁]
  exact hurwitz_stabilization a₀ a₁ d₀ d₁ hd₀ hd₁

/-- **Closed-Loop Eigenvalue Stability in the Complex Plane**:
Every complex root $z \in \mathbb{C}$ of the characteristic equation $\det(z I - A_{cl}) = 0$
under the synthesized gains has strictly negative real part: $\mathrm{Re}(z) < 0$. -/
theorem closedLoop_eigenvalues_hurwitz (a₀ a₁ d₀ d₁ : ℝ) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (z : ℂ)
    (hz : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      closedLoop (a₀ : ℂ) (a₁ : ℂ) ((d₀ : ℂ) - (a₀ : ℂ)) ((d₁ : ℂ) - (a₁ : ℂ))).det = 0) :
    z.re < 0 := by
  rw [pole_placement_charpoly] at hz
  have h_hurwitz := hurwitz_stabilization a₀ a₁ d₀ d₁ hd₀ hd₁
  have h₁ : a₁ + (d₁ - a₁) = d₁ := by ring
  have h₀ : a₀ + (d₀ - a₀) = d₀ := by ring
  rw [h₁, h₀] at h_hurwitz
  exact h_hurwitz z hz

end ControlsLean.Controls
