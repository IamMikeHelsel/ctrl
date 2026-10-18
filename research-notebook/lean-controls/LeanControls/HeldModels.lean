module

public import LeanControls.Generated.JerkIntegrator
public import LeanControls.Generated.CoupledPlanar
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Held-input ODE semantics for two polynomial benchmarks

The control is calculated from the initial state `z` of a segment and remains
constant while its time argument varies. In particular, the ODE right-hand side
does not recompute feedback from the current segment state. Each explicit
segment has the specified initial condition, satisfies the component ODEs, and
equals the transition independently emitted by the certificate generator.

These results concern normalized nominal exact-real dynamics. They do not yet
add quantization, disturbances, actuator limits, or a global piecewise trajectory.
-/

@[expose] public section
noncomputable section

namespace LeanControls.HeldModels

open Matrix
open BernsteinCertificate

/-- A held acceleration integrates to a quadratic position segment. -/
theorem held_position_derivative (t x v a : ℝ) :
    HasDerivAt (fun s => x + s * v + s ^ 2 / 2 * a) (v + t * a) t := by
  convert (((hasDerivAt_id t).mul_const v).const_add x).add
    ((((hasDerivAt_id t).pow 2).div_const 2).mul_const a) using 1
  · ext s
    simp
  · dsimp
    ring

/-- A held acceleration integrates to a linear velocity segment. -/
theorem held_velocity_derivative (t v a : ℝ) :
    HasDerivAt (fun s => v + s * a) a t := by
  simpa using ((hasDerivAt_id t).mul_const a).const_add v

namespace Jerk

/-- State order: position, velocity, acceleration. -/
abbrev State := Fin 3 → ℝ

/-- The scalar jerk command is sampled once at the segment's initial state. -/
def input (z : State) : ℝ := -z 0 - 3 * z 1 - 3 * z 2

def position (t : ℝ) (z : State) : ℝ :=
  z 0 + t * z 1 + t ^ 2 / 2 * z 2 + t ^ 3 / 6 * input z

def velocity (t : ℝ) (z : State) : ℝ :=
  z 1 + t * z 2 + t ^ 2 / 2 * input z

def acceleration (t : ℝ) (z : State) : ℝ := z 2 + t * input z

def segment (t : ℝ) (z : State) : State :=
  ![position t z, velocity t z, acceleration t z]

/-- Open-loop jerk-integrator vector field with an externally supplied input. -/
def vectorField (u : ℝ) (current : State) : State := ![current 1, current 2, u]

theorem segment_initial (z : State) : segment 0 z = z := by
  ext i
  fin_cases i <;> simp [segment, position, velocity, acceleration]

theorem position_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => position s z) (velocity t z) t := by
  have hp := (held_position_derivative t (z 0) (z 1) (z 2)).add
    ((((hasDerivAt_id t).pow 3).div_const 6).mul_const (input z))
  convert hp using 1
  · ext s
    simp [position]
  · dsimp [velocity]
    ring

theorem velocity_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => velocity s z) (acceleration t z) t := by
  exact held_position_derivative t (z 1) (z 2) (input z)

theorem acceleration_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => acceleration s z) (input z) t := by
  exact held_velocity_derivative t (z 2) (input z)

/-- All three equations use `input z`, the held command from the initial state. -/
theorem segment_ode (t : ℝ) (z : State) (i : Fin 3) :
    HasDerivAt (fun s => segment s z i) (vectorField (input z) (segment t z) i) t := by
  fin_cases i
  · simpa [segment, vectorField] using position_derivative t z
  · simpa [segment, vectorField] using velocity_derivative t z
  · simpa [segment, vectorField] using acceleration_derivative t z

/-- The generated polynomial is the endpoint of the independently defined ODE segment. -/
theorem segment_eq_transition (h : ℝ) (z : State) :
    segment h z = Generated.JerkIntegrator.transition h *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segment, position, velocity, acceleration, input,
      Generated.JerkIntegrator.transition, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.of_apply] <;> ring

/-- The generated certificate therefore applies to the actual held-input segment. -/
theorem segment_energy_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ 1 / 2) (z : State) :
    energy Generated.JerkIntegrator.P (segment h z) ≤
      energy Generated.JerkIntegrator.P z - h * squaredNorm z := by
  rw [segment_eq_transition]
  simpa using Generated.JerkIntegrator.certified_decrease hlo hhi z

/-- The energy stays below its sampled value throughout every permitted segment. -/
theorem intersample_energy {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 2) (z : State) :
    energy Generated.JerkIntegrator.P (segment t z) ≤ energy Generated.JerkIntegrator.P z := by
  have hd := segment_energy_decrease ht0 hthi z
  have hn : 0 ≤ squaredNorm z := Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  exact hd.trans (sub_le_self _ (mul_nonneg ht0 hn))

/-- Sample-index decay also bounds every point within every held segment.
This statement uses an actual held-segment recurrence, not a separately supplied
matrix recurrence. A global real-time coverage theorem is a separate step. -/
theorem sampled_segment_bound (h : ℕ → ℝ) (z : ℕ → State) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 2)
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ 1 / 2)
    (hdyn : ∀ k, z (k + 1) = segment (h k) (z k)) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h n) :
    energy Generated.JerkIntegrator.P (segment t (z n)) ≤
      (1 - hmin / Generated.JerkIntegrator.upperBound) ^ n *
        energy Generated.JerkIntegrator.P (z 0) := by
  have hs := Generated.JerkIntegrator.certified_jitter h z hmin0 hminhi hlo hhi
    (fun k => by rw [hdyn k, segment_eq_transition]) n
  exact (intersample_energy ht0 (hth.trans (hhi n)) (z n)).trans (by simpa using hs)

end Jerk

namespace Planar

/-- State order: q1, q2, v1, v2. -/
abbrev State := Fin 4 → ℝ

/-- First component of the sampled acceleration, using both positions and velocities. -/
def input1 (z : State) : ℝ := -2 * z 0 - (1 / 2) * z 1 - 3 * z 2 - (1 / 4) * z 3

/-- Second component; the proportional and derivative gain matrices do not commute. -/
def input2 (z : State) : ℝ := -(1 / 2) * z 0 - z 1 - (1 / 4) * z 2 - 2 * z 3

def position1 (t : ℝ) (z : State) : ℝ := z 0 + t * z 2 + t ^ 2 / 2 * input1 z
def position2 (t : ℝ) (z : State) : ℝ := z 1 + t * z 3 + t ^ 2 / 2 * input2 z
def velocity1 (t : ℝ) (z : State) : ℝ := z 2 + t * input1 z
def velocity2 (t : ℝ) (z : State) : ℝ := z 3 + t * input2 z

def segment (t : ℝ) (z : State) : State :=
  ![position1 t z, position2 t z, velocity1 t z, velocity2 t z]

/-- Open-loop planar double-integrator vector field with a supplied held input. -/
def vectorField (u1 u2 : ℝ) (current : State) : State :=
  ![current 2, current 3, u1, u2]

theorem segment_initial (z : State) : segment 0 z = z := by
  ext i
  fin_cases i <;> simp [segment, position1, position2, velocity1, velocity2]

theorem position1_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => position1 s z) (velocity1 t z) t := by
  exact held_position_derivative t (z 0) (z 2) (input1 z)

theorem position2_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => position2 s z) (velocity2 t z) t := by
  exact held_position_derivative t (z 1) (z 3) (input2 z)

theorem velocity1_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => velocity1 s z) (input1 z) t := by
  exact held_velocity_derivative t (z 2) (input1 z)

theorem velocity2_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => velocity2 s z) (input2 z) t := by
  exact held_velocity_derivative t (z 3) (input2 z)

/-- The acceleration is held at the value sampled from `z`, including the coupling. -/
theorem segment_ode (t : ℝ) (z : State) (i : Fin 4) :
    HasDerivAt (fun s => segment s z i)
      (vectorField (input1 z) (input2 z) (segment t z) i) t := by
  fin_cases i
  · simpa [segment, vectorField] using position1_derivative t z
  · simpa [segment, vectorField] using position2_derivative t z
  · simpa [segment, vectorField] using velocity1_derivative t z
  · simpa [segment, vectorField] using velocity2_derivative t z

/-- The generator's four-by-four polynomial is the exact held endpoint. -/
theorem segment_eq_transition (h : ℝ) (z : State) :
    segment h z = Generated.CoupledPlanar.transition h *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segment, position1, position2, velocity1, velocity2, input1, input2,
      Generated.CoupledPlanar.transition, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.of_apply] <;> ring

/-- The interval certificate now applies to the independently specified plant segment. -/
theorem segment_energy_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ 1 / 2) (z : State) :
    energy Generated.CoupledPlanar.P (segment h z) ≤
      energy Generated.CoupledPlanar.P z - h * squaredNorm z := by
  rw [segment_eq_transition]
  simpa using Generated.CoupledPlanar.certified_decrease hlo hhi z

/-- The coupled plant's energy cannot exceed its value at the last sample. -/
theorem intersample_energy {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 2) (z : State) :
    energy Generated.CoupledPlanar.P (segment t z) ≤ energy Generated.CoupledPlanar.P z := by
  have hd := segment_energy_decrease ht0 hthi z
  have hn : 0 ≤ squaredNorm z := Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  exact hd.trans (sub_le_self _ (mul_nonneg ht0 hn))

/-- A uniform sample-index envelope for every within-segment state. -/
theorem sampled_segment_bound (h : ℕ → ℝ) (z : ℕ → State) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 2)
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ 1 / 2)
    (hdyn : ∀ k, z (k + 1) = segment (h k) (z k)) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h n) :
    energy Generated.CoupledPlanar.P (segment t (z n)) ≤
      (1 - hmin / Generated.CoupledPlanar.upperBound) ^ n *
        energy Generated.CoupledPlanar.P (z 0) := by
  have hs := Generated.CoupledPlanar.certified_jitter h z hmin0 hminhi hlo hhi
    (fun k => by rw [hdyn k, segment_eq_transition]) n
  exact (intersample_energy ht0 (hth.trans (hhi n)) (z n)).trans (by simpa using hs)

end Planar
end LeanControls.HeldModels
