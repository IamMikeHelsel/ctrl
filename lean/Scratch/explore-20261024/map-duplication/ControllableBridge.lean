import ControlsLean
import RoboLean

open Module

variable {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]

theorem traj_eq_state (A : V →ₗ[K] V) (B : U →ₗ[K] V) (x₀ : V) (u : ℕ → U) (k : ℕ) :
    ControlsLean.Controls.traj A B x₀ u k = Control.state A B x₀ u k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ControlsLean.Controls.traj, Control.state, ih]

theorem controllable_bridge [FiniteDimensional K V] (A : V →ₗ[K] V) (B : U →ₗ[K] V) :
    ControlsLean.Controls.Controllable A B ↔ Control.Controllable A B := by
  rw [ControlsLean.Controls.controllable_iff_forall_exists]
  simp only [traj_eq_state]
  rfl
