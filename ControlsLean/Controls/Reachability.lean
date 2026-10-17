/-
Copyright (c) 2026 ControlsLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ControlsLean contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Reachability and controllability of discrete-time linear systems

System `x_{k+1} = A x_k + B u_k` with state space `V` (finite-dimensional over a field `K`)
and input space `U`.

* `reach A B k` is the set of states reachable from `0` in exactly `k` steps. It is a subspace,
  given recursively by `R₀ = 0`, `R_{k+1} = range B ⊔ A(R_k)`, and equals
  `range B + A·range B + ⋯ + A^{k-1}·range B`.
* **Stabilisation**: `R_k = R_n` for every `k ≥ n = dim V`. The proof is a dimension-counting
  argument on the increasing chain `R_k` and does not use Cayley–Hamilton.
* **Feedback invariance**: state feedback `u = F x + v` does not change any `R_k`.
* A controllable system can be steered from any state to any state in `dim V` steps.
-/

namespace ControlsLean.Controls

open Submodule Module
open LinearMap (range)

variable {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
variable (A : V →ₗ[K] V) (B : U →ₗ[K] V)

/-- State trajectory from `x₀` under the input sequence `u`. -/
def traj (x₀ : V) (u : ℕ → U) : ℕ → V
  | 0 => x₀
  | k + 1 => A (traj x₀ u k) + B (u k)

/-- States reachable from `0` in `k` steps, defined recursively. -/
def reach : ℕ → Submodule K V
  | 0 => ⊥
  | k + 1 => range B ⊔ (reach k).map A

variable {A B}

@[simp] theorem traj_zero (x₀ : V) (u : ℕ → U) : traj A B x₀ u 0 = x₀ := rfl
@[simp] theorem traj_succ (x₀ : V) (u : ℕ → U) (k : ℕ) :
    traj A B x₀ u (k + 1) = A (traj A B x₀ u k) + B (u k) := rfl
@[simp] theorem reach_zero : reach A B 0 = ⊥ := rfl
theorem reach_succ (k : ℕ) : reach A B (k + 1) = range B ⊔ (reach A B k).map A := rfl

/-- The state at time `k` depends only on inputs before time `k`. -/
theorem traj_congr (x₀ : V) {u u' : ℕ → U} {k : ℕ} (h : ∀ i < k, u i = u' i) :
    traj A B x₀ u k = traj A B x₀ u' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [traj_succ, ih fun i hi => h i (by omega), h k (by omega)]

/-- Superposition: free response plus forced response. -/
theorem traj_eq (x₀ : V) (u : ℕ → U) (k : ℕ) :
    traj A B x₀ u k = (A ^ k) x₀ + traj A B 0 u k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ', add_assoc]

/-- `reach A B k` is exactly the set of states reachable from `0` in `k` steps. -/
theorem mem_reach_iff {k : ℕ} {x : V} : x ∈ reach A B k ↔ ∃ u, traj A B 0 u k = x := by
  induction k generalizing x with
  | zero => simp [eq_comm]
  | succ k ih =>
    rw [reach_succ, mem_sup]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨u, rfl⟩ := ih.1 hw
      refine ⟨Function.update u k v, ?_⟩
      rw [traj_succ, traj_congr 0 (u' := u) fun i hi => Function.update_of_ne (by omega) _ _,
        Function.update_self, add_comm]
    · rintro ⟨u, rfl⟩
      exact ⟨_, ⟨u k, rfl⟩, _, ⟨_, ih.2 ⟨u, rfl⟩, rfl⟩, add_comm _ _⟩

/-- Closed form: `R_k = ⨆_{i<k} Aⁱ (range B)`. -/
theorem reach_eq_iSup (k : ℕ) :
    reach A B k = ⨆ i < k, range ((A ^ i) ∘ₗ B) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [reach_succ, ih, Nat.iSup_lt_succ', pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
    simp only [Submodule.map_iSup, pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc,
      LinearMap.range_comp]

theorem reach_mono_succ (k : ℕ) : reach A B k ≤ reach A B (k + 1) := by
  induction k with
  | zero => exact bot_le
  | succ k ih => exact sup_le_sup_left (map_mono ih) _

theorem reach_mono : Monotone (reach A B) := monotone_nat_of_le_succ reach_mono_succ

/-- Once the chain stalls, it is stationary forever. -/
theorem reach_stable {i : ℕ} (h : reach A B i = reach A B (i + 1)) :
    ∀ j, i ≤ j → reach A B j = reach A B i := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hij ih => rw [reach_succ, ih, ← reach_succ, ← h]

section FiniteDimensional

variable [FiniteDimensional K V]

/-- While the chain is strictly increasing, the dimension grows by at least one per step. -/
theorem le_finrank_reach {k : ℕ} (h : ∀ i < k, reach A B i < reach A B (i + 1)) :
    k ≤ finrank K (reach A B k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have := Submodule.finrank_lt_finrank_of_lt (h k (by omega))
    have := ih fun i hi => h i (by omega)
    omega

/-- **Stabilisation at `n = dim V`**: nothing new becomes reachable after `n` steps. -/
theorem reach_eq_reach_finrank {k : ℕ} (hk : finrank K V ≤ k) :
    reach A B k = reach A B (finrank K V) := by
  by_cases hs : ∃ i < finrank K V, reach A B i = reach A B (i + 1)
  · obtain ⟨i, hi, h⟩ := hs
    rw [reach_stable h k (by omega), reach_stable h _ hi.le]
  · push Not at hs
    have hlt : ∀ i < finrank K V, reach A B i < reach A B (i + 1) :=
      fun i hi => lt_of_le_of_ne (reach_mono_succ i) (hs i hi)
    have htop : reach A B (finrank K V) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (le_finrank_reach hlt))
    exact le_antisymm (htop ▸ le_top) (reach_mono hk)

/-- Every state reachable at any time is reachable within `dim V` steps. -/
theorem reach_le_reach_finrank (k : ℕ) : reach A B k ≤ reach A B (finrank K V) := by
  rcases le_total k (finrank K V) with h | h
  · exact reach_mono h
  · exact (reach_eq_reach_finrank h).le

/-- The system is (reachable-from-zero) controllable. -/
def Controllable (A : V →ₗ[K] V) (B : U →ₗ[K] V) : Prop := reach A B (finrank K V) = ⊤

/-- **Kalman rank condition**: controllable iff `[B, AB, …, A^{n-1}B]` has full rank `n`. -/
theorem controllable_iff_finrank :
    Controllable A B ↔
      finrank K ↥(⨆ i < finrank K V, range ((A ^ i) ∘ₗ B)) = finrank K V := by
  rw [Controllable, ← reach_eq_iSup]
  exact ⟨fun h => h ▸ finrank_top K V, Submodule.eq_top_of_finrank_eq⟩

omit [FiniteDimensional K V] in
/-- A controllable system can be steered from any `x₀` to any `x₁` in `dim V` steps. -/
theorem Controllable.exists_steer (hc : Controllable A B) (x₀ x₁ : V) :
    ∃ u, traj A B x₀ u (finrank K V) = x₁ := by
  obtain ⟨u, hu⟩ := mem_reach_iff.1 (hc ▸ mem_top : x₁ - (A ^ finrank K V) x₀ ∈ reach A B _)
  exact ⟨u, by rw [traj_eq, hu, add_sub_cancel]⟩

/-- Controllability means every state is reachable from `0` at *some* time. -/
theorem controllable_iff_forall_exists :
    Controllable A B ↔ ∀ x, ∃ k u, traj A B 0 u k = x := by
  constructor
  · intro hc x
    exact ⟨_, mem_reach_iff.1 (hc ▸ mem_top)⟩
  · intro h
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨k, u, rfl⟩ := h x
    exact reach_le_reach_finrank k (mem_reach_iff.2 ⟨u, rfl⟩)

end FiniteDimensional

/-! ### Invariance under state feedback -/

/-- Feedback `u = F x + v` leaves every reachable subspace unchanged. -/
theorem reach_feedback (F : V →ₗ[K] U) (k : ℕ) : reach (A + B ∘ₗ F) B k = reach A B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [reach_succ, reach_succ, ih]
    apply le_antisymm <;> refine sup_le le_sup_left ?_ <;> rintro _ ⟨w, hw, rfl⟩
    · rw [show (A + B ∘ₗ F) w = B (F w) + A w by
        simp only [LinearMap.add_apply, LinearMap.comp_apply]; abel]
      exact add_mem (mem_sup_left ⟨F w, rfl⟩) (mem_sup_right ⟨w, hw, rfl⟩)
    · rw [show A w = B (-F w) + (A + B ∘ₗ F) w by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_neg]; abel]
      exact add_mem (mem_sup_left ⟨-F w, rfl⟩) (mem_sup_right ⟨w, hw, rfl⟩)

theorem controllable_feedback [FiniteDimensional K V] (F : V →ₗ[K] U) :
    Controllable (A + B ∘ₗ F) B ↔ Controllable A B := by
  rw [Controllable, Controllable, reach_feedback]

end ControlsLean.Controls
