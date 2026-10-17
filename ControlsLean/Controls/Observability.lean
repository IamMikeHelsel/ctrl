/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.Reachability
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Observability of discrete-time linear systems, as the dual of controllability

System `x_{k+1} = A x_k + B u_k`, `y_k = C x_k`, with state space `V` and output space `Y`.

* `unobs A C k = ⨅ i < k, ker (C ∘ Aⁱ)` is the set of initial states whose free response
  produces zero output during the first `k` steps. It is also given recursively by
  `N₀ = ⊤`, `N_{k+1} = ker C ⊓ A⁻¹(N_k)`.
* **Duality**: `unobs A C k` is the coannihilator of `reach Aᵀ Cᵀ k`, where `Aᵀ = A.dualMap`
  and `Cᵀ = C.dualMap`. Hence `(A, C)` is observable iff `(Aᵀ, Cᵀ)` is controllable.
* **Stabilisation**: `N_k = N_n` for every `k ≥ n = dim V`.
* **Output injection**: replacing `A` with `A + L C` does not change any `N_k`.
* An observable system's initial state is determined by the outputs over `dim V` steps.

Everything is coordinate-free and avoids Cayley–Hamilton: stabilisation is transported from
`reach_eq_reach_finrank` through the duality.
-/

namespace ControlsLean.Controls

open Submodule Module
open LinearMap (ker range)

variable {K V U Y : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]
variable (A : V →ₗ[K] V) (C : V →ₗ[K] Y)

/-- Initial states indistinguishable from `0` by the outputs over the first `k` steps. -/
def unobs (k : ℕ) : Submodule K V := ⨅ i < k, ker (C ∘ₗ A ^ i)

variable {A C}

theorem mem_unobs_iff {k : ℕ} {x : V} : x ∈ unobs A C k ↔ ∀ i < k, C ((A ^ i) x) = 0 := by
  simp [unobs, mem_iInf]

@[simp] theorem unobs_zero : unobs A C 0 = ⊤ := by simp [unobs]

/-- Recursive form: `N_{k+1} = ker C ⊓ A⁻¹(N_k)`. -/
theorem unobs_succ (k : ℕ) : unobs A C (k + 1) = ker C ⊓ (unobs A C k).comap A := by
  ext x
  simp only [mem_unobs_iff, mem_inf, LinearMap.mem_ker, mem_comap, Nat.forall_lt_succ_left,
    pow_zero, Module.End.one_apply, pow_succ, Module.End.mul_apply]

theorem unobs_anti : Antitone (unobs A C) := fun _ _ hjk _ hx =>
  mem_unobs_iff.2 fun i hi => mem_unobs_iff.1 hx i (by omega)

/-! ### Duality with reachability -/

theorem dualMap_pow (i : ℕ) : (A ^ i).dualMap = A.dualMap ^ i := by
  induction i with
  | zero => simp [Module.End.one_eq_id]
  | succ i ih =>
    rw [pow_succ, pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.dualMap_comp_dualMap, ih]

omit [AddCommGroup U] [Module K U] in
/-- The coannihilator of the range of a dual map is the kernel. -/
theorem dualCoannihilator_range_dualMap {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) : (range f.dualMap).dualCoannihilator = ker f := by
  ext x
  simp only [mem_dualCoannihilator, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, LinearMap.dualMap_apply, LinearMap.mem_ker]
  exact forall_dual_apply_eq_zero_iff K (f x)

omit [AddCommGroup U] [Module K U] in
/-- **Duality**: the unobservable subspace of `(A, C)` is the coannihilator of the reachable
subspace of the dual system `(Aᵀ, Cᵀ)`. -/
theorem unobs_eq_dualCoannihilator_reach (k : ℕ) :
    unobs A C k = (reach A.dualMap C.dualMap k).dualCoannihilator := by
  simp only [reach_eq_iSup, dualCoannihilator_iSup_eq, unobs, ← dualMap_pow,
    LinearMap.dualMap_comp_dualMap, dualCoannihilator_range_dualMap]

/-- The system `(A, C)` is observable: no nonzero initial state is invisible in the output. -/
def Observable (A : V →ₗ[K] V) (C : V →ₗ[K] Y) : Prop := unobs A C (finrank K V) = ⊥

section FiniteDimensional

variable [FiniteDimensional K V]

omit [AddCommGroup U] [Module K U] in
/-- **Observability is dual to controllability**: `(A, C)` is observable iff `(Aᵀ, Cᵀ)` is
controllable. -/
theorem observable_iff_controllable_dual :
    Observable A C ↔ Controllable A.dualMap C.dualMap := by
  rw [Observable, Controllable, Subspace.dual_finrank_eq, unobs_eq_dualCoannihilator_reach]
  constructor
  · intro h
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := reach A.dualMap C.dualMap (finrank K V)), h, dualAnnihilator_bot]
  · intro h
    rw [h, dualCoannihilator_top]

omit [AddCommGroup U] [Module K U] in
/-- **Stabilisation at `n = dim V`**: no further states become distinguishable after `n`
steps. -/
theorem unobs_eq_unobs_finrank {k : ℕ} (hk : finrank K V ≤ k) :
    unobs A C k = unobs A C (finrank K V) := by
  rw [unobs_eq_dualCoannihilator_reach, unobs_eq_dualCoannihilator_reach,
    ← Subspace.dual_finrank_eq (K := K) (V := V),
    reach_eq_reach_finrank (by rwa [Subspace.dual_finrank_eq])]

omit [AddCommGroup U] [Module K U] in
theorem unobs_finrank_le_unobs (k : ℕ) : unobs A C (finrank K V) ≤ unobs A C k := by
  rcases le_total k (finrank K V) with h | h
  · exact unobs_anti h
  · exact (unobs_eq_unobs_finrank h).ge

omit [AddCommGroup U] [Module K U] in
/-- Observability means the full output sequence of the free response determines the
initial state. -/
theorem observable_iff_forall :
    Observable A C ↔ ∀ x, (∀ i, C ((A ^ i) x) = 0) → x = 0 := by
  constructor
  · intro h x hx
    exact (mem_bot K).1 (h ▸ mem_unobs_iff.2 fun i _ => hx i)
  · intro h
    refine eq_bot_iff.2 fun x hx => (mem_bot K).2 (h x fun i => ?_)
    exact mem_unobs_iff.1 (unobs_finrank_le_unobs (i + 1) hx) i (by omega)

omit [FiniteDimensional K V] in
/-- An observable system's initial state is determined by the inputs and the outputs over
the first `dim V` steps. -/
theorem Observable.eq_of_output_eq (ho : Observable A C) (B : U →ₗ[K] V) {x₀ x₀' : V}
    (u : ℕ → U) (h : ∀ i < finrank K V, C (traj A B x₀ u i) = C (traj A B x₀' u i)) :
    x₀ = x₀' := by
  rw [← sub_eq_zero, ← mem_bot K, ← ho]
  refine mem_unobs_iff.2 fun i hi => ?_
  have := h i hi
  rw [traj_eq, traj_eq (x₀ := x₀'), map_add, map_add, add_left_inj] at this
  rw [map_sub, map_sub, this, sub_self]

end FiniteDimensional

/-! ### Invariance under output injection -/

/-- Output injection `A ↦ A + L C` leaves every unobservable subspace unchanged. -/
theorem unobs_outputInjection (L : Y →ₗ[K] V) (k : ℕ) :
    unobs (A + L ∘ₗ C) C k = unobs A C k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [unobs_succ, unobs_succ, ih]
    ext x
    simp only [mem_inf, LinearMap.mem_ker, mem_comap, LinearMap.add_apply, LinearMap.comp_apply]
    constructor <;> rintro ⟨hc, hx⟩ <;> refine ⟨hc, ?_⟩ <;> simpa [hc] using hx

theorem observable_outputInjection [FiniteDimensional K V] (L : Y →ₗ[K] V) :
    Observable (A + L ∘ₗ C) C ↔ Observable A C := by
  rw [Observable, Observable, unobs_outputInjection]

end ControlsLean.Controls
