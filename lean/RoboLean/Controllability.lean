import Mathlib

/-!
# Discrete-time linear control: reachability, controllability, observability

We study the discrete-time linear system `x_{k+1} = A x_k + B u_k` with `A : V →ₗ[K] V`,
`B : U →ₗ[K] V` over a field `K` (state space `V`, input space `U`), and its output
`y_k = C x_k` with `C : V →ₗ[K] Y`. Matrix statements specialize to `A = toLin' A`, etc.

## Main results

* `Control.state_eq`: closed form `x_k = Aᵏ x₀ + ∑_{i<k} A^{k-1-i} B u_i`.
* `Control.reachable_eq_krylov`: states reachable from `0` in `k` steps form the Krylov subspace
  `𝒦ₖ = range B + range AB + ⋯ + range A^{k-1}B`.
* `Control.krylov_eq_krylov_finrank`: by Cayley–Hamilton the chain `𝒦ₖ` stabilizes at
  `k = n = dim V`.
* `Control.controllable_iff_krylov_eq_top`, `Control.controllable_iff_rank_kalmanMatrix`:
  the Kalman controllability criterion (subspace and rank forms).
* `Control.Controllable.exists_input_state_finrank_eq`: deadbeat steering in exactly `n` steps.
* `Control.mem_unobservable_iff`, `Control.observable_iff_rank_obsMatrix`,
  `Control.observable_iff_controllable_transpose`: observability and duality.
* `Control.doubleIntegrator_controllable`, `Control.unicycle_not_controllable`: examples.
-/

open Polynomial Module

namespace Control

variable {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]

/-- State after `k` steps of `x_{k+1} = A x_k + B u_k`, from `x₀` under the input sequence `u`. -/
def state (A : V →ₗ[K] V) (B : U →ₗ[K] V) (x₀ : V) (u : ℕ → U) : ℕ → V
  | 0 => x₀
  | k + 1 => A (state A B x₀ u k) + B (u k)

variable (A : V →ₗ[K] V) (B : U →ₗ[K] V)

/-- Zero steps leaves the state unchanged. -/
@[simp] theorem state_zero (x₀ : V) (u : ℕ → U) : state A B x₀ u 0 = x₀ := rfl

/-- One-step recursion. -/
theorem state_succ (x₀ : V) (u : ℕ → U) (k : ℕ) :
    state A B x₀ u (k + 1) = A (state A B x₀ u k) + B (u k) := rfl

/-- **Closed form** (variation of constants): `x_k = Aᵏ x₀ + ∑_{i<k} A^{k-1-i} B u_i`. -/
theorem state_eq (x₀ : V) (u : ℕ → U) (k : ℕ) :
    state A B x₀ u k = (A ^ k) x₀ + ∑ i ∈ Finset.range k, (A ^ (k - 1 - i)) (B (u i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [state_succ, ih, map_add, map_sum, Finset.sum_range_succ, pow_succ', Module.End.mul_apply,
      add_assoc]
    congr 1
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Module.End.one_apply]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [← Module.End.mul_apply, ← pow_succ']
    congr 3
    omega


/-- Superposition: the state is the free response plus the forced response from rest. -/
theorem state_eq_add (x₀ : V) (u : ℕ → U) (k : ℕ) :
    state A B x₀ u k = (A ^ k) x₀ + state A B 0 u k := by
  rw [state_eq, state_eq A B 0]; simp

/-- The input-to-state map after `k` steps from rest. -/
noncomputable def reachMap (k : ℕ) : (ℕ → U) →ₗ[K] V where
  toFun u := ∑ i ∈ Finset.range k, (A ^ (k - 1 - i)) (B (u i))
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.smul_sum]

/-- From rest, the state is the image of the input under `reachMap`. -/
theorem state_zero_eq_reachMap (u : ℕ → U) (k : ℕ) : state A B 0 u k = reachMap A B k u := by
  simp [state_eq, reachMap]

/-- Controllability (Krylov) subspace `range B + range AB + ⋯ + range A^{k-1}B`. -/
def krylov (k : ℕ) : Submodule K V := ⨆ (i : ℕ) (_ : i < k), LinearMap.range ((A ^ i) ∘ₗ B)

/-- The set of states reachable from `0` in exactly `k` steps. -/
def reachable (k : ℕ) : Set V := {x | ∃ u : ℕ → U, state A B 0 u k = x}

/-- Each block `range (Aⁱ B)`, `i < k`, lies in `𝒦ₖ`. -/
theorem range_le_krylov {i k : ℕ} (h : i < k) : LinearMap.range ((A ^ i) ∘ₗ B) ≤ krylov A B k :=
  le_iSup₂_of_le (f := fun i (_ : i < k) => LinearMap.range ((A ^ i) ∘ₗ B)) i h le_rfl

/-- The image of the `k`-step input-to-state map is the Krylov subspace `𝒦ₖ`. -/
theorem range_reachMap (k : ℕ) : LinearMap.range (reachMap A B k) = krylov A B k := by
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    show ∑ i ∈ Finset.range k, (A ^ (k - 1 - i)) (B (u i)) ∈ _
    refine (krylov A B k).sum_mem fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact range_le_krylov A B (i := k - 1 - i) (by omega) ⟨u i, rfl⟩
  · refine iSup₂_le fun i hi => ?_
    rintro x ⟨w, rfl⟩
    refine ⟨Function.update 0 (k - 1 - i) w, ?_⟩
    simp only [reachMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rw [Finset.sum_eq_single (k - 1 - i)]
    · simp only [Function.update_self]; congr 2; omega
    · intro j _ hj; simp [Function.update_of_ne hj]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Reachable set = Krylov subspace.** -/
theorem reachable_eq_krylov (k : ℕ) : reachable A B k = (krylov A B k : Set V) := by
  rw [← range_reachMap]; ext x
  simp [reachable, state_zero_eq_reachMap]

/-- `x ∈ 𝒦ₖ` iff some input drives the system from `0` to `x` in exactly `k` steps. -/
theorem mem_krylov_iff (k : ℕ) (x : V) : x ∈ krylov A B k ↔ ∃ u, state A B 0 u k = x := by
  rw [← SetLike.mem_coe, ← reachable_eq_krylov]; rfl

/-- The Krylov chain is increasing. -/
theorem krylov_mono {k l : ℕ} (h : k ≤ l) : krylov A B k ≤ krylov A B l :=
  iSup₂_le fun i hi => range_le_krylov A B (by omega)

/-- `𝒦₀ = 0`. -/
theorem krylov_zero : krylov A B 0 = ⊥ := by simp [krylov]

/-- `𝒦ₖ₊₁ = 𝒦ₖ ⊔ range (Aᵏ B)`. -/
theorem krylov_succ (k : ℕ) :
    krylov A B (k + 1) = krylov A B k ⊔ LinearMap.range ((A ^ k) ∘ₗ B) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · exact (range_le_krylov A B h).trans le_sup_left
    · exact le_sup_right
  · exact sup_le (krylov_mono A B (Nat.le_succ k)) (range_le_krylov A B (Nat.lt_succ_self k))

/-- `A (range (Aⁱ B)) = range (Aⁱ⁺¹ B)`. -/
theorem map_range_pow_comp (i : ℕ) :
    (LinearMap.range ((A ^ i) ∘ₗ B)).map A = LinearMap.range ((A ^ (i + 1)) ∘ₗ B) := by
  rw [← LinearMap.range_comp, ← LinearMap.comp_assoc, pow_succ', Module.End.mul_eq_comp]


section CayleyHamilton

variable [FiniteDimensional K V]

/-- Cayley–Hamilton, in the form used for Krylov arguments: if `A^i x ∈ W` for all
`i < n = dim V`, then also `A^n x ∈ W`. -/
theorem pow_finrank_apply_mem (W : Submodule K V) (x : V)
    (hx : ∀ i < finrank K V, (A ^ i) x ∈ W) : (A ^ finrank K V) x ∈ W := by
  have h := LinearMap.aeval_self_charpoly A
  rw [(LinearMap.charpoly_monic A).as_sum, LinearMap.charpoly_natDegree] at h
  have h' := congrArg (fun f : V →ₗ[K] V => f x) h
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, LinearMap.add_apply,
    LinearMap.zero_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply] at h'
  rw [add_eq_zero_iff_eq_neg] at h'
  rw [h']
  exact W.neg_mem (W.sum_mem fun i hi => W.smul_mem _ (hx i (Finset.mem_range.1 hi)))


/-- Cayley–Hamilton step: `range (Aⁿ B) ⊆ 𝒦ₙ`. -/
theorem range_pow_finrank_le_krylov :
    LinearMap.range ((A ^ finrank K V) ∘ₗ B) ≤ krylov A B (finrank K V) := by
  rintro _ ⟨w, rfl⟩
  exact pow_finrank_apply_mem A _ (B w) fun i hi => range_le_krylov A B hi ⟨w, rfl⟩

/-- The controllability subspace `𝒦ₙ` is `A`-invariant. -/
theorem apply_mem_krylov_finrank {x : V} (hx : x ∈ krylov A B (finrank K V)) :
    A x ∈ krylov A B (finrank K V) := by
  suffices h : krylov A B (finrank K V) ≤ (krylov A B (finrank K V)).comap A from h hx
  refine iSup₂_le fun i hi => ?_
  rw [← Submodule.map_le_iff_le_comap, map_range_pow_comp]
  rcases Nat.lt_or_ge (i + 1) (finrank K V) with h | h
  · exact range_le_krylov A B h
  · have e : i + 1 = finrank K V := by omega
    rw [e]; exact range_pow_finrank_le_krylov A B

/-- `𝒦ₙ` is invariant under every power of `A`. -/
theorem pow_apply_mem_krylov_finrank (j : ℕ) {x : V} (hx : x ∈ krylov A B (finrank K V)) :
    (A ^ j) x ∈ krylov A B (finrank K V) := by
  induction j with
  | zero => simpa using hx
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact apply_mem_krylov_finrank A B ih

/-- Every `range (Aʲ B)` lies in `𝒦ₙ`, for all `j` (not only `j < n`). -/
theorem range_pow_le_krylov_finrank (j : ℕ) :
    LinearMap.range ((A ^ j) ∘ₗ B) ≤ krylov A B (finrank K V) := by
  rcases Nat.lt_or_ge j (finrank K V) with h | h
  · exact range_le_krylov A B h
  · rintro _ ⟨w, rfl⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [LinearMap.comp_apply, add_comm, pow_add, Module.End.mul_apply]
    exact pow_apply_mem_krylov_finrank A B d (range_pow_finrank_le_krylov A B ⟨w, rfl⟩)

/-- **Stabilization**: `𝒦ₖ ≤ 𝒦ₙ` for every `k`, where `n = dim V`. -/
theorem krylov_le_krylov_finrank (k : ℕ) : krylov A B k ≤ krylov A B (finrank K V) :=
  iSup₂_le fun j _ => range_pow_le_krylov_finrank A B j

/-- **Stabilization**: the Krylov chain is constant from `k = n = dim V` on. -/
theorem krylov_eq_krylov_finrank {k : ℕ} (hk : finrank K V ≤ k) :
    krylov A B k = krylov A B (finrank K V) :=
  le_antisymm (krylov_le_krylov_finrank A B k) (krylov_mono A B hk)

/-- A state reachable from the origin in *some* number of steps is reachable in exactly
`n = dim V` steps. -/
theorem reachable_subset_reachable_finrank (k : ℕ) :
    reachable A B k ⊆ reachable A B (finrank K V) := by
  rw [reachable_eq_krylov, reachable_eq_krylov]
  exact krylov_le_krylov_finrank A B k

end CayleyHamilton

/-! ### Controllability and the Kalman criterion -/

/-- The system `x_{k+1} = A x_k + B u_k` is **controllable** if every state can be reached from
the origin in some finite number of steps. -/
def Controllable : Prop := ∀ x : V, ∃ (k : ℕ) (u : ℕ → U), state A B 0 u k = x

/-- **Kalman criterion (subspace form)**: the system is controllable iff the controllability
subspace `range B + range AB + ⋯ + range Aⁿ⁻¹B` is the whole space. -/
theorem controllable_iff_krylov_eq_top [FiniteDimensional K V] :
    Controllable A B ↔ krylov A B (finrank K V) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, u, hu⟩ := h x
    exact krylov_le_krylov_finrank A B k ((mem_krylov_iff A B k x).2 ⟨u, hu⟩)
  · intro h x
    obtain ⟨u, hu⟩ := (mem_krylov_iff A B _ x).1 (h ▸ Submodule.mem_top)
    exact ⟨_, u, hu⟩

/-- **Deadbeat control**: a controllable system can be steered from any initial state to any
target state in exactly `n = dim V` steps. -/
theorem Controllable.exists_input_state_finrank_eq [FiniteDimensional K V]
    (h : Controllable A B) (x₀ xf : V) :
    ∃ u : ℕ → U, state A B x₀ u (finrank K V) = xf := by
  rw [controllable_iff_krylov_eq_top] at h
  obtain ⟨u, hu⟩ := (mem_krylov_iff A B _ (xf - (A ^ finrank K V) x₀)).1
    (h ▸ Submodule.mem_top)
  exact ⟨u, by rw [state_eq_add, hu, add_sub_cancel]⟩

/-- Controllability is equivalent to the existence of steering inputs between arbitrary pairs
of states in exactly `n` steps. -/
theorem controllable_iff_forall_exists [FiniteDimensional K V] :
    Controllable A B ↔ ∀ x₀ xf : V, ∃ u : ℕ → U, state A B x₀ u (finrank K V) = xf :=
  ⟨fun h => h.exists_input_state_finrank_eq A B, fun h x => ⟨_, h 0 x⟩⟩


/-! ### Observability -/

section Observability

variable {Y : Type*} [AddCommGroup Y] [Module K Y] (C : V →ₗ[K] Y)

/-- The **unobservable subspace** `⋂_{i < n} ker (C Aⁱ)`, `n = dim V`. -/
noncomputable def unobservable : Submodule K V :=
  ⨅ (i : ℕ) (_ : i < finrank K V), LinearMap.ker (C ∘ₗ A ^ i)

/-- Membership in the unobservable subspace, unfolded. -/
theorem mem_unobservable_iff_lt {x : V} :
    x ∈ unobservable A C ↔ ∀ i < finrank K V, C ((A ^ i) x) = 0 := by
  simp [unobservable]

variable [FiniteDimensional K V]

/-- The unobservable subspace is `A`-invariant (Cayley–Hamilton). -/
theorem apply_mem_unobservable {x : V} (hx : x ∈ unobservable A C) : A x ∈ unobservable A C := by
  rw [mem_unobservable_iff_lt] at hx ⊢
  intro i hi
  rw [← Module.End.mul_apply, ← pow_succ]
  rcases Nat.lt_or_ge (i + 1) (finrank K V) with h | h
  · exact hx _ h
  · have e : i + 1 = finrank K V := by omega
    rw [e]
    exact pow_finrank_apply_mem A (LinearMap.ker C) x hx

/-- **Unobservable subspace characterization** (via Cayley–Hamilton): `x` lies in
`⋂_{i<n} ker (C Aⁱ)` iff the zero-input output `y_k = C Aᵏ x` vanishes for *all* `k`. -/
theorem mem_unobservable_iff {x : V} :
    x ∈ unobservable A C ↔ ∀ k : ℕ, C ((A ^ k) x) = 0 := by
  refine ⟨fun hx k => ?_, fun h => (mem_unobservable_iff_lt A C).2 fun i _ => h i⟩
  have hpow : ∀ j, (A ^ j) x ∈ unobservable A C := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact apply_mem_unobservable A C ih
  rcases Nat.lt_or_ge k (finrank K V) with h | h
  · exact (mem_unobservable_iff_lt A C).1 hx k h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, Module.End.mul_apply]
    exact pow_finrank_apply_mem A (LinearMap.ker C) _ ((mem_unobservable_iff_lt A C).1 (hpow d))

/-- Two initial states produce the same output `y_k = C x_k` under every input sequence iff
their difference is unobservable. -/
theorem output_eq_iff_sub_mem_unobservable (x x' : V) :
    (∀ (u : ℕ → U) (k : ℕ), C (state A B x u k) = C (state A B x' u k)) ↔
      x - x' ∈ unobservable A C := by
  rw [mem_unobservable_iff]
  simp only [state_eq_add A B x, state_eq_add A B x', map_add, add_left_inj, map_sub,
    sub_eq_zero]
  exact ⟨fun h k => h 0 k, fun h _ k => h k⟩

/-- The pair `(A, C)` is **observable** if the only initial state producing identically zero
free output `C Aᵏ x` is `x = 0`. -/
def Observable : Prop := ∀ x : V, (∀ k : ℕ, C ((A ^ k) x) = 0) → x = 0

theorem observable_iff_unobservable_eq_bot : Observable A C ↔ unobservable A C = ⊥ := by
  rw [Submodule.eq_bot_iff]
  simp only [mem_unobservable_iff]
  rfl

/-- Observability means the initial state is uniquely determined by the input/output record. -/
theorem observable_iff_injective_output :
    Observable A C ↔ ∀ x x' : V,
      (∀ (u : ℕ → U) (k : ℕ), C (state A B x u k) = C (state A B x' u k)) → x = x' := by
  rw [observable_iff_unobservable_eq_bot, Submodule.eq_bot_iff]
  simp only [output_eq_iff_sub_mem_unobservable A B C]
  exact ⟨fun h x x' hx => sub_eq_zero.1 (h _ hx),
    fun h x hx => h x 0 (by simpa using hx)⟩

end Observability

/-! ### Matrix form: the Kalman rank condition and duality -/

section Matrix

open Matrix

variable {n m p : ℕ}

/-- The Kalman controllability matrix `[B, AB, A²B, …, Aⁿ⁻¹B]`, with columns indexed by
`(i, j) : Fin n × Fin m` (column `j` of the block `Aⁱ B`). -/
def kalmanMatrix (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin m) K) :
    Matrix (Fin n) (Fin n × Fin m) K :=
  Matrix.of fun r q => (A ^ (q.1 : ℕ) * B) r q.2

/-- The observability matrix `[C; CA; …; CAⁿ⁻¹]`, with rows indexed by `(i, j) : Fin n × Fin p`. -/
def obsMatrix (A : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin p) (Fin n) K) :
    Matrix (Fin n × Fin p) (Fin n) K :=
  Matrix.of fun q c => (C * A ^ (q.1 : ℕ)) q.2 c

/-- The column space of the Kalman matrix is the controllability subspace `𝒦ₙ`. -/
theorem range_kalmanMatrix (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin m) K) :
    LinearMap.range (kalmanMatrix A B).mulVecLin =
      krylov (toLin' A) (toLin' B) (finrank K (Fin n → K)) := by
  rw [Matrix.range_mulVecLin, Module.finrank_fin_fun]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine range_le_krylov (toLin' A) (toLin' B) i.isLt ⟨Pi.single j 1, ?_⟩
    rw [← toLin'_pow, ← toLin'_mul, toLin'_apply, mulVec_single_one]
    rfl
  · refine iSup₂_le fun i hi => ?_
    rw [← toLin'_pow, ← toLin'_mul, range_toLin']
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨(⟨i, hi⟩, j), rfl⟩

/-- **Kalman rank condition**: `(A, B)` is controllable iff
`rank [B, AB, …, Aⁿ⁻¹B] = n`. -/
theorem controllable_iff_rank_kalmanMatrix (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K) :
    Controllable (toLin' A) (toLin' B) ↔ (kalmanMatrix A B).rank = n := by
  rw [controllable_iff_krylov_eq_top, ← range_kalmanMatrix, Matrix.rank]
  constructor
  · intro h; rw [h, finrank_top, Module.finrank_fin_fun]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [h, Module.finrank_fin_fun]

/-- The null space of the observability matrix is the unobservable subspace. -/
theorem ker_obsMatrix (A : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin p) (Fin n) K) :
    LinearMap.ker (obsMatrix A C).mulVecLin = unobservable (toLin' A) (toLin' C) := by
  ext x
  rw [mem_unobservable_iff_lt, Module.finrank_fin_fun, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h i hi
    rw [← LinearMap.comp_apply, ← toLin'_pow, ← toLin'_mul, toLin'_apply]
    funext j
    have := congrFun h (⟨i, hi⟩, j)
    simpa [obsMatrix, mulVec, dotProduct] using this
  · intro h
    funext ⟨i, j⟩
    have := congrFun (h i i.isLt) j
    rw [← LinearMap.comp_apply, ← toLin'_pow, ← toLin'_mul, toLin'_apply] at this
    simpa [obsMatrix, mulVec, dotProduct] using this

/-- **Rank test for observability**: `(A, C)` is observable iff `rank [C; CA; …; CAⁿ⁻¹] = n`. -/
theorem observable_iff_rank_obsMatrix (A : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin p) (Fin n) K) :
    Observable (toLin' A) (toLin' C) ↔ (obsMatrix A C).rank = n := by
  rw [observable_iff_unobservable_eq_bot, ← ker_obsMatrix, Matrix.rank]
  have h := LinearMap.finrank_range_add_finrank_ker (obsMatrix A C).mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [← Submodule.finrank_eq_zero (R := K)]
  omega

/-- The Kalman matrix of `(Aᵀ, Cᵀ)` is the transpose of the observability matrix of `(A, C)`. -/
theorem kalmanMatrix_transpose (A : Matrix (Fin n) (Fin n) K) (C : Matrix (Fin p) (Fin n) K) :
    kalmanMatrix Aᵀ Cᵀ = (obsMatrix A C)ᵀ := by
  ext r q
  simp [kalmanMatrix, obsMatrix, ← transpose_pow, ← transpose_mul]

/-- **Duality**: `(A, C)` is observable iff `(Aᵀ, Cᵀ)` is controllable. -/
theorem observable_iff_controllable_transpose (A : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin p) (Fin n) K) :
    Observable (toLin' A) (toLin' C) ↔ Controllable (toLin' Aᵀ) (toLin' Cᵀ) := by
  rw [observable_iff_rank_obsMatrix, controllable_iff_rank_kalmanMatrix, kalmanMatrix_transpose,
    rank_transpose]

end Matrix


/-! ### Examples -/

section Examples

open Matrix

/-- Double integrator (position/velocity, force input): `A = [[1,1],[0,1]]`. -/
def doubleIntegratorA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- Double integrator input matrix `B = [0; 1]`. -/
def doubleIntegratorB : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- **The double integrator is controllable**: every state is reached from rest in two steps
(using `u₀ = x₀`, `u₁ = x₁ - x₀`). -/
theorem doubleIntegrator_controllable :
    Controllable (toLin' doubleIntegratorA) (toLin' doubleIntegratorB) := by
  intro x
  refine ⟨2, fun k => if k = 0 then fun _ => x 0 else fun _ => x 1 - x 0, ?_⟩
  ext i
  fin_cases i <;>
    simp [state, doubleIntegratorA, doubleIntegratorB, toLin'_apply, dotProduct]

/-- Linearization of the unicycle `ẋ = v cos θ, ẏ = v sin θ, θ̇ = ω` at rest (`θ = 0`),
discretized: `A = I₃`. -/
def unicycleA : Matrix (Fin 3) (Fin 3) ℝ := 1

/-- Input matrix of the linearized unicycle, inputs `(v, ω)`: `B = [[1,0],[0,0],[0,1]]`
(no direct lateral motion). -/
def unicycleB : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]

/-- In the linearized unicycle the lateral coordinate `y` never changes, whatever the input. -/
theorem unicycle_lateral_invariant (x₀ : Fin 3 → ℝ) (u : ℕ → Fin 2 → ℝ) (k : ℕ) :
    state (toLin' unicycleA) (toLin' unicycleB) x₀ u k 1 = x₀ 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [state_succ]
    simpa [unicycleA, unicycleB, toLin'_apply, mulVec, dotProduct, Fin.sum_univ_two] using ih

/-- **The linearized unicycle is NOT controllable**: the sideways state `(0, 1, 0)` can never be
reached from rest. The nonholonomic unicycle *is* controllable as a nonlinear system (via
Lie brackets / Chow–Rashevskii), so this shows that linearization-based control design cannot
handle nonholonomic robots: genuinely nonlinear control is required. -/
theorem unicycle_not_controllable :
    ¬ Controllable (toLin' unicycleA) (toLin' unicycleB) := by
  intro h
  obtain ⟨k, u, hu⟩ := h (Pi.single 1 1)
  have := unicycle_lateral_invariant 0 u k
  rw [hu] at this
  simp at this

end Examples

end Control
