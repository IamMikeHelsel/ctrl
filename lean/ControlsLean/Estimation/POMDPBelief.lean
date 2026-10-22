/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib

/-!
# Partially Observable Markov Decision Processes (POMDPs) & PWLC Value Functions

This module formalizes discrete-state Bayesian belief filtering and the
Smallwood–Sondik (1973) / Kaelbling–Littman–Cassandra (1998) Piecewise-Linear and Convex
(PWLC) value function theory for Partially Observable Markov Decision Processes (POMDPs),
closing **Roadmap §4.4**.

## Main Results

1. **Bayesian Belief Simplex & Exact Filtering (`IsBelief`, `beliefUpdate`)**:
   - `IsBelief`: probability simplex characterization $b(s) \ge 0$ and $\sum_s b(s) = 1$
     over `Fin n`.
   - `isBelief_convex_comb`: the belief simplex is closed under convex combinations
     $\lambda b_1 + (1 - \lambda) b_2$ for $0 \le \lambda \le 1$.
   - `unnormBeliefUpdate`, `obsNormConst`, `beliefUpdate`: unnormalized Bayes update
     $\tilde{b}(s') = O(s') \sum_s T(s, s') b(s)$, observation partition function
     $Z(b) = \sum_{s'} \tilde{b}(s')$, and normalized posterior belief
     $b^+(s') = \tilde{b}(s') / Z(b)$.
   - `beliefUpdate_isBelief`: whenever $Z(b) > 0$, `beliefUpdate T O b` is a valid belief
     distribution on the probability simplex.
   - `beliefPredict_obsNormConst_eq_one` and `beliefPredict_isBelief`: pure Markov prediction
     ($O(s') = 1$ for all $s'$) has unit normalization $Z(b) = 1$ and maps the belief simplex
     into itself.

2. **$\alpha$-Vector Representation & Piecewise-Linear Convexity (`pomdpValue`)**:
   - `pomdpValue`: for a non-empty finite collection of $\alpha$-vectors
     $\Gamma : \mathrm{Fin}\ K \to (\mathrm{Fin}\ n \to \mathbb{R})$ ($K \ge 1$),
     $$V_\Gamma(b) = \sup_{i \in \mathrm{Fin}\ K} (b \cdot \Gamma_i).$$
   - `pomdpValue_ge_dot` and `pomdpValue_le_iff`: characterization of $V_\Gamma(b)$ as the
     pointwise least upper bound of the linear hyperplanes $b \mapsto b \cdot \Gamma_i$.
   - `pomdpValue_convex`: **Piecewise-Linear Convexity (PWLC)** of the POMDP value function:
     $$V_\Gamma(\lambda b_1 + (1 - \lambda) b_2) \le \lambda V_\Gamma(b_1) + (1 - \lambda) V_\Gamma(b_2)$$
     for all $b_1, b_2$ and $0 \le \lambda \le 1$.
   - `pomdpValue_monotone`: monotonicity of $V_\Gamma(b)$ with respect to dominates in $\Gamma$
     for non-negative belief vectors.

3. **Smallwood–Sondik Bellman Backup Duality (`bellmanBackupAlpha`, `bellman_backup_alpha_eq`)**:
   - `bellmanBackupAlpha`: one-step backed-up $\alpha$-vector
     $$\alpha_{\mathrm{back}}(s) = r(s) + \gamma \sum_{s'} T(s, s') O(s') \alpha_{\mathrm{next}}(s').$$
   - `bellman_backup_alpha_eq`: exact adjoint duality between forward belief filtering and
     backward $\alpha$-vector propagation:
     $$b \cdot \alpha_{\mathrm{back}} = b \cdot r + \gamma \bigl(\tilde{b} \cdot \alpha_{\mathrm{next}}\bigr).$$
   - `bellman_backup_normalized_eq`: for $Z(b) > 0$,
     $$b \cdot \alpha_{\mathrm{back}} = b \cdot r + \gamma Z(b) \bigl(b^+ \cdot \alpha_{\mathrm{next}}\bigr).$$
   - `bellman_backup_pwlc_preservation`: maximizing over $i \in \mathrm{Fin}\ K$ proves that the
     one-step Bellman backup of a PWLC value function is itself a PWLC value function generated
     by the backed-up $\alpha$-vectors:
     $$b \cdot r + \gamma Z(b) V_\Gamma(b^+) = V_{\Gamma_{\mathrm{back}}}(b).$$
-/

namespace ControlsLean.Estimation.POMDPBelief

open Finset BigOperators Matrix

/-! ## 1. The Bayesian Belief Simplex and Exact POMDP Filtering -/

/-- A vector $b : \mathrm{Fin}\ n \to \mathbb{R}$ is a valid POMDP belief state if it lies on
the probability simplex: all entries are non-negative and sum to $1$. -/
def IsBelief {n : ℕ} (b : Fin n → ℝ) : Prop :=
  (∀ s : Fin n, 0 ≤ b s) ∧ ∑ s : Fin n, b s = 1

/-- Every entry of a valid belief state is bounded above by $1$. -/
theorem IsBelief.le_one {n : ℕ} {b : Fin n → ℝ} (hb : IsBelief b) (s : Fin n) :
    b s ≤ 1 := by
  rw [← hb.2]
  exact single_le_sum (fun i _ ↦ hb.1 i) (mem_univ s)

/-- Convexity of the POMDP belief simplex: any convex combination
$\lambda b_1 + (1 - \lambda) b_2$ with $0 \le \lambda \le 1$ of two belief states is a
valid belief state. -/
theorem isBelief_convex_comb {n : ℕ} {b₁ b₂ : Fin n → ℝ}
    (hb₁ : IsBelief b₁) (hb₂ : IsBelief b₂)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsBelief (fun s ↦ t * b₁ s + (1 - t) * b₂ s) := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  refine ⟨fun s ↦ add_nonneg (mul_nonneg ht0 (hb₁.1 s)) (mul_nonneg h1t (hb₂.1 s)), ?_⟩
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hb₁.2, hb₂.2]
  ring

/-- A row-stochastic Markov state-transition kernel $T(s, s') = \Pr(s' \mid s, a)$ on `Fin n`. -/
def IsTransitionKernel {n : ℕ} (T : Fin n → Fin n → ℝ) : Prop :=
  (∀ s s' : Fin n, 0 ≤ T s s') ∧ (∀ s : Fin n, ∑ s' : Fin n, T s s' = 1)

/-- A non-negative observation likelihood vector $O(s') = \Pr(o \mid s', a)$ on `Fin n`. -/
def IsObsLikelihood {n : ℕ} (O : Fin n → ℝ) : Prop :=
  ∀ s' : Fin n, 0 ≤ O s'

/-- Unnormalized Bayesian belief update $\tilde{b}(s') = O(s') \sum_s T(s, s') b(s)$. -/
def unnormBeliefUpdate {n : ℕ} (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ)
    (b : Fin n → ℝ) (s' : Fin n) : ℝ :=
  O s' * ∑ s : Fin n, T s s' * b s

/-- Observation normalization constant (partition function) $Z(b) = \sum_{s'} \tilde{b}(s')$. -/
def obsNormConst {n : ℕ} (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ) (b : Fin n → ℝ) : ℝ :=
  ∑ s' : Fin n, unnormBeliefUpdate T O b s'

/-- Normalized Bayesian belief update $b^+(s') = \tilde{b}(s') / Z(b)$. -/
noncomputable def beliefUpdate {n : ℕ} (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ)
    (b : Fin n → ℝ) (s' : Fin n) : ℝ :=
  unnormBeliefUpdate T O b s' / obsNormConst T O b

/-- Non-negativity of the unnormalized belief update $\tilde{b}(s') \ge 0$. -/
theorem unnormBeliefUpdate_nonneg {n : ℕ} {T : Fin n → Fin n → ℝ} {O : Fin n → ℝ}
    {b : Fin n → ℝ} (hT : ∀ s s', 0 ≤ T s s') (hO : IsObsLikelihood O)
    (hb : ∀ s, 0 ≤ b s) (s' : Fin n) :
    0 ≤ unnormBeliefUpdate T O b s' := by
  unfold unnormBeliefUpdate
  exact mul_nonneg (hO s') (sum_nonneg fun s _ ↦ mul_nonneg (hT s s') (hb s))

/-- Non-negativity of the observation normalization constant $Z(b) \ge 0$. -/
theorem obsNormConst_nonneg {n : ℕ} {T : Fin n → Fin n → ℝ} {O : Fin n → ℝ}
    {b : Fin n → ℝ} (hT : ∀ s s', 0 ≤ T s s') (hO : IsObsLikelihood O)
    (hb : ∀ s, 0 ≤ b s) :
    0 ≤ obsNormConst T O b :=
  sum_nonneg fun s' _ ↦ unnormBeliefUpdate_nonneg hT hO hb s'

/-- Exact Bayesian belief update preserves the probability simplex whenever $Z(b) > 0$. -/
theorem beliefUpdate_isBelief {n : ℕ} {T : Fin n → Fin n → ℝ} {O : Fin n → ℝ}
    {b : Fin n → ℝ} (hT : IsTransitionKernel T) (hO : IsObsLikelihood O)
    (hb : IsBelief b) (hZ : 0 < obsNormConst T O b) :
    IsBelief (beliefUpdate T O b) := by
  refine ⟨fun s' ↦ div_nonneg (unnormBeliefUpdate_nonneg hT.1 hO hb.1 s') (le_of_lt hZ), ?_⟩
  unfold beliefUpdate
  rw [← sum_div]
  exact div_self (ne_of_gt hZ)

/-- Pure Markov prediction ($O(s') = 1$ for all $s'$) has unit observation normalization
constant $Z(b) = 1$ for any belief $b$. -/
theorem beliefPredict_obsNormConst_eq_one {n : ℕ} {T : Fin n → Fin n → ℝ}
    {b : Fin n → ℝ} (hT : IsTransitionKernel T) (hb : IsBelief b) :
    obsNormConst T (fun _ ↦ 1) b = 1 := by
  unfold obsNormConst unnormBeliefUpdate
  simp only [one_mul]
  rw [sum_comm]
  have hinner : ∀ s : Fin n, ∑ s' : Fin n, T s s' * b s = b s := by
    intro s
    rw [← sum_mul, hT.2 s, one_mul]
  simp_rw [hinner]
  exact hb.2

/-- Pure Markov prediction preserves the belief simplex without requiring division. -/
theorem beliefPredict_isBelief {n : ℕ} {T : Fin n → Fin n → ℝ}
    {b : Fin n → ℝ} (hT : IsTransitionKernel T) (hb : IsBelief b) :
    IsBelief (unnormBeliefUpdate T (fun _ ↦ 1) b) := by
  refine ⟨fun s' ↦ unnormBeliefUpdate_nonneg hT.1 (fun _ ↦ zero_le_one) hb.1 s', ?_⟩
  exact beliefPredict_obsNormConst_eq_one hT hb

/-! ## 2. $\alpha$-Vector Representation & Piecewise-Linear Convexity (PWLC) -/

/-- The POMDP value function represented by a non-empty finite collection of $\alpha$-vectors
$\Gamma : \mathrm{Fin}\ K \to (\mathrm{Fin}\ n \to \mathbb{R})$ (with $K \ge 1$):
$$V_\Gamma(b) = \sup_{i \in \mathrm{Fin}\ K} (b \cdot \Gamma_i).$$ -/
def pomdpValue {n K : ℕ} [NeZero K] (Γ : Fin K → (Fin n → ℝ)) (b : Fin n → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun i : Fin K ↦ b ⬝ᵥ Γ i)

/-- Every hyperplane $b \cdot \Gamma_i$ is a lower bound for the POMDP value function $V_\Gamma(b)$. -/
theorem pomdpValue_ge_dot {n K : ℕ} [NeZero K] (Γ : Fin K → (Fin n → ℝ))
    (b : Fin n → ℝ) (i : Fin K) :
    b ⬝ᵥ Γ i ≤ pomdpValue Γ b :=
  le_sup' (fun j : Fin K ↦ b ⬝ᵥ Γ j) (mem_univ i)

/-- Upper bound characterization: $V_\Gamma(b) \le c$ if and only if $b \cdot \Gamma_i \le c$
for all $i \in \mathrm{Fin}\ K$. -/
theorem pomdpValue_le_iff {n K : ℕ} [NeZero K] (Γ : Fin K → (Fin n → ℝ))
    (b : Fin n → ℝ) (c : ℝ) :
    pomdpValue Γ b ≤ c ↔ ∀ i : Fin K, b ⬝ᵥ Γ i ≤ c := by
  unfold pomdpValue
  rw [sup'_le_iff]
  simp

/-- Attainability of the POMDP value function: for every belief $b$, there exists an active
$\alpha$-vector index $i^\star \in \mathrm{Fin}\ K$ such that $V_\Gamma(b) = b \cdot \Gamma_{i^\star}$. -/
theorem exists_alpha_achieving_pomdpValue {n K : ℕ} [NeZero K]
    (Γ : Fin K → (Fin n → ℝ)) (b : Fin n → ℝ) :
    ∃ i : Fin K, pomdpValue Γ b = b ⬝ᵥ Γ i := by
  unfold pomdpValue
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty (fun j : Fin K ↦ b ⬝ᵥ Γ j)
  exact ⟨i, hi⟩

/-- Linearity of the dot product over a convex combination of belief vectors:
$(\lambda b_1 + (1 - \lambda) b_2) \cdot \alpha = \lambda (b_1 \cdot \alpha) + (1 - \lambda) (b_2 \cdot \alpha)$. -/
theorem dotProduct_convex_comb {n : ℕ} (b₁ b₂ α : Fin n → ℝ) (t : ℝ) :
    (fun s ↦ t * b₁ s + (1 - t) * b₂ s) ⬝ᵥ α =
      t * (b₁ ⬝ᵥ α) + (1 - t) * (b₂ ⬝ᵥ α) := by
  change (t • b₁ + (1 - t) • b₂) ⬝ᵥ α = t * (b₁ ⬝ᵥ α) + (1 - t) * (b₂ ⬝ᵥ α)
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

/-- **Smallwood–Sondik Piecewise-Linear Convexity (PWLC) of the POMDP Value Function**:
For any collection of $\alpha$-vectors $\Gamma$, any belief vectors $b_1, b_2 : \mathrm{Fin}\ n \to \mathbb{R}$,
and any convex weight $0 \le t \le 1$,
$$V_\Gamma(t b_1 + (1 - t) b_2) \le t V_\Gamma(b_1) + (1 - t) V_\Gamma(b_2).$$ -/
theorem pomdpValue_convex {n K : ℕ} [NeZero K] (Γ : Fin K → (Fin n → ℝ))
    (b₁ b₂ : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pomdpValue Γ (fun s ↦ t * b₁ s + (1 - t) * b₂ s) ≤
      t * pomdpValue Γ b₁ + (1 - t) * pomdpValue Γ b₂ := by
  rw [pomdpValue_le_iff]
  intro i
  rw [dotProduct_convex_comb]
  have h1 : b₁ ⬝ᵥ Γ i ≤ pomdpValue Γ b₁ := pomdpValue_ge_dot Γ b₁ i
  have h2 : b₂ ⬝ᵥ Γ i ≤ pomdpValue Γ b₂ := pomdpValue_ge_dot Γ b₂ i
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ht0) (mul_le_mul_of_nonneg_left h2 h1t)

/-- Positive homogeneity of $V_\Gamma$: for $c \ge 0$, $V_\Gamma(c \cdot b) = c \cdot V_\Gamma(b)$. -/
theorem pomdpValue_smul_nonneg {n K : ℕ} [NeZero K] (Γ : Fin K → (Fin n → ℝ))
    (b : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    pomdpValue Γ (c • b) = c * pomdpValue Γ b := by
  apply le_antisymm
  · rw [pomdpValue_le_iff]
    intro i
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (pomdpValue_ge_dot Γ b i) hc
  · obtain ⟨i, hi⟩ := exists_alpha_achieving_pomdpValue Γ b
    rw [hi]
    have hge := pomdpValue_ge_dot Γ (c • b) i
    rwa [smul_dotProduct, smul_eq_mul] at hge

/-- Monotonicity of $V_\Gamma$ with respect to pointwise dominance of $\alpha$-vectors
for non-negative belief vectors. -/
theorem pomdpValue_monotone {n K : ℕ} [NeZero K] {Γ₁ Γ₂ : Fin K → (Fin n → ℝ)}
    (hΓ : ∀ i s, Γ₁ i s ≤ Γ₂ i s) {b : Fin n → ℝ} (hb : ∀ s, 0 ≤ b s) :
    pomdpValue Γ₁ b ≤ pomdpValue Γ₂ b := by
  rw [pomdpValue_le_iff]
  intro i
  calc b ⬝ᵥ Γ₁ i ≤ b ⬝ᵥ Γ₂ i := by
        unfold dotProduct
        exact sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hΓ i s) (hb s)
    _ ≤ pomdpValue Γ₂ b := pomdpValue_ge_dot Γ₂ b i

/-! ## 3. Bellman Backup Duality & Preservation of PWLC Structure -/

/-- One-step Bellman backed-up $\alpha$-vector for a fixed action with immediate reward $r$,
discount factor $\gamma$, transition kernel $T$, observation likelihood $O$, and continuation
$\alpha$-vector $\alpha_{\mathrm{next}}$:
$$\alpha_{\mathrm{back}}(s) = r(s) + \gamma \sum_{s'} T(s, s') O(s') \alpha_{\mathrm{next}}(s').$$ -/
def bellmanBackupAlpha {n : ℕ} (r : Fin n → ℝ) (γ : ℝ)
    (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ) (α_next : Fin n → ℝ) (s : Fin n) : ℝ :=
  r s + γ * ∑ s' : Fin n, T s s' * O s' * α_next s'

/-- **Bellman Backup Adjoint Duality Identity**:
The inner product of a prior belief $b$ with the backed-up $\alpha$-vector $\alpha_{\mathrm{back}}$
equals the immediate expected reward $b \cdot r$ plus the discounted inner product of the
unnormalized posterior belief $\tilde{b}$ with $\alpha_{\mathrm{next}}$:
$$b \cdot \alpha_{\mathrm{back}} = b \cdot r + \gamma \bigl(\tilde{b} \cdot \alpha_{\mathrm{next}}\bigr).$$ -/
theorem bellman_backup_alpha_eq {n : ℕ} (r : Fin n → ℝ) (γ : ℝ)
    (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ) (α_next : Fin n → ℝ) (b : Fin n → ℝ) :
    b ⬝ᵥ bellmanBackupAlpha r γ T O α_next =
      b ⬝ᵥ r + γ * (unnormBeliefUpdate T O b ⬝ᵥ α_next) := by
  unfold dotProduct bellmanBackupAlpha unnormBeliefUpdate
  simp_rw [mul_add, sum_add_distrib, ← mul_assoc, mul_sum, sum_mul]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s' _ ↦ sum_congr rfl fun s _ ↦ ?_
  ring

/-- Normalized posterior scaling identity: for $Z(b) > 0$,
$\tilde{b} \cdot \alpha_{\mathrm{next}} = Z(b) \cdot \bigl(\mathrm{beliefUpdate}(T, O, b) \cdot \alpha_{\mathrm{next}}\bigr)$. -/
theorem unnorm_dot_eq_obsNormConst_mul_beliefUpdate_dot {n : ℕ}
    (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ) (α_next : Fin n → ℝ) (b : Fin n → ℝ)
    (hZ : obsNormConst T O b ≠ 0) :
    unnormBeliefUpdate T O b ⬝ᵥ α_next =
      obsNormConst T O b * (beliefUpdate T O b ⬝ᵥ α_next) := by
  unfold dotProduct beliefUpdate
  rw [mul_sum]
  refine sum_congr rfl fun s' _ ↦ ?_
  rw [← mul_assoc, mul_div_cancel₀ _ hZ]

/-- **Normalized Bellman Backup Linear Identity**:
Whenever $Z(b) \ne 0$, evaluating the backed-up $\alpha$-vector at prior belief $b$ equals
the expected immediate reward plus $\gamma Z(b)$ times the continuation value at the normalized
posterior belief $b^+$:
$$b \cdot \alpha_{\mathrm{back}} = b \cdot r + \gamma Z(b) \bigl(b^+ \cdot \alpha_{\mathrm{next}}\bigr).$$ -/
theorem bellman_backup_normalized_eq {n : ℕ} (r : Fin n → ℝ) (γ : ℝ)
    (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ) (α_next : Fin n → ℝ) (b : Fin n → ℝ)
    (hZ : obsNormConst T O b ≠ 0) :
    b ⬝ᵥ bellmanBackupAlpha r γ T O α_next =
      b ⬝ᵥ r + γ * obsNormConst T O b * (beliefUpdate T O b ⬝ᵥ α_next) := by
  rw [bellman_backup_alpha_eq,
      unnorm_dot_eq_obsNormConst_mul_beliefUpdate_dot T O α_next b hZ, mul_assoc]

/-- **Smallwood–Sondik PWLC Preservation Under Bellman Backup**:
Given a continuation $\alpha$-vector family $\Gamma : \mathrm{Fin}\ K \to (\mathrm{Fin}\ n \to \mathbb{R})$,
let $\Gamma_{\mathrm{back}}(i) = \mathrm{bellmanBackupAlpha}(r, \gamma, T, O, \Gamma(i))$.
Then for any belief $b$ with $Z(b) > 0$ and $\gamma \ge 0$, the one-step Bellman backup of the
PWLC value function $V_\Gamma$ equals the PWLC value function of the backed-up $\alpha$-vectors:
$$b \cdot r + \gamma Z(b) V_\Gamma(\mathrm{beliefUpdate}\ T\ O\ b) = V_{\Gamma_{\mathrm{back}}}(b).$$ -/
theorem bellman_backup_pwlc_preservation {n K : ℕ} [NeZero K]
    (r : Fin n → ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (T : Fin n → Fin n → ℝ) (O : Fin n → ℝ)
    (Γ : Fin K → (Fin n → ℝ)) (b : Fin n → ℝ)
    (hZ : 0 < obsNormConst T O b) :
    b ⬝ᵥ r + γ * obsNormConst T O b * pomdpValue Γ (beliefUpdate T O b) =
      pomdpValue (fun i ↦ bellmanBackupAlpha r γ T O (Γ i)) b := by
  have hZ_ne : obsNormConst T O b ≠ 0 := ne_of_gt hZ
  have hγZ_nonneg : 0 ≤ γ * obsNormConst T O b := mul_nonneg hγ (le_of_lt hZ)
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_alpha_achieving_pomdpValue Γ (beliefUpdate T O b)
    rw [hi, ← bellman_backup_normalized_eq r γ T O (Γ i) b hZ_ne]
    exact pomdpValue_ge_dot (fun j ↦ bellmanBackupAlpha r γ T O (Γ j)) b i
  · rw [pomdpValue_le_iff]
    intro i
    rw [bellman_backup_normalized_eq r γ T O (Γ i) b hZ_ne]
    have hle := pomdpValue_ge_dot Γ (beliefUpdate T O b) i
    linarith [mul_le_mul_of_nonneg_left hle hγZ_nonneg]

end ControlsLean.Estimation.POMDPBelief
