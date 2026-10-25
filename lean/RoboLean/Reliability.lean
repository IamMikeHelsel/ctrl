import Mathlib

/-!
# Reliability and safety-critical control

Sorry-free formal results for high-assurance control architectures:

1. **Simplex architecture** (Sha et al.): an unverified, possibly adversarial high-performance
   controller is wrapped by a verified safety controller and a one-step look-ahead switch.
   The closed loop never leaves the recoverable set `C ⊆ S`.
2. **Discrete-time control barrier functions** (CBFs) and the CBF **safety filter**.
3. **Stability under (m,K)-firm deadline misses** for a control task that sometimes fails to
   update the actuator.
4. **Redundancy**: TMR, N-modular redundancy (with `NMR → 1`), series/parallel reliability.
5. **Watchdog / heartbeat** detection latency.
6. **Fault-tolerant sensor fusion**: the trimmed (Marzullo/Lamport style) mean of `n` readings,
   at most `f` of which are Byzantine, lies within the range of the correct readings.

Stability.lean covers basic Lyapunov theory; nothing here duplicates it.
-/

open Finset Filter Topology

namespace Reliability

/-! ## 1. Simplex architecture -/

section Simplex

variable {X U : Type*}

open Classical in
/-- **Simplex decision module.** Given plant `f`, recoverable set `C`, verified safety
controller `s`, current state `x` and the untrusted controller's proposal `uh`, apply `uh`
iff the one-step prediction `f x uh` stays in `C`; otherwise apply the safety input `s x`. -/
noncomputable def simplexInput (f : X → U → X) (C : Set X) (s : X → U) (x : X) (uh : U) : U :=
  if f x uh ∈ C then uh else s x

/-- Closed-loop Simplex trajectory. The untrusted controller `h : ℕ → X → U` is completely
arbitrary and may change with time (a learning-enabled / AI controller, or an adversary). -/
noncomputable def simplexTraj (f : X → U → X) (C : Set X) (s : X → U) (h : ℕ → X → U)
    (x₀ : X) : ℕ → X
  | 0 => x₀
  | k + 1 =>
    let x := simplexTraj f C s h x₀ k
    f x (simplexInput f C s x (h k x))

/-- **Performance preservation.** Whenever the untrusted proposal is itself recoverable, the
Simplex switch passes it through unchanged: the safety layer never overrides a good command. -/
theorem simplexInput_of_mem {f : X → U → X} {C : Set X} {s : X → U} {x : X} {uh : U}
    (h : f x uh ∈ C) : simplexInput f C s x uh = uh := by
  classical
  simp [simplexInput, h]

/-- One Simplex step from a recoverable state lands in a recoverable state, for **every**
proposal `uh` of the untrusted controller. -/
theorem simplex_step_mem {f : X → U → X} {C : Set X} {s : X → U}
    (hsafe : ∀ x ∈ C, f x (s x) ∈ C) {x : X} (hx : x ∈ C) (uh : U) :
    f x (simplexInput f C s x uh) ∈ C := by
  classical
  unfold simplexInput
  split_ifs with h
  · exact h
  · exact hsafe x hx

/-- **Simplex safety theorem.** Let `C ⊆ S` be invariant under the verified safety controller
`s` (`x ∈ C → f x (s x) ∈ C`). Then from any `x₀ ∈ C` the Simplex closed loop stays in `C`,
hence in the safe set `S`, forever — **no matter what** the untrusted controller `h` does.
Engineering reading: an unverified (e.g. neural-network) controller may be deployed, because
the verified fallback plus the look-ahead switch alone guarantee safety. -/
theorem simplex_safe {f : X → U → X} {C S : Set X} {s : X → U}
    (hCS : C ⊆ S) (hsafe : ∀ x ∈ C, f x (s x) ∈ C) (h : ℕ → X → U) {x₀ : X} (hx₀ : x₀ ∈ C)
    (k : ℕ) : simplexTraj f C s h x₀ k ∈ C ∧ simplexTraj f C s h x₀ k ∈ S := by
  have : simplexTraj f C s h x₀ k ∈ C := by
    induction k with
    | zero => exact hx₀
    | succ k ih => exact simplex_step_mem hsafe ih _
  exact ⟨this, hCS this⟩

/-- **History-dependent Simplex (most general form).** Any input sequence `u` such that at
every step either the successor is recoverable, or the verified safety input was applied,
keeps the plant in `C ⊆ S`. This covers untrusted controllers with memory, randomness, or
full knowledge of the past, and supervisors with any tie-breaking rule. -/
theorem simplex_safe_general {f : X → U → X} {C S : Set X} {s : X → U}
    (hCS : C ⊆ S) (hsafe : ∀ x ∈ C, f x (s x) ∈ C) {x : ℕ → X} {u : ℕ → U}
    (hdyn : ∀ k, x (k + 1) = f (x k) (u k))
    (hrule : ∀ k, f (x k) (u k) ∈ C ∨ u k = s (x k)) (hx₀ : x 0 ∈ C) (k : ℕ) :
    x k ∈ C ∧ x k ∈ S := by
  have : x k ∈ C := by
    induction k with
    | zero => exact hx₀
    | succ k ih =>
      rw [hdyn k]
      rcases hrule k with h | h
      · exact h
      · rw [h]; exact hsafe _ ih
  exact ⟨this, hCS this⟩

end Simplex

/-! ## 2. Discrete-time control barrier functions -/

section CBF

variable {X U : Type*}

/-- **CBF decay bound along any trajectory.** If the barrier value `hb` satisfies the discrete
CBF condition `hb(x_{k+1}) ≥ (1-γ) hb(x_k)` with `γ ≤ 1`, then
`hb(x_k) ≥ (1-γ)^k hb(x_0)`: the safety margin can shrink at most geometrically. -/
theorem cbf_lower_bound {hb : X → ℝ} {γ : ℝ} (hγ1 : γ ≤ 1) {x : ℕ → X}
    (hdec : ∀ k, (1 - γ) * hb (x k) ≤ hb (x (k + 1))) (k : ℕ) :
    (1 - γ) ^ k * hb (x 0) ≤ hb (x k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (1 - γ) ^ (k + 1) * hb (x 0) = (1 - γ) * ((1 - γ) ^ k * hb (x 0)) := by ring
      _ ≤ (1 - γ) * hb (x k) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ _ := hdec k

/-- **Forward invariance of the safe set `{hb ≥ 0}`** (`0 < γ ≤ 1`, in fact any `γ ≤ 1`). -/
theorem cbf_invariant {hb : X → ℝ} {γ : ℝ} (hγ1 : γ ≤ 1) {x : ℕ → X}
    (hdec : ∀ k, (1 - γ) * hb (x k) ≤ hb (x (k + 1))) (h0 : 0 ≤ hb (x 0)) (k : ℕ) :
    0 ≤ hb (x k) :=
  (mul_nonneg (pow_nonneg (by linarith) _) h0).trans (cbf_lower_bound hγ1 hdec k)

/-- **Strict safety margin is preserved** when `γ < 1`: if `hb(x_0) > 0` then `hb(x_k) > 0`
for all `k`. (For `γ = 1` the condition only says `hb(x_{k+1}) ≥ 0`, so positivity can be lost
in one step; strictness genuinely needs `γ < 1`.) -/
theorem cbf_positive {hb : X → ℝ} {γ : ℝ} (hγ1 : γ < 1) {x : ℕ → X}
    (hdec : ∀ k, (1 - γ) * hb (x k) ≤ hb (x (k + 1))) (h0 : 0 < hb (x 0)) (k : ℕ) :
    0 < hb (x k) :=
  (mul_pos (pow_pos (by linarith) _) h0).trans_le (cbf_lower_bound hγ1.le hdec k)

/-- Closed-loop CBF theorem for a state-feedback law `u`: if
`hb (f x (u x)) ≥ (1-γ) hb x` for all `x`, then `{hb ≥ 0}` is forward invariant under
`x ↦ f x (u x)`. -/
theorem cbf_closed_loop_invariant {f : X → U → X} {u : X → U} {hb : X → ℝ} {γ : ℝ}
    (hγ1 : γ ≤ 1) (hcbf : ∀ x, (1 - γ) * hb x ≤ hb (f x (u x))) {x₀ : X} (h0 : 0 ≤ hb x₀)
    (k : ℕ) : 0 ≤ hb ((fun x => f x (u x))^[k] x₀) :=
  cbf_invariant (x := fun k => (fun x => f x (u x))^[k] x₀) hγ1
    (fun k => by simp only [Function.iterate_succ_apply']; exact hcbf _) h0 k

/-- The CBF **admissible input set** `K(x) = {u | hb(f x u) ≥ (1-γ) hb(x)}`. -/
def cbfAdmissible (f : X → U → X) (hb : X → ℝ) (γ : ℝ) (x : X) : Set U :=
  {u | (1 - γ) * hb x ≤ hb (f x u)}

/-- **CBF safety filter.** Any input sequence (possibly from an untrusted, time-varying,
history-dependent controller, projected/filtered online) that is chosen inside the admissible
set `K(x_k)` at every step keeps the system in `{hb ≥ 0}` forever. -/
theorem cbf_filter_safe {f : X → U → X} {hb : X → ℝ} {γ : ℝ} (hγ1 : γ ≤ 1) {x : ℕ → X}
    {u : ℕ → U} (hdyn : ∀ k, x (k + 1) = f (x k) (u k))
    (hadm : ∀ k, u k ∈ cbfAdmissible f hb γ (x k)) (h0 : 0 ≤ hb (x 0)) (k : ℕ) :
    0 ≤ hb (x k) :=
  cbf_invariant hγ1 (fun k => by rw [hdyn k]; exact hadm k) h0 k

/-- Strict version of the safety filter (`γ < 1`, `hb(x_0) > 0`). -/
theorem cbf_filter_positive {f : X → U → X} {hb : X → ℝ} {γ : ℝ} (hγ1 : γ < 1) {x : ℕ → X}
    {u : ℕ → U} (hdyn : ∀ k, x (k + 1) = f (x k) (u k))
    (hadm : ∀ k, u k ∈ cbfAdmissible f hb γ (x k)) (h0 : 0 < hb (x 0)) (k : ℕ) :
    0 < hb (x k) :=
  cbf_positive hγ1 (fun k => by rw [hdyn k]; exact hadm k) h0 k

open Classical in
/-- **Minimal-intervention filter**: pass the nominal command if admissible, else use a
certified backup law. -/
noncomputable def cbfFilter (f : X → U → X) (hb : X → ℝ) (γ : ℝ) (backup : X → U) (x : X)
    (unom : U) : U :=
  if unom ∈ cbfAdmissible f hb γ x then unom else backup x

/-- If the backup law is a valid CBF controller, the minimal-intervention filter always
returns an admissible input, whatever the nominal command. -/
theorem cbfFilter_mem {f : X → U → X} {hb : X → ℝ} {γ : ℝ} {backup : X → U}
    (hb_ok : ∀ x, backup x ∈ cbfAdmissible f hb γ x) (x : X) (unom : U) :
    cbfFilter f hb γ backup x unom ∈ cbfAdmissible f hb γ x := by
  classical
  unfold cbfFilter
  split_ifs with h
  · exact h
  · exact hb_ok x

end CBF

/-! ## 3. Stability under (m,K)-firm deadline misses

Model: on a deadline *hit* the closed-loop map `A_c` is applied, on a *miss* the open-loop map
`A_o` (input held / zeroed). With `a = ‖A_o‖`, `c = ‖A_c‖`, a window of `K` periods with
`j ≤ m` misses has gain at most `a^j c^(K-j)`. Its worst case over `j ≤ m` is
`ρ = max(a,c)^m · c^(K-m)` (equal to `a^m c^(K-m)` if `a ≥ c`, to `c^K` if `a ≤ c`).
The sufficient condition is `ρ < 1`. -/



/-- Worst-case gain of a window of `K` periods containing `j ≤ m` misses. -/
theorem window_gain_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {m K j : ℕ} (hjm : j ≤ m) (hmK : m ≤ K) :
    a ^ j * c ^ (K - j) ≤ max a c ^ m * c ^ (K - m) := by
  have hM : 0 ≤ max a c := le_trans ha (le_max_left _ _)
  calc a ^ j * c ^ (K - j) ≤ max a c ^ j * c ^ (K - j) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha (le_max_left _ _) _) (pow_nonneg hc _)
    _ = max a c ^ j * c ^ (m - j) * c ^ (K - m) := by
        rw [mul_assoc, ← pow_add]; congr 2; omega
    _ ≤ max a c ^ j * max a c ^ (m - j) * c ^ (K - m) := by
        gcongr
        · exact le_max_right _ _
    _ = _ := by rw [← pow_add]; congr 2; omega

/-- Gain over `L` consecutive periods is at most the product of per-period gains. -/
theorem firm_window {v : ℕ → ℝ} {miss : ℕ → Prop} [DecidablePred miss] {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hstep : ∀ k, v (k + 1) ≤ (if miss k then a else c) * v k) (n L : ℕ) :
    v (n + L) ≤ (∏ i ∈ Ico n (n + L), if miss i then a else c) * v n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega)]
    calc v (n + L + 1) ≤ (if miss (n + L) then a else c) * v (n + L) := hstep _
      _ ≤ (if miss (n + L) then a else c) * ((∏ i ∈ Ico n (n + L), if miss i then a else c) * v n) :=
          mul_le_mul_of_nonneg_left ih (by split_ifs <;> assumption)
      _ = _ := by ring

/-- A window with at most `m` misses has gain at most `ρ = max(a,c)^m c^(K-m)`. -/
theorem firm_prod_le {miss : ℕ → Prop} [DecidablePred miss] {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) {m K : ℕ} (hmK : m ≤ K) (n : ℕ)
    (hwin : #{i ∈ Ico n (n + K) | miss i} ≤ m) :
    (∏ i ∈ Ico n (n + K), if miss i then a else c) ≤ max a c ^ m * c ^ (K - m) := by
  rw [Finset.prod_ite, prod_const, prod_const]
  have hcard : #{i ∈ Ico n (n + K) | ¬ miss i} = K - #{i ∈ Ico n (n + K) | miss i} := by
    have := Finset.card_filter_add_card_filter_not (s := Ico n (n + K)) miss
    rw [Nat.card_Ico, add_tsub_cancel_left] at this
    exact Nat.eq_sub_of_add_eq' this
  rw [hcard]
  exact window_gain_le ha hc hwin hmK

/-- Geometric decay at window boundaries: `v(nK) ≤ ρ^n v(0)`. -/
theorem firm_geometric {v : ℕ → ℝ} {miss : ℕ → Prop} [DecidablePred miss] {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hv : ∀ k, 0 ≤ v k)
    (hstep : ∀ k, v (k + 1) ≤ (if miss k then a else c) * v k) {m K : ℕ} (hmK : m ≤ K)
    (hwin : ∀ n, #{i ∈ Ico n (n + K) | miss i} ≤ m) (n : ℕ) :
    v (n * K) ≤ (max a c ^ m * c ^ (K - m)) ^ n * v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hρ : 0 ≤ max a c ^ m * c ^ (K - m) :=
      mul_nonneg (pow_nonneg (le_trans ha (le_max_left _ _)) _) (pow_nonneg hc _)
    calc v ((n + 1) * K) = v (n * K + K) := by ring_nf
      _ ≤ (∏ i ∈ Ico (n * K) (n * K + K), if miss i then a else c) * v (n * K) :=
          firm_window ha hc hstep _ _
      _ ≤ (max a c ^ m * c ^ (K - m)) * ((max a c ^ m * c ^ (K - m)) ^ n * v 0) :=
          mul_le_mul (firm_prod_le ha hc hmK _ (hwin _)) ih (hv _) hρ
      _ = _ := by ring

/-- **Explicit exponential bound**: `v k ≤ max(1,a,c)^K · ρ^⌊k/K⌋ · v 0`. -/
theorem firm_bound {v : ℕ → ℝ} {miss : ℕ → Prop} [DecidablePred miss] {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hv : ∀ k, 0 ≤ v k)
    (hstep : ∀ k, v (k + 1) ≤ (if miss k then a else c) * v k) {m K : ℕ} (hmK : m ≤ K)
    (hK : 0 < K) (hwin : ∀ n, #{i ∈ Ico n (n + K) | miss i} ≤ m) (k : ℕ) :
    v k ≤ max 1 (max a c) ^ K * (max a c ^ m * c ^ (K - m)) ^ (k / K) * v 0 := by
  set B := max 1 (max a c)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  -- one-step gain is at most `B`
  have hstepB : ∀ j, v (j + 1) ≤ B * v j := fun j => (hstep j).trans <|
    mul_le_mul_of_nonneg_right (by
      split_ifs
      · exact (le_max_left a c).trans (le_max_right _ _)
      · exact (le_max_right a c).trans (le_max_right _ _)) (hv j)
  have hgrow : ∀ j r, v (j + r) ≤ B ^ r * v j := by
    intro j r
    induction r with
    | zero => simp
    | succ r ih =>
      calc v (j + (r + 1)) = v ((j + r) + 1) := by ring_nf
        _ ≤ B * v (j + r) := hstepB _
        _ ≤ B * (B ^ r * v j) := mul_le_mul_of_nonneg_left ih hB0
        _ = B ^ (r + 1) * v j := by ring
  have hk : k = k / K * K + k % K := by rw [Nat.div_add_mod']
  calc v k = v (k / K * K + k % K) := by rw [← hk]
    _ ≤ B ^ (k % K) * v (k / K * K) := hgrow _ _
    _ ≤ B ^ K * ((max a c ^ m * c ^ (K - m)) ^ (k / K) * v 0) :=
        mul_le_mul (pow_le_pow_right₀ hB1 (Nat.mod_lt _ hK).le)
          (firm_geometric ha hc hv hstep hmK hwin _) (hv _) (pow_nonneg hB0 _)
    _ = _ := by ring

/-- Under `ρ < 1`, any nonnegative "Lyapunov-norm" sequence obeying the hit/miss gain
bounds converges to `0`. -/
theorem firm_tendsto_zero {v : ℕ → ℝ} {miss : ℕ → Prop} [DecidablePred miss] {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hv : ∀ k, 0 ≤ v k)
    (hstep : ∀ k, v (k + 1) ≤ (if miss k then a else c) * v k) {m K : ℕ} (hmK : m ≤ K)
    (hK : 0 < K) (hwin : ∀ n, #{i ∈ Ico n (n + K) | miss i} ≤ m)
    (hρ : max a c ^ m * c ^ (K - m) < 1) :
    Tendsto v atTop (𝓝 0) := by
  have hρ0 : 0 ≤ max a c ^ m * c ^ (K - m) :=
    mul_nonneg (pow_nonneg (le_trans ha (le_max_left _ _)) _) (pow_nonneg hc _)
  have h1 : Tendsto (fun k => (max a c ^ m * c ^ (K - m)) ^ (k / K)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).comp (Nat.tendsto_div_const_atTop hK.ne')
  have h2 : Tendsto (fun k => max 1 (max a c) ^ K * (max a c ^ m * c ^ (K - m)) ^ (k / K) * v 0)
      atTop (𝓝 0) := by
    simpa using (h1.const_mul (max 1 (max a c) ^ K)).mul_const (v 0)
  exact squeeze_zero hv (firm_bound ha hc hv hstep hmK hK hwin) h2

section Operators

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **(m,K)-firm stability theorem** for linear control loops on any normed space (e.g.
`EuclideanSpace`, with operator norms). If in every window of `K` consecutive periods at most
`m` deadlines are missed, and `max(‖A_o‖,‖A_c‖)^m · ‖A_c‖^(K-m) < 1`, then the state
converges to `0` (exponentially, by `firm_operator_bound`) for every miss pattern. -/
theorem firm_operator_tendsto {Ac Ao : E →L[𝕜] E} {miss : ℕ → Prop} [DecidablePred miss]
    {x : ℕ → E} (hx : ∀ k, x (k + 1) = (if miss k then Ao else Ac) (x k)) {m K : ℕ}
    (hmK : m ≤ K) (hK : 0 < K) (hwin : ∀ n, #{i ∈ Ico n (n + K) | miss i} ≤ m)
    (hρ : max ‖Ao‖ ‖Ac‖ ^ m * ‖Ac‖ ^ (K - m) < 1) :
    Tendsto x atTop (𝓝 0) := by
  have := firm_tendsto_zero (v := fun k => ‖x k‖) (miss := miss) (norm_nonneg Ao) (norm_nonneg Ac)
    (fun k => norm_nonneg _) (fun k => by
      rw [hx k]; split_ifs <;> exact ContinuousLinearMap.le_opNorm _ _) hmK hK hwin hρ
  exact tendsto_zero_iff_norm_tendsto_zero.mpr this

/-- Explicit exponential envelope for the operator version. -/
theorem firm_operator_bound {Ac Ao : E →L[𝕜] E} {miss : ℕ → Prop} [DecidablePred miss]
    {x : ℕ → E} (hx : ∀ k, x (k + 1) = (if miss k then Ao else Ac) (x k)) {m K : ℕ}
    (hmK : m ≤ K) (hK : 0 < K) (hwin : ∀ n, #{i ∈ Ico n (n + K) | miss i} ≤ m) (k : ℕ) :
    ‖x k‖ ≤ max 1 (max ‖Ao‖ ‖Ac‖) ^ K * (max ‖Ao‖ ‖Ac‖ ^ m * ‖Ac‖ ^ (K - m)) ^ (k / K) *
      ‖x 0‖ :=
  firm_bound (v := fun k => ‖x k‖) (miss := miss) (norm_nonneg Ao) (norm_nonneg Ac)
    (fun k => norm_nonneg _) (fun k => by
      rw [hx k]; split_ifs <;> exact ContinuousLinearMap.le_opNorm _ _) hmK hK hwin k

end Operators

/-- When missing is worse than hitting (`c ≤ a`), the rate is the familiar `a^m c^(K-m)`. -/
theorem firm_rate_of_le {a c : ℝ} (h : c ≤ a) (m K : ℕ) :
    max a c ^ m * c ^ (K - m) = a ^ m * c ^ (K - m) := by rw [max_eq_left h]

/-- When missing is better than hitting (`a ≤ c`), the worst window has no misses: `c^K`. -/
theorem firm_rate_of_ge {a c : ℝ} (h : a ≤ c) {m K : ℕ} (hmK : m ≤ K) :
    max a c ^ m * c ^ (K - m) = c ^ K := by
  rw [max_eq_right h, ← pow_add]; congr 1; omega



/-! ## 4. Redundancy -/

/-- **Triple modular redundancy** with a perfect voter: the system works iff at least 2 of 3
independent modules (each with reliability `p`) work. -/
def tmr (p : ℝ) : ℝ := p ^ 3 + 3 * p ^ 2 * (1 - p)

/-- Classic closed form `R_TMR = 3p² − 2p³`. -/
theorem tmr_eq (p : ℝ) : tmr p = 3 * p ^ 2 - 2 * p ^ 3 := by unfold tmr; ring

/-- `R_TMR − p = p (2p−1)(1−p)`. -/
theorem tmr_sub (p : ℝ) : tmr p - p = p * (2 * p - 1) * (1 - p) := by unfold tmr; ring

/-- **TMR helps iff `1/2 < p < 1`**: triplication improves on a single module exactly
when modules are better than a coin flip (and not already perfect). -/
theorem tmr_gt_iff {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p < tmr p ↔ 1 / 2 < p ∧ p < 1 := by
  rw [← sub_pos, tmr_sub]
  constructor
  · intro h
    rcases h0.lt_or_eq with hp | hp
    · have : 0 < (2 * p - 1) * (1 - p) := by
        have := h; rw [mul_assoc] at this; exact pos_of_mul_pos_right this hp.le
      rcases h1.lt_or_eq with hq | hq
      · have := (pos_iff_pos_of_mul_pos this).mpr (by linarith)
        constructor <;> linarith
      · subst hq; norm_num at this
    · subst hp; simp at h
  · rintro ⟨ha, hb⟩
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- **N-modular redundancy**, `N = 2k+1` independent modules, majority vote: probability that
at least `k+1` modules work (binomial tail). -/
noncomputable def nmr (k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Ioc k (2 * k + 1), ((2 * k + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (2 * k + 1 - i)

/-- NMR with `k = 1` is TMR. -/
theorem nmr_one (p : ℝ) : nmr 1 p = tmr p := by
  unfold nmr tmr
  rw [show Ioc 1 (2 * 1 + 1) = {2, 3} by decide, sum_pair (by norm_num)]
  norm_num [Nat.choose]
  ring

/-- NMR failure probability = lower binomial tail (at most `k` modules working). -/
theorem nmr_failure (k : ℕ) (p : ℝ) :
    1 - nmr k p = ∑ i ∈ range (k + 1),
      ((2 * k + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (2 * k + 1 - i) := by
  have h := add_pow p (1 - p) (2 * k + 1)
  rw [add_sub_cancel, one_pow] at h
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => ((2 * k + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (2 * k + 1 - i))
    (show k + 1 ≤ 2 * k + 1 + 1 by omega)
  rw [Finset.Ico_add_one_add_one_eq_Ioc] at hsplit
  have h' : (1 : ℝ) = ∑ i ∈ range (2 * k + 1 + 1),
      ((2 * k + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (2 * k + 1 - i) := by
    exact h.trans (sum_congr rfl fun i _ => by ring)
  unfold nmr
  linarith

/-- Each failure term is at most `(pq)^k q` when `q = 1−p ≤ p`. -/
theorem nmr_term_le {p : ℝ} (hq0 : 0 ≤ 1 - p) (hqp : 1 - p ≤ p) {k i : ℕ} (hi : i ≤ k) :
    p ^ i * (1 - p) ^ (2 * k + 1 - i) ≤ (p * (1 - p)) ^ k * (1 - p) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hp0 : 0 ≤ p := hq0.trans hqp
  rw [show 2 * (i + j) + 1 - i = i + 2 * j + 1 by omega]
  generalize 1 - p = q at hq0 hqp ⊢
  calc p ^ i * q ^ (i + 2 * j + 1) = (p * q) ^ i * (q * q) ^ j * q := by
        rw [mul_pow, mul_pow, pow_add, pow_add, pow_mul]; ring
    _ ≤ (p * q) ^ i * (p * q) ^ j * q := by
        gcongr
    _ = _ := by ring

/-- **Chernoff-type bound**: NMR failure `≤ 2 (4p(1−p))^k`, exponentially small in `k`
for `p > 1/2`. -/
theorem nmr_failure_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    1 - nmr k p ≤ 2 * (4 * (p * (1 - p))) ^ k := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hqp : 1 - p ≤ p := by linarith
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg (by linarith) hq0
  rw [nmr_failure]
  calc ∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (2 * k + 1 - i)
      ≤ ∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ) * ((p * (1 - p)) ^ k * (1 - p)) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (nmr_term_le hq0 hqp (by simp at hi; omega))
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ)) * ((p * (1 - p)) ^ k * (1 - p)) := by
        rw [sum_mul]
    _ ≤ (2 : ℝ) ^ (2 * k + 1) * ((p * (1 - p)) ^ k * 1) := by
        gcongr
        · calc ∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ)
              ≤ ∑ i ∈ range (2 * k + 1 + 1), ((2 * k + 1).choose i : ℝ) :=
                sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
                  (fun _ _ _ => Nat.cast_nonneg _)
            _ = 2 ^ (2 * k + 1) := by exact_mod_cast Nat.sum_range_choose (2 * k + 1)
        · linarith
    _ = 2 * (4 * (p * (1 - p))) ^ k := by
        rw [mul_pow (4 : ℝ), pow_succ, pow_mul]; norm_num; ring

/-- **NMR → 1**: with module reliability `p > 1/2`, majority-voted `(2k+1)`-modular
redundancy becomes arbitrarily reliable as `k → ∞`. -/
theorem nmr_tendsto_one {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) :
    Tendsto (fun k => nmr k p) atTop (𝓝 1) := by
  have hr0 : 0 ≤ 4 * (p * (1 - p)) := by nlinarith
  have hr1 : 4 * (p * (1 - p)) < 1 := by nlinarith
  have hfail : Tendsto (fun k => 1 - nmr k p) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => ?_) (nmr_failure_le hp.le hp1)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul 2)
    rw [nmr_failure]
    exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (by linarith) _)) (pow_nonneg (by linarith) _)
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hfail
  simpa using this


section SeriesParallel

variable {ι : Type*}

/-- Reliability of a **series** system (all independent components must work). -/
def seriesRel (s : Finset ι) (p : ι → ℝ) : ℝ := ∏ i ∈ s, p i
/-- Reliability of a **parallel** (redundant) system (at least one component must work). -/
def parallelRel (s : Finset ι) (p : ι → ℝ) : ℝ := 1 - ∏ i ∈ s, (1 - p i)

/-- A series system is no more reliable than its weakest component. -/
theorem seriesRel_le {s : Finset ι} {p : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    {j : ι} (hj : j ∈ s) : seriesRel s p ≤ p j := by
  classical
  unfold seriesRel
  rw [← mul_prod_erase s p hj]
  exact mul_le_of_le_one_right (h0 j hj) (prod_le_one (fun i hi => h0 i (mem_of_mem_erase hi))
    (fun i hi => h1 i (mem_of_mem_erase hi)))

/-- A parallel system is at least as reliable as each component. -/
theorem le_parallelRel {s : Finset ι} {p : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    {j : ι} (hj : j ∈ s) : p j ≤ parallelRel s p := by
  classical
  unfold parallelRel
  rw [← mul_prod_erase s (fun i => 1 - p i) hj]
  have : ∏ i ∈ s.erase j, (1 - p i) ≤ 1 :=
    prod_le_one (fun i hi => by linarith [h1 i (mem_of_mem_erase hi)])
      (fun i hi => by linarith [h0 i (mem_of_mem_erase hi)])
  nlinarith [h1 j hj]

/-- Series reliability is a probability. -/
theorem seriesRel_mem_Icc {s : Finset ι} {p : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) : seriesRel s p ∈ Set.Icc 0 1 :=
  ⟨prod_nonneg h0, prod_le_one h0 h1⟩

/-- Parallel reliability is a probability. -/
theorem parallelRel_mem_Icc {s : Finset ι} {p : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) : parallelRel s p ∈ Set.Icc 0 1 := by
  have a : 0 ≤ ∏ i ∈ s, (1 - p i) := prod_nonneg fun i hi => by linarith [h1 i hi]
  have b : ∏ i ∈ s, (1 - p i) ≤ 1 :=
    prod_le_one (fun i hi => by linarith [h1 i hi]) (fun i hi => by linarith [h0 i hi])
  unfold parallelRel; constructor <;> linarith

/-- Series ≤ parallel for the same nonempty set of components. -/
theorem seriesRel_le_parallelRel {s : Finset ι} {p : ι → ℝ} (hs : s.Nonempty)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) : seriesRel s p ≤ parallelRel s p := by
  obtain ⟨j, hj⟩ := hs
  exact (seriesRel_le h0 h1 hj).trans (le_parallelRel h0 h1 hj)

/-- **Parallel ≥ max**: redundancy is at least as good as the best single component. -/
theorem parallelRel_ge_sup' {s : Finset ι} {p : ι → ℝ} (hs : s.Nonempty)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) : s.sup' hs p ≤ parallelRel s p :=
  Finset.sup'_le hs p fun _ hj => le_parallelRel h0 h1 hj

end SeriesParallel

/-! ## 5. Watchdog / heartbeat monitoring -/

/-- **Watchdog detection time.** The monitor checks for a heartbeat at times `j·T`. A fault at
time `tf` stops heartbeats; a heartbeat emitted just before the fault may still be seen until
`tf + δ` (`0 ≤ δ ≤ T`, staleness), so every check at time `≥ tf + δ` is a miss
(`watchdog_checks_miss`). The first such check has index `⌈(tf+δ)/T⌉₊`, and the fault is
declared at the `k`-th consecutive miss, i.e. at check index `⌈(tf+δ)/T⌉₊ + k − 1`. -/
noncomputable def watchdogDetect (T tf δ : ℝ) (k : ℕ) : ℝ :=
  ((⌈(tf + δ) / T⌉₊ + (k - 1) : ℕ) : ℝ) * T

/-- **Watchdog latency bound.** The fault is declared no earlier than `tf + δ` (no false
early alarm from this fault), strictly before `tf + δ + k·T`, hence with
latency `≤ (k+1)·T`. -/
theorem watchdog_latency {T tf δ : ℝ} (hT : 0 < T) (htf : 0 ≤ tf) (hδ0 : 0 ≤ δ) (hδT : δ ≤ T)
    {k : ℕ} (hk : 1 ≤ k) :
    tf + δ ≤ watchdogDetect T tf δ k ∧ watchdogDetect T tf δ k < tf + δ + k * T ∧
      watchdogDetect T tf δ k ≤ tf + (k + 1) * T := by
  unfold watchdogDetect
  have hx : 0 ≤ (tf + δ) / T := div_nonneg (by linarith) hT.le
  have hc1 := Nat.le_ceil ((tf + δ) / T)
  have hc2 := Nat.ceil_lt_add_one hx
  have hk' : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; simp
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast [hk']
  set c : ℝ := (⌈(tf + δ) / T⌉₊ : ℝ)
  have e : (tf + δ) / T * T = tf + δ := div_mul_cancel₀ _ hT.ne'
  have l1 : tf + δ ≤ c * T := by rw [← e]; exact mul_le_mul_of_nonneg_right hc1 hT.le
  have l2 : c * T < tf + δ + T := by
    have := mul_lt_mul_of_pos_right hc2 hT; rw [add_mul, e] at this; linarith
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Every check from index `⌈(tf+δ)/T⌉₊` on happens at or after `tf + δ` (so it misses). -/
theorem watchdog_checks_miss {T tf δ : ℝ} (hT : 0 < T) {j : ℕ} (hj : ⌈(tf + δ) / T⌉₊ ≤ j) :
    tf + δ ≤ (j : ℝ) * T := by
  have h1 : (tf + δ) / T ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hj)
  rwa [div_le_iff₀ hT] at h1


/-! ## 6. Fault-tolerant sensor fusion (trimmed mean)

`n` sensor readings `L` are a permutation of the correct readings `G` and at most `f`
arbitrary (Byzantine) readings `B`. Sort, discard the `f` smallest and `f` largest; every
surviving value — and hence their mean — lies within the range of the correct readings.
Only `n > 2f` is needed for nonemptiness; the stronger `n > 3f` (Dolev–Lynch–Pinter–Stark–
Weihl) is what makes iterated approximate agreement contract, which is not formalized here. -/

section TrimmedMean

open List

/-- If more than `f` readings are `≤ x`, some correct reading is `≤ x`. -/
theorem exists_good_le {L G B : List ℝ} (hperm : L ~ G ++ B) {f : ℕ} (hB : B.length ≤ f) {x : ℝ}
    (hx : f < L.countP (fun y => decide (y ≤ x))) : ∃ g ∈ G, g ≤ x := by
  rw [hperm.countP_eq, countP_append] at hx
  have hb := countP_le_length (p := fun y => decide (y ≤ x)) (l := B)
  have : 0 < G.countP (fun y => decide (y ≤ x)) := by omega
  obtain ⟨g, hg, hgx⟩ := countP_pos_iff.mp this
  exact ⟨g, hg, by simpa using hgx⟩

/-- If more than `f` readings are `≥ x`, some correct reading is `≥ x`. -/
theorem exists_good_ge {L G B : List ℝ} (hperm : L ~ G ++ B) {f : ℕ} (hB : B.length ≤ f) {x : ℝ}
    (hx : f < L.countP (fun y => decide (x ≤ y))) : ∃ g ∈ G, x ≤ g := by
  rw [hperm.countP_eq, countP_append] at hx
  have hb := countP_le_length (p := fun y => decide (x ≤ y)) (l := B)
  have : 0 < G.countP (fun y => decide (x ≤ y)) := by omega
  obtain ⟨g, hg, hgx⟩ := countP_pos_iff.mp this
  exact ⟨g, hg, by simpa using hgx⟩

/-- In a sorted list, at least `i+1` entries are `≤ s[i]`. -/
theorem sorted_countP_le {s : List ℝ} (hs : s.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < s.length) :
    i + 1 ≤ s.countP (fun y => decide (y ≤ s[i])) := by
  have hsub := (take_sublist (i + 1) s).countP_le (p := fun y => decide (y ≤ s[i]))
  have : (s.take (i + 1)).countP (fun y => decide (y ≤ s[i])) = (s.take (i + 1)).length := by
    rw [countP_eq_length]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := getElem_of_mem ha
    rw [getElem_take]
    simp only [length_take] at hj
    simp only [decide_eq_true_eq]
    rcases Nat.lt_or_ge j i with h | h
    · exact (pairwise_iff_getElem.mp hs) j i (by omega) hi h
    · have : j = i := by omega
      subst this; rfl
  rw [this, length_take] at hsub
  omega

/-- In a sorted list, at least `length − i` entries are `≥ s[i]`. -/
theorem sorted_countP_ge {s : List ℝ} (hs : s.Pairwise (· ≤ ·)) {i : ℕ} (hi : i < s.length) :
    s.length - i ≤ s.countP (fun y => decide (s[i] ≤ y)) := by
  have hsub := (drop_sublist i s).countP_le (p := fun y => decide (s[i] ≤ y))
  have : (s.drop i).countP (fun y => decide (s[i] ≤ y)) = (s.drop i).length := by
    rw [countP_eq_length]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := getElem_of_mem ha
    rw [getElem_drop]
    simp only [decide_eq_true_eq]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · exact (pairwise_iff_getElem.mp hs) i (i + j) hi _ (by omega)
  rw [this, length_drop] at hsub
  omega

/-- The fault-tolerant **trimmed list**: sort, drop the `f` smallest and `f` largest. -/
noncomputable def trimmed (L : List ℝ) (f : ℕ) : List ℝ :=
  ((L.insertionSort (· ≤ ·)).drop f).take (L.length - 2 * f)

/-- Every surviving value is bracketed by two correct readings. -/
theorem mem_trimmed_bounds {L G B : List ℝ} (hperm : L ~ G ++ B) {f : ℕ} (hB : B.length ≤ f)
    {x : ℝ} (hx : x ∈ trimmed L f) : (∃ g ∈ G, g ≤ x) ∧ (∃ g ∈ G, x ≤ g) := by
  set s := L.insertionSort (· ≤ ·) with hs_def
  have hsorted : s.Pairwise (· ≤ ·) := pairwise_insertionSort _ _
  have hsp : s ~ L := perm_insertionSort _ _
  have hlen : s.length = L.length := hsp.length_eq
  unfold trimmed at hx
  rw [← hs_def] at hx
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem hx
  simp only [length_take, length_drop] at hj
  rw [getElem_take, getElem_drop]
  have hi : f + j < s.length := by omega
  constructor
  · apply exists_good_le hperm hB
    rw [← hsp.countP_eq]
    have := sorted_countP_le hsorted hi
    omega
  · apply exists_good_ge hperm hB
    rw [← hsp.countP_eq]
    have := sorted_countP_ge hsorted hi
    omega

/-- If all correct sensors read within `[lo, hi]`, so does every surviving value. -/
theorem mem_trimmed_Icc {L G B : List ℝ} (hperm : L ~ G ++ B) {f : ℕ} (hB : B.length ≤ f)
    {lo hi : ℝ} (hG : ∀ g ∈ G, lo ≤ g ∧ g ≤ hi) {x : ℝ} (hx : x ∈ trimmed L f) :
    lo ≤ x ∧ x ≤ hi := by
  obtain ⟨⟨g₁, hg₁, h₁⟩, ⟨g₂, hg₂, h₂⟩⟩ := mem_trimmed_bounds hperm hB hx
  exact ⟨(hG g₁ hg₁).1.trans h₁, h₂.trans (hG g₂ hg₂).2⟩

/-- The trimmed list has `n − 2f` elements. -/
theorem length_trimmed (L : List ℝ) (f : ℕ) (h : 2 * f ≤ L.length) :
    (trimmed L f).length = L.length - 2 * f := by
  unfold trimmed
  simp only [length_take, length_drop, length_insertionSort]
  omega

/-- The **fault-tolerant midpoint / trimmed mean** of the readings. -/
noncomputable def trimmedMean (L : List ℝ) (f : ℕ) : ℝ :=
  (trimmed L f).sum / (trimmed L f).length

/-- **Fault-tolerant sensor fusion theorem.** With `n > 2f` readings of which at most `f`
are arbitrary (Byzantine), the trimmed mean lies in any interval `[lo, hi]` containing all
correct readings (e.g. `[min G, max G]`): faulty sensors cannot drag the fused estimate
outside the range of honest measurements. -/
theorem trimmedMean_mem_Icc {L G B : List ℝ} (hperm : L ~ G ++ B) {f : ℕ} (hB : B.length ≤ f)
    (hn : 2 * f < L.length) {lo hi : ℝ} (hG : ∀ g ∈ G, lo ≤ g ∧ g ≤ hi) :
    lo ≤ trimmedMean L f ∧ trimmedMean L f ≤ hi := by
  have hlen := length_trimmed L f hn.le
  have hpos : (0 : ℝ) < (trimmed L f).length := by rw [hlen]; exact_mod_cast (by omega)
  have h1 := card_nsmul_le_sum (trimmed L f) lo fun x hx => (mem_trimmed_Icc hperm hB hG hx).1
  have h2 := sum_le_card_nsmul (trimmed L f) hi fun x hx => (mem_trimmed_Icc hperm hB hG hx).2
  rw [nsmul_eq_mul] at h1 h2
  unfold trimmedMean
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

end TrimmedMean
end Reliability
