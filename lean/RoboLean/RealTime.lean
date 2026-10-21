import Mathlib

/-!
# Real-time scheduling theory for control loops

Uniprocessor scheduling of periodic tasks `τᵢ = (Cᵢ, Tᵢ)` (WCET `Cᵢ`, period `Tᵢ`,
implicit deadline `Dᵢ = Tᵢ`), discrete time `ℕ`, synchronous release.

Main results:
* **Response-time analysis** (Joseph–Pandya / Audsley): `rtaStep` is monotone, the iteration from
  `C` is nondecreasing, a reached fixed point is the least (pre-)fixed point, exceeding `D` rules
  out any fixed point `≤ D`; the executable `rta` is sound and complete (`rta_sound`, `rta_none`,
  `rta_isSome_iff`), with `decide` examples.
* **RTA vs. schedules**: `fp_response_le_of_rta` (abstract fixed-priority schedule, critical
  instant) and `fpSched_rta_sound` (a concrete simulated preemptive fixed-priority scheduler).
* **Utilization necessity**: `not_meets_of_utilization_gt_one` — `U > 1` ⇒ no schedule meets all
  deadlines over the hyperperiod.
* **EDF optimality / sufficiency**: job-level `IsEDF.meets_deadlines` (processor-demand criterion,
  busy-interval argument), `dbf_le_self`, and the exact test `edf_schedulable_iff`
  (`∃ feasible schedule ↔ U ≤ 1`, EDF witnessing).
* **Liu–Layland**: `rm_two_tasks_schedulable` (`U ≤ 2(√2-1)` ⇒ RM schedulable for `n = 2`, via RTA),
  `llBound_antitoneOn`, `tendsto_llBound` (`n(2^{1/n}-1) → ln 2`), `log_two_le_llBound`.
* **Control loops**: `ControlTrace` — latency `≤ R`, jitter `≤ R - C`, actuation interval within
  `T ± (R - C)`, actuation before the next release when `R ≤ T`.
-/

namespace RealTime

/-! ## Part 1: generic fixed-point iteration for monotone maps on `ℕ` -/

section FixedPoint

variable {f : ℕ → ℕ}

/-- Fuel-bounded fixed-point search: starting at `R`, stop with `none` if the current value
exceeds the bound `D` (or the fuel runs out), stop with `some R` when `f R = R`, otherwise continue
from `f R`. -/
def fixLoop (f : ℕ → ℕ) (D : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, R => if D < R then none else if f R = R then some R else fixLoop f D fuel (f R)

/-- If `R` lies below every pre-fixed point `P` (`f P ≤ P`), so does `f R` (for monotone `f`). -/
theorem le_prefix_step (hf : Monotone f) {R : ℕ} (hR : ∀ P, f P ≤ P → R ≤ P) :
    ∀ P, f P ≤ P → f R ≤ P :=
  fun P hP => (hf (hR P hP)).trans hP

/-- Soundness of `fixLoop`: a returned value is a fixed point, is at most `D`, and lies below every
pre-fixed point (hence is the least fixed point). -/
theorem fixLoop_sound (hf : Monotone f) (D : ℕ) :
    ∀ (fuel R R' : ℕ), (∀ P, f P ≤ P → R ≤ P) → fixLoop f D fuel R = some R' →
      f R' = R' ∧ R' ≤ D ∧ ∀ P, f P ≤ P → R' ≤ P := by
  intro fuel
  induction fuel with
  | zero => intro R R' _ h; simp [fixLoop] at h
  | succ n ih =>
    intro R R' hR h
    simp only [fixLoop] at h
    split_ifs at h with h1 h2
    · cases h; exact ⟨h2, Nat.le_of_not_lt h1, hR⟩
    · exact ih _ _ (le_prefix_step hf hR) h

/-- Completeness of `fixLoop`: if the search starts at a point `R` with `R ≤ f R` lying below all
pre-fixed points, and the fuel is large enough (`D < fuel + R`), then `none` means that no
pre-fixed point (in particular no fixed point) is `≤ D`. -/
theorem fixLoop_complete (hf : Monotone f) (D : ℕ) :
    ∀ (fuel R : ℕ), R ≤ f R → (∀ P, f P ≤ P → R ≤ P) → D < fuel + R →
      fixLoop f D fuel R = none → ∀ P, f P ≤ P → D < P := by
  intro fuel
  induction fuel with
  | zero => intro R _ hR hD _ P hP; have := hR P hP; omega
  | succ n ih =>
    intro R hRf hR hD h P hP
    simp only [fixLoop] at h
    split_ifs at h with h1 h2
    · exact lt_of_lt_of_le h1 (hR P hP)
    · have hlt : R < f R := lt_of_le_of_ne hRf (Ne.symm h2)
      exact ih (f R) (hf hRf) (le_prefix_step hf hR) (by omega) h P hP

/-- The iterates `f^[k] x₀` stay below every pre-fixed point `P ≥ x₀`... stated with the
hypothesis `x₀ ≤ P` for all pre-fixed points. -/
theorem iterate_le_prefix (hf : Monotone f) {x₀ : ℕ} (h0 : ∀ P, f P ≤ P → x₀ ≤ P) (k : ℕ) :
    ∀ P, f P ≤ P → f^[k] x₀ ≤ P := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    intro P hP
    rw [Function.iterate_succ_apply']
    exact le_prefix_step hf ih P hP

/-- If `x₀ ≤ f x₀` then the iteration `f^[k] x₀` is nondecreasing in `k`. -/
theorem iterate_monotone (hf : Monotone f) {x₀ : ℕ} (h0 : x₀ ≤ f x₀) :
    Monotone fun k => f^[k] x₀ := by
  apply monotone_nat_of_le_succ
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    simp only [Function.iterate_succ_apply'] at ih ⊢
    exact hf ih

end FixedPoint

/-! ## Response-time analysis for fixed-priority preemptive scheduling -/

/-- A periodic task: worst-case execution time `C` and period `T` (implicit deadline `D = T`). -/
structure Task where
  /-- worst-case execution time -/
  C : ℕ
  /-- period (= relative deadline) -/
  T : ℕ
deriving DecidableEq, Repr

/-- Ceiling division on `ℕ`: `cdiv a b = ⌈a / b⌉` for `b > 0`. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem cdiv_mono {a a' : ℕ} (b : ℕ) (h : a ≤ a') : cdiv a b ≤ cdiv a' b :=
  Nat.div_le_div_right (by omega)

/-- `cdiv (k * b) b = k`. -/
theorem cdiv_mul_self (k b : ℕ) (hb : 0 < b) : cdiv (k * b) b = k := by
  unfold cdiv
  apply Nat.div_eq_of_lt_le <;> (try simp only [add_mul, one_mul]) <;> omega

/-- `cdiv (k * b + r) b = k + 1` when `0 < r ≤ b`. -/
theorem cdiv_mul_add (k b r : ℕ) (hr : 0 < r) (hrb : r ≤ b) : cdiv (k * b + r) b = k + 1 := by
  unfold cdiv
  apply Nat.div_eq_of_lt_le <;> (try simp only [add_mul, one_mul]) <;> omega

/-- Interference from the higher-priority tasks `hp` in a window of length `R`:
`∑_{j ∈ hp} ⌈R / Tⱼ⌉ Cⱼ`. -/
def interference (hp : List Task) (R : ℕ) : ℕ :=
  (hp.map fun j => cdiv R j.T * j.C).sum

theorem interference_mono (hp : List Task) : Monotone (interference hp) := by
  intro R R' h
  induction hp with
  | nil => simp [interference]
  | cons j hp ih =>
    simp only [interference, List.map_cons, List.sum_cons] at ih ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (cdiv_mono _ h)) ih

/-- The Joseph–Pandya / Audsley response-time recurrence `R ↦ C + ∑_{j ∈ hp} ⌈R/Tⱼ⌉ Cⱼ`. -/
def rtaStep (C : ℕ) (hp : List Task) (R : ℕ) : ℕ := C + interference hp R

/-- The RTA recurrence is monotone. -/
theorem rtaStep_monotone (C : ℕ) (hp : List Task) : Monotone (rtaStep C hp) :=
  fun _ _ h => Nat.add_le_add_left (interference_mono hp h) C

theorem le_rtaStep (C : ℕ) (hp : List Task) (R : ℕ) : C ≤ rtaStep C hp R := Nat.le_add_right _ _

/-- Every pre-fixed point (in particular every fixed point) of the recurrence is `≥ C`. -/
theorem C_le_of_prefix {C : ℕ} {hp : List Task} {P : ℕ} (hP : rtaStep C hp P ≤ P) : C ≤ P :=
  (le_rtaStep C hp P).trans hP

/-- The RTA iteration `R₀ = C`, `R_{k+1} = rtaStep R_k` is nondecreasing. -/
theorem rta_iterate_monotone (C : ℕ) (hp : List Task) :
    Monotone fun k => (rtaStep C hp)^[k] C :=
  iterate_monotone (rtaStep_monotone C hp) (le_rtaStep C hp C)

/-- Every RTA iterate lies below every pre-fixed point. -/
theorem rta_iterate_le (C : ℕ) (hp : List Task) (k : ℕ) {P : ℕ} (hP : rtaStep C hp P ≤ P) :
    (rtaStep C hp)^[k] C ≤ P :=
  iterate_le_prefix (rtaStep_monotone C hp) (fun _ h => C_le_of_prefix h) k P hP

/-- If the RTA iteration reaches a fixed point `R`, then `R` is the least fixed point
(indeed the least pre-fixed point), and it is `≥ C`. -/
theorem rta_iterate_fixpoint_least (C : ℕ) (hp : List Task) (k : ℕ)
    (hfix : rtaStep C hp ((rtaStep C hp)^[k] C) = (rtaStep C hp)^[k] C) :
    C ≤ (rtaStep C hp)^[k] C ∧ ∀ P, rtaStep C hp P ≤ P → (rtaStep C hp)^[k] C ≤ P :=
  ⟨C_le_of_prefix hfix.le, fun _ hP => rta_iterate_le C hp k hP⟩

/-- If some RTA iterate exceeds the deadline `D`, then no fixed point (indeed no pre-fixed point)
is `≤ D`: the task is deemed unschedulable. -/
theorem rta_iterate_exceeds (C : ℕ) (hp : List Task) (k D : ℕ)
    (hk : D < (rtaStep C hp)^[k] C) : ∀ P, rtaStep C hp P ≤ P → D < P :=
  fun _ hP => lt_of_lt_of_le hk (rta_iterate_le C hp k hP)

/-- The response-time analysis: iterate from `C` with fuel `D + 1`; `some R` is the worst-case
response time, `none` means it exceeds the deadline `D`. -/
def rta (C : ℕ) (hp : List Task) (D : ℕ) : Option ℕ := fixLoop (rtaStep C hp) D (D + 1) C

/-- Soundness of `rta`: a returned `R` is a fixed point of the recurrence, `R ≤ D`, `C ≤ R`, and
`R` is below every (pre-)fixed point, i.e. it is the least fixed point. -/
theorem rta_sound {C : ℕ} {hp : List Task} {D R : ℕ} (h : rta C hp D = some R) :
    rtaStep C hp R = R ∧ C ≤ R ∧ R ≤ D ∧ ∀ P, rtaStep C hp P ≤ P → R ≤ P := by
  obtain ⟨h1, h2, h3⟩ := fixLoop_sound (rtaStep_monotone C hp) D (D + 1) C R
    (fun _ hP => C_le_of_prefix hP) h
  exact ⟨h1, C_le_of_prefix h1.le, h2, h3⟩

/-- Completeness of `rta`: `none` means no (pre-)fixed point is `≤ D`. -/
theorem rta_none {C : ℕ} {hp : List Task} {D : ℕ} (h : rta C hp D = none) :
    ∀ P, rtaStep C hp P ≤ P → D < P :=
  fixLoop_complete (rtaStep_monotone C hp) D (D + 1) C (le_rtaStep C hp C)
    (fun _ hP => C_le_of_prefix hP) (by omega) h

/-- Exact characterisation: `rta` succeeds iff some `R ≤ D` satisfies `C + ∑ ⌈R/Tⱼ⌉Cⱼ ≤ R`. -/
theorem rta_isSome_iff (C : ℕ) (hp : List Task) (D : ℕ) :
    (rta C hp D).isSome ↔ ∃ R ≤ D, rtaStep C hp R ≤ R := by
  constructor
  · intro h
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨h1, -, h3, -⟩ := rta_sound hR
    exact ⟨R, h3, h1.le⟩
  · rintro ⟨R, hRD, hR⟩
    cases h : rta C hp D with
    | none => exact absurd (rta_none h R hR) (by omega)
    | some _ => rfl

/-- Example: higher-priority tasks `(1,4)` and `(2,6)`, task under analysis with `C = 3`,
`D = 12`: worst-case response time `10`. -/
example : rta 3 [⟨1, 4⟩, ⟨2, 6⟩] 12 = some 10 := by decide

/-- Example: with `C = 6` the iteration `6, 9, 13` exceeds `D = 12`. -/
example : rta 6 [⟨1, 4⟩, ⟨2, 6⟩] 12 = none := by decide

/-! ## Schedules and the utilization necessity condition -/

/-- A uniprocessor schedule for `n` tasks: in each unit slot `t` the processor runs at most one
task (`none` = idle). -/
abbrev Schedule (n : ℕ) := ℕ → Option (Fin n)

/-- Number of slots in `[a, b)` that the schedule `s` gives to `i` (a task, or a job — the
definition works for schedules over any type of executable entities). -/
def served {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) (a b : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico a b, if s t = some i then 1 else 0

/-- Service is additive over adjacent windows. -/
theorem served_add {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    served s i a b + served s i b c = served s i a c :=
  Finset.sum_Ico_consecutive _ hab hbc

theorem served_mono_right {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) (a : ℕ) {b c : ℕ} (hbc : b ≤ c) :
    served s i a b ≤ served s i a c := by
  unfold served
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hbc)

/-- In one slot the processor serves at most one task. -/
theorem sum_slot_le_one {n : ℕ} (s : Schedule n) (t : ℕ) :
    (∑ i : Fin n, if s t = some i then 1 else 0) ≤ 1 := by
  cases h : s t with
  | none => simp
  | some j => simp [Finset.sum_ite_eq]

/-- Total service in `[a, b)` over all tasks is at most the window length `b - a`. -/
theorem sum_served_le {n : ℕ} (s : Schedule n) (a b : ℕ) :
    ∑ i : Fin n, served s i a b ≤ b - a := by
  unfold served
  rw [Finset.sum_comm]
  calc ∑ t ∈ Finset.Ico a b, ∑ i : Fin n, (if s t = some i then 1 else 0)
      ≤ ∑ _t ∈ Finset.Ico a b, 1 := Finset.sum_le_sum fun t _ => sum_slot_le_one s t
    _ = b - a := by simp

/-- Any single entity gets at most `b - a` slots in `[a, b)`. -/
theorem served_le {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) (a b : ℕ) : served s i a b ≤ b - a := by
  unfold served
  calc ∑ t ∈ Finset.Ico a b, (if s t = some i then 1 else 0) ≤ ∑ _t ∈ Finset.Ico a b, 1 :=
        Finset.sum_le_sum fun t _ => by split_ifs <;> simp
    _ = b - a := by simp

/-- Service over `[0, mT)` splits into the `m` period windows `[kT, (k+1)T)`. -/
theorem served_windows {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) (T m : ℕ) :
    ∑ k ∈ Finset.range m, served s i (k * T) ((k + 1) * T) = served s i 0 (m * T) := by
  induction m with
  | zero => simp [served]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, served_add s i (Nat.zero_le _) (by nlinarith)]

/-- Job `k` of task `i` is released at `k Tᵢ` and has deadline `(k+1) Tᵢ`. The schedule `s` meets
all deadlines up to the horizon `H` if each such job with deadline `≤ H` receives `Cᵢ` slots in its
window. (Slots of task `i` are attributed to whichever job's window they fall in; with implicit
deadlines the windows of one task are disjoint.) -/
def MeetsDeadlinesUpTo {n : ℕ} (τ : Fin n → Task) (s : Schedule n) (H : ℕ) : Prop :=
  ∀ i k, (k + 1) * (τ i).T ≤ H → (τ i).C ≤ served s i (k * (τ i).T) ((k + 1) * (τ i).T)

/-- Demand over a common multiple `H` of all periods is at most `H` for any feasible schedule:
`∑ᵢ (H / Tᵢ) Cᵢ ≤ H`. -/
theorem demand_le_of_meets {n : ℕ} (τ : Fin n → Task) (s : Schedule n) (H : ℕ)
    (hdvd : ∀ i, (τ i).T ∣ H) (hs : MeetsDeadlinesUpTo τ s H) :
    ∑ i, H / (τ i).T * (τ i).C ≤ H := by
  calc ∑ i, H / (τ i).T * (τ i).C ≤ ∑ i, served s i 0 H := by
        refine Finset.sum_le_sum fun i _ => ?_
        obtain ⟨m, hm⟩ := hdvd i
        rcases Nat.eq_zero_or_pos (τ i).T with h0 | hpos
        · simp [h0]
        have hH : H / (τ i).T = m := by rw [hm]; exact Nat.mul_div_cancel_left m hpos
        rw [hH]
        have hH' : H = m * (τ i).T := by rw [hm, mul_comm]
        rw [hH', ← served_windows]
        calc m * (τ i).C = ∑ _k ∈ Finset.range m, (τ i).C := by simp
          _ ≤ _ := Finset.sum_le_sum fun k hk => hs i k (by
              rw [Finset.mem_range] at hk
              rw [hH']; exact Nat.mul_le_mul_right _ hk)
    _ ≤ H - 0 := sum_served_le s 0 H
    _ = H := Nat.sub_zero H

/-- Total utilization `U = ∑ Cᵢ / Tᵢ`. -/
noncomputable def utilization {n : ℕ} (τ : Fin n → Task) : ℝ := ∑ i, ((τ i).C : ℝ) / (τ i).T

/-- The hyperperiod `H = lcm Tᵢ`. -/
def hyperperiod {n : ℕ} (τ : Fin n → Task) : ℕ := Finset.univ.lcm fun i => (τ i).T

theorem dvd_hyperperiod {n : ℕ} (τ : Fin n → Task) (i : Fin n) : (τ i).T ∣ hyperperiod τ :=
  Finset.dvd_lcm (Finset.mem_univ i)

theorem hyperperiod_pos {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T) :
    0 < hyperperiod τ := by
  unfold hyperperiod
  rw [Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, not_exists]
  exact fun i => (hT i).ne'

/-- The demand over a common multiple `H` of the periods equals `H · U`. -/
theorem demand_eq_mul_utilization {n : ℕ} (τ : Fin n → Task) (H : ℕ) (hT : ∀ i, 0 < (τ i).T)
    (hdvd : ∀ i, (τ i).T ∣ H) :
    ((∑ i, H / (τ i).T * (τ i).C : ℕ) : ℝ) = H * utilization τ := by
  rw [utilization, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_div (hdvd i) (by exact_mod_cast (hT i).ne')]
  have : ((τ i).T : ℝ) ≠ 0 := by exact_mod_cast (hT i).ne'
  field_simp

/-- **Utilization necessity.** If `U > 1`, no uniprocessor schedule whatsoever (EDF or otherwise)
meets all deadlines over the hyperperiod: the demand `H · U` exceeds the `H` available slots. -/
theorem not_meets_of_utilization_gt_one {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hU : 1 < utilization τ) (s : Schedule n) : ¬ MeetsDeadlinesUpTo τ s (hyperperiod τ) := by
  intro hs
  have h1 := demand_le_of_meets τ s _ (dvd_hyperperiod τ) hs
  have h2 := demand_eq_mul_utilization τ _ hT (dvd_hyperperiod τ)
  have hH : (0 : ℝ) < hyperperiod τ := by exact_mod_cast hyperperiod_pos τ hT
  have h3 : ((∑ i, hyperperiod τ / (τ i).T * (τ i).C : ℕ) : ℝ) ≤ hyperperiod τ := by
    exact_mod_cast h1
  rw [h2] at h3
  nlinarith

/-- Equivalently: feasibility over the hyperperiod forces `U ≤ 1`. -/
theorem utilization_le_one_of_meets {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (s : Schedule n) (hs : MeetsDeadlinesUpTo τ s (hyperperiod τ)) : utilization τ ≤ 1 :=
  not_lt.mp fun hU => not_meets_of_utilization_gt_one τ hT hU s hs

/-! ## Processor-demand criterion -/

/-- Demand bound function of synchronous periodic implicit-deadline tasks:
`dbf(t) = ∑ᵢ ⌊t / Tᵢ⌋ Cᵢ`, the total work of jobs released and due within `[0, t]`. -/
def dbf {n : ℕ} (τ : Fin n → Task) (t : ℕ) : ℕ := ∑ i, t / (τ i).T * (τ i).C

/-- `dbf(t) ≤ U · t` (for positive periods). -/
theorem dbf_le_utilization_mul {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T) (t : ℕ) :
    (dbf τ t : ℝ) ≤ utilization τ * t := by
  rw [dbf, utilization, Finset.sum_mul]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have hTi : (0 : ℝ) < (τ i).T := by exact_mod_cast hT i
  have hfl : ((t / (τ i).T : ℕ) : ℝ) * (τ i).T ≤ t := by
    exact_mod_cast Nat.div_mul_le_self t (τ i).T
  have hfl' : ((t / (τ i).T : ℕ) : ℝ) ≤ t / (τ i).T := by rw [le_div_iff₀ hTi]; exact hfl
  calc ((t / (τ i).T : ℕ) : ℝ) * (τ i).C ≤ t / (τ i).T * (τ i).C :=
        mul_le_mul_of_nonneg_right hfl' (Nat.cast_nonneg _)
    _ = (τ i).C / (τ i).T * t := by ring

/-- **Processor-demand criterion holds when `U ≤ 1`:** `dbf(t) ≤ t` for every `t`. -/
theorem dbf_le_self {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hU : utilization τ ≤ 1) (t : ℕ) : dbf τ t ≤ t := by
  have h := dbf_le_utilization_mul τ hT t
  have : utilization τ * t ≤ t := by
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  exact_mod_cast h.trans this

/-- Conversely the criterion at `t = H` (hyperperiod) is exactly `U ≤ 1`. -/
theorem dbf_hyperperiod_le_iff {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T) :
    dbf τ (hyperperiod τ) ≤ hyperperiod τ ↔ utilization τ ≤ 1 := by
  have h2 := demand_eq_mul_utilization τ _ hT (dvd_hyperperiod τ)
  have hH : (0 : ℝ) < hyperperiod τ := by exact_mod_cast hyperperiod_pos τ hT
  rw [← dbf] at h2
  constructor
  · intro h
    have h3 : (dbf τ (hyperperiod τ) : ℝ) ≤ hyperperiod τ := by exact_mod_cast h
    rw [h2] at h3
    nlinarith
  · intro h
    exact dbf_le_self τ hT h _

/-! ## Liu–Layland bound for two tasks under rate-monotonic priorities -/

/-- The real-arithmetic core of the two-task Liu–Layland bound. Write `T₂ = k T₁ + r` with
`0 < r < T₁`. If the RTA test fails both at `R = k T₁` (inequality `hA`) and at `R = T₂`
(inequality `hB`), then the utilization exceeds `2(√2 - 1)`. (Here `x = C₁`, `y = C₂`, `a = T₁`.)
The proof reduces to `U·T₁T₂ > r² + kT₁² ≥ 2(√2-1)·T₁T₂`, the last step being the perfect square
`(r - (√2-1)T₁)² ≥ 0`. -/
theorem ll2_real {x y a r k : ℝ} (ha : 0 < a) (hr : 0 < r) (hra : r < a) (hk : 1 ≤ k)
    (hA : k * a < y + k * x) (hB : k * a + r < y + (k + 1) * x) :
    2 * (Real.sqrt 2 - 1) < x / a + y / (k * a + r) := by
  set s := Real.sqrt 2 with hs
  have hs2 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs15 : s < 3 / 2 := by nlinarith
  have hb : 0 < k * a + r := by nlinarith
  have key : r ^ 2 + k * a ^ 2 < x * (k * a + r) + y * a := by
    rcases le_total x r with hxr | hxr
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxr) (sub_nonneg.mpr hra.le), mul_lt_mul_of_pos_right hB ha]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxr) hr.le, mul_lt_mul_of_pos_right hA ha]
  have key2 : 2 * (s - 1) * (a * (k * a + r)) ≤ r ^ 2 + k * a ^ 2 := by
    nlinarith [sq_nonneg (r - (s - 1) * a), mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg (sq_nonneg a) (by linarith : (0:ℝ) ≤ 3 - 2 * s))]
  have : x / a + y / (k * a + r) = (x * (k * a + r) + y * a) / (a * (k * a + r)) := by
    field_simp
  rw [this, lt_div_iff₀ (by positivity)]
  linarith

theorem two_mul_sqrt_two_sub_one_lt_one : 2 * (Real.sqrt 2 - 1) < 1 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- **Liu–Layland bound, `n = 2`.** Two periodic tasks with `0 < T₁ ≤ T₂` under rate-monotonic
(fixed) priorities, task 1 having higher priority. If `C₁/T₁ + C₂/T₂ ≤ 2(√2 - 1) ≈ 0.828`, then
task 1 meets its deadline (`C₁ ≤ T₁`) and the response-time analysis of task 2 succeeds with
deadline `T₂` (so by `rta_sound` its worst-case response time is `≤ T₂`). -/
theorem rm_two_tasks_schedulable (C₁ T₁ C₂ T₂ : ℕ) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hU : (C₁ : ℝ) / T₁ + C₂ / T₂ ≤ 2 * (Real.sqrt 2 - 1)) :
    C₁ ≤ T₁ ∧ (rta C₂ [⟨C₁, T₁⟩] T₂).isSome := by
  have hβ := two_mul_sqrt_two_sub_one_lt_one
  have hT₁r : (0 : ℝ) < T₁ := by exact_mod_cast hT₁
  have hT₂r : (0 : ℝ) < T₂ := by exact_mod_cast lt_of_lt_of_le hT₁ hT
  have hU1 : (C₁ : ℝ) / T₁ + C₂ / T₂ < 1 := lt_of_le_of_lt hU hβ
  have hc2 : (0 : ℝ) ≤ C₂ / T₂ := by positivity
  refine ⟨?_, ?_⟩
  · have : (C₁ : ℝ) / T₁ < 1 := by linarith
    rw [div_lt_one hT₁r] at this
    exact_mod_cast this.le
  rw [rta_isSome_iff]
  have hstep : ∀ R, rtaStep C₂ [⟨C₁, T₁⟩] R = C₂ + cdiv R T₁ * C₁ := by
    intro R; simp [rtaStep, interference]
  set k := T₂ / T₁ with hk
  set r := T₂ % T₁ with hr
  have hdecomp : T₂ = k * T₁ + r := by rw [hk, hr, mul_comm]; exact (Nat.div_add_mod T₂ T₁).symm
  have hk1 : 1 ≤ k := Nat.div_pos hT hT₁
  have hrlt : r < T₁ := Nat.mod_lt _ hT₁
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · refine ⟨T₂, le_rfl, ?_⟩
    rw [hstep]
    have hT₂ : T₂ = k * T₁ := by omega
    rw [hT₂, cdiv_mul_self k T₁ hT₁]
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hT₂' : (T₂ : ℝ) = k * T₁ := by exact_mod_cast hT₂
    rw [hT₂'] at hU1
    have h' : (C₂ : ℝ) + k * C₁ < k * T₁ := by
      have e : (C₁ : ℝ) / T₁ + C₂ / (k * T₁) = (C₂ + k * C₁) / (k * T₁) := by field_simp; ring
      rw [e, div_lt_one (by positivity)] at hU1
      exact hU1
    exact_mod_cast h'.le
  · by_contra hno
    simp only [not_exists, not_and, not_le] at hno
    have hA := hno (k * T₁) (by omega)
    have hB := hno T₂ le_rfl
    rw [hstep, cdiv_mul_self k T₁ hT₁] at hA
    rw [hstep, hdecomp, cdiv_mul_add k T₁ r hrpos hrlt.le] at hB
    have hA' : (k : ℝ) * T₁ < C₂ + k * C₁ := by exact_mod_cast hA
    have hB' : (k : ℝ) * T₁ + r < C₂ + (k + 1) * C₁ := by exact_mod_cast hB
    have hT₂' : (T₂ : ℝ) = k * T₁ + r := by exact_mod_cast hdecomp
    have := ll2_real (x := (C₁ : ℝ)) (y := C₂) (r := (r : ℝ)) (k := (k : ℝ)) hT₁r (by exact_mod_cast hrpos)
      (by exact_mod_cast hrlt) (by exact_mod_cast hk1) (by linarith) (by linarith)
    rw [← hT₂'] at this
    linarith

/-! ## EDF optimality via the processor-demand criterion (job level) -/

/-- A finite set of jobs indexed by `J`: release time `r`, absolute deadline `d`, cost `c`. A job
must receive `c j` slots in `[r j, d j)`. -/
structure JobSet (J : Type*) where
  /-- release time -/
  r : J → ℕ
  /-- absolute deadline -/
  d : J → ℕ
  /-- execution cost -/
  c : J → ℕ

section EDF

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A schedule `s : ℕ → Option J` is an EDF schedule for `js` if
* it only runs pending jobs (released and not yet complete), and
* whenever a job `j` is pending, the job that runs has a deadline `≤ d j`
  (in particular the processor is not idle). -/
structure IsEDF (js : JobSet J) (s : ℕ → Option J) : Prop where
  runs_pending : ∀ t j, s t = some j → js.r j ≤ t ∧ served s j 0 t < js.c j
  edf_choice : ∀ t j, js.r j ≤ t → served s j 0 t < js.c j → ∃ j', s t = some j' ∧ js.d j' ≤ js.d j

theorem served_succ {α : Type*} [DecidableEq α] (s : ℕ → Option α) (i : α) (t : ℕ) :
    served s i 0 (t + 1) = served s i 0 t + if s t = some i then 1 else 0 := by
  unfold served
  rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]

omit [Fintype J] in
/-- In an EDF schedule (indeed any schedule running only pending jobs) no job receives more than
its cost. -/
theorem IsEDF.served_le_cost {js : JobSet J} {s : ℕ → Option J} (hs : IsEDF js s) (j : J) :
    ∀ t, served s j 0 t ≤ js.c j := by
  intro t
  induction t with
  | zero => simp [served]
  | succ t ih =>
    rw [served_succ]
    split_ifs with h
    · have := (hs.runs_pending t j h).2; omega
    · omega

/-- The processor-demand condition: for every interval `[t₁, t₂)`, the total cost of the jobs
released at or after `t₁` and due by `t₂` is at most `t₂ - t₁`. -/
def DemandOK (js : JobSet J) : Prop :=
  ∀ t₁ t₂, ∑ j ∈ Finset.univ.filter (fun j => t₁ ≤ js.r j ∧ js.d j ≤ t₂), js.c j ≤ t₂ - t₁

/-- **EDF meets every deadline under the processor-demand condition.** Classical busy-interval
argument: if job `j₀` missed its deadline `D`, let `t₀` be the start of the maximal interval
before `D` in which only jobs with deadline `≤ D` run. Jobs with deadline `≤ D` released before
`t₀` are complete by `t₀`, so `[t₀, D)` is entirely spent on jobs released in `[t₀, D)` with
deadline `≤ D`, and the unfinished `j₀` makes their demand exceed `D - t₀`. -/
theorem IsEDF.meets_deadlines {js : JobSet J} {s : ℕ → Option J} (hs : IsEDF js s)
    (hdem : DemandOK js) (j₀ : J) : js.c j₀ ≤ served s j₀ 0 (js.d j₀) := by
  classical
  by_contra hmiss
  push Not at hmiss
  set D := js.d j₀ with hD
  let P : ℕ → Prop := fun t => ∀ t', t ≤ t' → t' < D → ∃ j', s t' = some j' ∧ js.d j' ≤ D
  have hP : P (js.r j₀) := fun t' h1 h2 =>
    hs.edf_choice t' j₀ h1 (lt_of_le_of_lt (served_mono_right s j₀ 0 h2.le) hmiss)
  have hex : ∃ t, P t := ⟨_, hP⟩
  set t₀ := Nat.find hex with ht₀
  have hP0 : P t₀ := Nat.find_spec hex
  have ht0r : t₀ ≤ js.r j₀ := Nat.find_min' hex hP
  -- jobs with deadline `≤ D` released before `t₀` are complete by `t₀`
  have hdone : ∀ j, js.r j < t₀ → js.d j ≤ D → js.c j ≤ served s j 0 t₀ := by
    intro j hj hjd
    have hnot : ¬ P (t₀ - 1) := Nat.find_min hex (by omega)
    by_contra hlt
    push Not at hlt
    have hlt' : served s j 0 (t₀ - 1) < js.c j :=
      lt_of_le_of_lt (served_mono_right s j 0 (Nat.sub_le t₀ 1)) hlt
    obtain ⟨j', h1, h2⟩ := hs.edf_choice (t₀ - 1) j (by omega) hlt'
    apply hnot
    intro t' h1' h2'
    by_cases heq : t' = t₀ - 1
    · subst heq; exact ⟨j', h1, h2.trans hjd⟩
    · exact hP0 t' (by omega) h2'
  set S := Finset.univ.filter (fun j => t₀ ≤ js.r j ∧ js.d j ≤ D) with hS
  have hslot : ∀ t ∈ Finset.Ico t₀ D, 1 ≤ ∑ j ∈ S, (if s t = some j then 1 else 0) := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    obtain ⟨j', h1, h2⟩ := hP0 t ht.1 ht.2
    have hr : t₀ ≤ js.r j' := by
      by_contra h
      push Not at h
      have e1 := hdone j' h h2
      have e2 := (hs.runs_pending t j' h1).2
      have e3 := served_mono_right s j' 0 ht.1
      omega
    have hmem : j' ∈ S := by simp [hS, hr, h2]
    calc 1 = (if s t = some j' then 1 else 0) := by simp [h1]
      _ ≤ _ := Finset.single_le_sum (f := fun j => if s t = some j then 1 else 0)
          (fun _ _ => Nat.zero_le _) hmem
  have hcount : D - t₀ ≤ ∑ j ∈ S, served s j t₀ D := by
    calc D - t₀ = ∑ _t ∈ Finset.Ico t₀ D, 1 := by simp
      _ ≤ ∑ t ∈ Finset.Ico t₀ D, ∑ j ∈ S, (if s t = some j then 1 else 0) :=
          Finset.sum_le_sum hslot
      _ = ∑ j ∈ S, served s j t₀ D := by rw [Finset.sum_comm]; rfl
  have hwin : ∀ j, served s j t₀ D ≤ served s j 0 D := by
    intro j
    rcases le_total t₀ D with h | h
    · rw [← served_add s j (Nat.zero_le t₀) h]; omega
    · simp [served, Finset.Ico_eq_empty_of_le h]
  have hle : ∀ j ∈ S, served s j t₀ D ≤ js.c j := fun j _ =>
    (hwin j).trans (hs.served_le_cost j D)
  have hj0S : j₀ ∈ S := by simp [hS, ht0r, hD]
  have hlt : ∑ j ∈ S, served s j t₀ D < ∑ j ∈ S, js.c j :=
    Finset.sum_lt_sum hle ⟨j₀, hj0S, lt_of_le_of_lt (hwin j₀) hmiss⟩
  have h2 : ∑ j ∈ S, js.c j ≤ D - t₀ := by convert hdem t₀ D
  omega

/-! ### Construction of an EDF schedule -/

/-- EDF choice given remaining work `rem` at time `t`: a pending job (released, `rem > 0`) of
minimal deadline, or `none` if no job is pending. -/
noncomputable def edfPick (js : JobSet J) (rem : J → ℕ) (t : ℕ) : Option J :=
  if h : (Finset.univ.filter fun j => js.r j ≤ t ∧ 0 < rem j).Nonempty then
    some (Classical.choose (Finset.exists_min_image _ js.d h)) else none

omit [DecidableEq J] in
theorem edfPick_some {js : JobSet J} {rem : J → ℕ} {t : ℕ} {j : J} (h : edfPick js rem t = some j) :
    js.r j ≤ t ∧ 0 < rem j ∧ ∀ j', js.r j' ≤ t → 0 < rem j' → js.d j ≤ js.d j' := by
  unfold edfPick at h
  split_ifs at h with hne
  cases h
  obtain ⟨hmem, hmin⟩ := Classical.choose_spec (Finset.exists_min_image _ js.d hne)
  have hmem' := (Finset.mem_filter.mp hmem).2
  exact ⟨hmem'.1, hmem'.2, fun j' h1 h2 => hmin j' (by simp [h1, h2])⟩

omit [DecidableEq J] in
theorem edfPick_none {js : JobSet J} {rem : J → ℕ} {t : ℕ} (h : edfPick js rem t = none) :
    ∀ j, js.r j ≤ t → rem j = 0 := by
  unfold edfPick at h
  split_ifs at h with hne
  intro j hj
  by_contra h0
  exact hne ⟨j, by simp [hj, Nat.pos_of_ne_zero h0]⟩

/-- Remaining work of each job under the EDF simulation. -/
noncomputable def edfRem (js : JobSet J) : ℕ → J → ℕ
  | 0 => js.c
  | t + 1 => fun j => edfRem js t j - if edfPick js (edfRem js t) t = some j then 1 else 0

/-- The (preemptive, uniprocessor) EDF schedule of the job set `js`. -/
noncomputable def edf (js : JobSet J) (t : ℕ) : Option J := edfPick js (edfRem js t) t

theorem edfRem_add_served (js : JobSet J) (j : J) :
    ∀ t, edfRem js t j + served (edf js) j 0 t = js.c j := by
  intro t
  induction t with
  | zero => simp [edfRem, served]
  | succ t ih =>
    rw [served_succ]
    simp only [edfRem]
    change edfRem js t j - (if edf js t = some j then 1 else 0) + _ = _
    split_ifs with h
    · have := (edfPick_some h).2.1; omega
    · omega

/-- The EDF simulation is indeed an EDF schedule. -/
theorem edf_isEDF (js : JobSet J) : IsEDF js (edf js) where
  runs_pending t j h := by
    obtain ⟨h1, h2, -⟩ := edfPick_some h
    have := edfRem_add_served js j t
    exact ⟨h1, by omega⟩
  edf_choice t j hr hlt := by
    have hrem : 0 < edfRem js t j := by have := edfRem_add_served js j t; omega
    cases h : edf js t with
    | none => exact absurd (edfPick_none h j hr) hrem.ne'
    | some j' => exact ⟨j', rfl, (edfPick_some h).2.2 j hr hrem⟩

/-- **EDF is optimal for the processor-demand condition:** the EDF schedule meets every deadline
of any finite job set satisfying `DemandOK`. -/
theorem edf_meets_deadlines (js : JobSet J) (hdem : DemandOK js) (j : J) :
    js.c j ≤ served (edf js) j 0 (js.d j) :=
  (edf_isEDF js).meets_deadlines hdem j

end EDF

/-! ## EDF sufficiency for periodic tasks: `U ≤ 1` ⇒ schedulable -/

/-- `t ≤ ⌈t / T⌉ · T`. -/
theorem le_cdiv_mul (t T : ℕ) (hT : 0 < T) : t ≤ cdiv t T * T := by
  have := Nat.lt_div_mul_add (a := t + T - 1) hT
  unfold cdiv; omega

/-- At most `⌊(t₂ - t₁) / T⌋` period windows `[kT, (k+1)T)` fit inside `[t₁, t₂)`. -/
theorem card_windows_le (T m t₁ t₂ : ℕ) (hT : 0 < T) :
    (Finset.univ.filter fun k : Fin m => t₁ ≤ k * T ∧ (k + 1) * T ≤ t₂).card ≤ (t₂ - t₁) / T := by
  have hsub : (Finset.univ.filter fun k : Fin m => t₁ ≤ k * T ∧ (k + 1) * T ≤ t₂).map
      Fin.valEmbedding ⊆ Finset.Ico (cdiv t₁ T) (t₂ / T) := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨k, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_Ico]
    constructor
    · show (t₁ + T - 1) / T ≤ k
      rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hT, Nat.succ_eq_add_one, add_mul, one_mul]
      omega
    · show (k : ℕ) < t₂ / T
      rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hT]; exact h2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Nat.card_Ico] at hcard
  refine hcard.trans ?_
  rw [Nat.le_div_iff_mul_le hT, Nat.sub_mul]
  have h1 := le_cdiv_mul t₁ T hT
  have h2 := Nat.div_mul_le_self t₂ T
  omega

/-- The jobs of the periodic task set `τ` released in `[0, H)`: job `⟨i, k⟩` is the `k`-th job
of task `i`. -/
abbrev PJob {n : ℕ} (τ : Fin n → Task) (H : ℕ) := Σ i : Fin n, Fin (H / (τ i).T)

/-- Job parameters: release `k Tᵢ`, deadline `(k+1) Tᵢ`, cost `Cᵢ`. -/
def periodicJobs {n : ℕ} (τ : Fin n → Task) (H : ℕ) : JobSet (PJob τ H) where
  r j := j.2 * (τ j.1).T
  d j := (j.2 + 1) * (τ j.1).T
  c j := (τ j.1).C

/-- The job-level demand in any interval of length `L` is at most `dbf(L)`, hence the
processor-demand condition holds when `U ≤ 1`. -/
theorem periodicJobs_demandOK {n : ℕ} (τ : Fin n → Task) (H : ℕ) (hT : ∀ i, 0 < (τ i).T)
    (hU : utilization τ ≤ 1) : DemandOK (periodicJobs τ H) := by
  intro t₁ t₂
  refine le_trans ?_ (dbf_le_self τ hT hU (t₂ - t₁))
  rw [Finset.sum_filter, Fintype.sum_sigma, dbf]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine (Finset.sum_le_card_nsmul _ _ (τ i).C (fun _ _ => le_rfl)).trans ?_
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_right _ (by convert card_windows_le (τ i).T (H / (τ i).T) t₁ t₂ (hT i) <;> rfl)

/-- **EDF sufficiency.** If `U ≤ 1` (and all periods are positive) then the EDF schedule meets
every deadline in the hyperperiod. Together with `utilization_le_one_of_meets` this gives the
exact characterisation `edf_schedulable_iff`. -/
theorem exists_meets_of_utilization_le_one {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hU : utilization τ ≤ 1) : ∃ s : Schedule n, MeetsDeadlinesUpTo τ s (hyperperiod τ) := by
  set H := hyperperiod τ
  set js := periodicJobs τ H
  have hdem := periodicJobs_demandOK τ H hT hU
  let sj := edf js
  refine ⟨fun t => (sj t).map Sigma.fst, ?_⟩
  intro i k hk
  have hkm : k < H / (τ i).T := by rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (hT i)]; exact hk
  let j : PJob τ H := ⟨i, ⟨k, hkm⟩⟩
  have hmeet : (τ i).C ≤ served sj j 0 ((k + 1) * (τ i).T) := edf_meets_deadlines js hdem j
  have hzero : served sj j 0 (k * (τ i).T) = 0 := by
    unfold served
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    rw [if_neg]
    intro h
    have := ((edf_isEDF js).runs_pending t j h).1
    simp only [js, periodicJobs, j] at this
    omega
  have hsplit := served_add sj j (Nat.zero_le (k * (τ i).T))
    (Nat.mul_le_mul_right _ (Nat.le_add_right k 1))
  have hproj : served sj j (k * (τ i).T) ((k + 1) * (τ i).T) ≤
      served (fun t => (sj t).map Sigma.fst) i (k * (τ i).T) ((k + 1) * (τ i).T) := by
    unfold served
    refine Finset.sum_le_sum fun t _ => ?_
    split_ifs with h1 h2 <;> simp_all [j]
  omega

/-- **Exact schedulability test for implicit-deadline periodic tasks on a uniprocessor**
(Liu–Layland 1973): a schedule meeting all deadlines over the hyperperiod exists iff `U ≤ 1`,
and when it exists, EDF is such a schedule. -/
theorem edf_schedulable_iff {n : ℕ} (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T) :
    (∃ s : Schedule n, MeetsDeadlinesUpTo τ s (hyperperiod τ)) ↔ utilization τ ≤ 1 :=
  ⟨fun ⟨s, hs⟩ => utilization_le_one_of_meets τ hT s hs,
    exists_meets_of_utilization_le_one τ hT⟩

/-! ## Connecting the RTA fixed point to fixed-priority schedules -/

/-- Abstract properties of a fixed-priority preemptive schedule `s` of a synchronous periodic task
set `τ` (all tasks release their first job at time `0`, the *critical instant*), as seen from task
`i` whose higher-priority tasks are listed in `hp`:

* `work_bound`: a task never executes more than its released work, i.e. in `[0, t)` task `j`
  executes at most `⌈t / Tⱼ⌉ Cⱼ` slots (jobs released at `0, Tⱼ, 2Tⱼ, …`, each of size `Cⱼ`);
* `busy`: while the first job of task `i` is unfinished, the processor is neither idle nor running
  a lower-priority task (work-conserving + priority-driven). -/
structure FPCriticalInstant {n : ℕ} (τ : Fin n → Task) (s : Schedule n) (i : Fin n)
    (hp : List (Fin n)) : Prop where
  work_bound : ∀ j t, served s j 0 t ≤ cdiv t (τ j).T * (τ j).C
  busy : ∀ t, served s i 0 t < (τ i).C → ∃ j, s t = some j ∧ (j = i ∨ j ∈ hp)

/-- **RTA is sound for the critical-instant job.** In any fixed-priority schedule satisfying
`FPCriticalInstant`, if `R` is a pre-fixed point of the RTA recurrence of task `i`
(`Cᵢ + ∑_{j ∈ hp} ⌈R/Tⱼ⌉ Cⱼ ≤ R`; e.g. the value returned by `rta`), then the first job of task `i`
has received its full `Cᵢ` units of service by time `R`, i.e. its response time is `≤ R`. -/
theorem fp_response_le_of_rta {n : ℕ} (τ : Fin n → Task) (s : Schedule n) (i : Fin n)
    (hp : List (Fin n)) (hnd : hp.Nodup) (hi : i ∉ hp) (hs : FPCriticalInstant τ s i hp)
    {R : ℕ} (hR : rtaStep (τ i).C (hp.map τ) R ≤ R) : (τ i).C ≤ served s i 0 R := by
  classical
  by_contra hlt
  push Not at hlt
  have hiS : i ∉ hp.toFinset := by simpa using hi
  -- every slot in `[0, R)` is busy with task `i` or a higher-priority task
  have hslot : ∀ t ∈ Finset.Ico 0 R,
      1 ≤ ∑ j ∈ insert i hp.toFinset, (if s t = some j then 1 else 0) := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    obtain ⟨j, hj, hj'⟩ := hs.busy t (lt_of_le_of_lt (served_mono_right s i 0 ht.2.le) hlt)
    have hjmem : j ∈ insert i hp.toFinset := by
      rcases hj' with rfl | h
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
    calc 1 = (if s t = some j then 1 else 0) := by simp [hj]
      _ ≤ _ := Finset.single_le_sum (f := fun j => if s t = some j then 1 else 0)
          (fun _ _ => Nat.zero_le _) hjmem
  have hcount : R ≤ ∑ j ∈ insert i hp.toFinset, served s j 0 R := by
    calc R = ∑ _t ∈ Finset.Ico 0 R, 1 := by simp
      _ ≤ ∑ t ∈ Finset.Ico 0 R, ∑ j ∈ insert i hp.toFinset, (if s t = some j then 1 else 0) :=
          Finset.sum_le_sum hslot
      _ = ∑ j ∈ insert i hp.toFinset, served s j 0 R := by rw [Finset.sum_comm]; rfl
  rw [Finset.sum_insert hiS] at hcount
  have hhp : ∑ j ∈ hp.toFinset, served s j 0 R ≤ interference (hp.map τ) R := by
    calc ∑ j ∈ hp.toFinset, served s j 0 R
        ≤ ∑ j ∈ hp.toFinset, cdiv R (τ j).T * (τ j).C :=
          Finset.sum_le_sum fun j _ => hs.work_bound j R
      _ = interference (hp.map τ) R := by
          rw [List.sum_toFinset _ hnd, interference, List.map_map]; rfl
  unfold rtaStep at hR
  omega

/-- Combining with `rta`: if the response-time analysis of task `i` returns `some R`, the
critical-instant job of task `i` completes within `R ≤ D`. -/
theorem fp_response_le_of_rta_eq_some {n : ℕ} (τ : Fin n → Task) (s : Schedule n) (i : Fin n)
    (hp : List (Fin n)) (hnd : hp.Nodup) (hi : i ∉ hp) (hs : FPCriticalInstant τ s i hp)
    {D R : ℕ} (h : rta (τ i).C (hp.map τ) D = some R) :
    R ≤ D ∧ (τ i).C ≤ served s i 0 R :=
  ⟨(rta_sound h).2.2.1, fp_response_le_of_rta τ s i hp hnd hi hs (rta_sound h).1.le⟩

/-! ### A concrete fixed-priority scheduler satisfying `FPCriticalInstant`

Fixed-priority preemptive scheduling is the job-level "earliest key first" scheduler `edf` with
the key `d` replaced by the task's priority. Tasks are indexed in priority order (index `0` is the
highest priority; e.g. sort by period for rate-monotonic). We simulate `M` jobs per task. -/

/-- Job set for fixed-priority scheduling: job `(i, k)` released at `k Tᵢ`, cost `Cᵢ`, and
"deadline" field used as the priority key `i`. -/
def fpJobs {n : ℕ} (τ : Fin n → Task) (M : ℕ) : JobSet (Fin n × Fin M) where
  r j := j.2 * (τ j.1).T
  d j := j.1
  c j := (τ j.1).C

/-- The fixed-priority preemptive schedule (task level) of `M` jobs per task. -/
noncomputable def fpSched {n : ℕ} (τ : Fin n → Task) (M : ℕ) : Schedule n :=
  fun t => (edf (fpJobs τ M) t).map Prod.fst

/-- The higher-priority tasks of task `i` (smaller index). -/
def higherPrio {n : ℕ} (i : Fin n) : List (Fin n) := (List.finRange n).filter (· < i)

theorem higherPrio_nodup {n : ℕ} (i : Fin n) : (higherPrio i).Nodup :=
  (List.nodup_finRange n).filter _

theorem not_mem_higherPrio {n : ℕ} (i : Fin n) : i ∉ higherPrio i := by simp [higherPrio]

theorem mem_higherPrio {n : ℕ} {i j : Fin n} : j ∈ higherPrio i ↔ j < i := by
  simp [higherPrio, List.mem_finRange]

/-- Task-level service is the sum of the job-level services of its jobs. -/
theorem served_fpSched {n : ℕ} (τ : Fin n → Task) (M : ℕ) (i : Fin n) (a b : ℕ) :
    served (fpSched τ M) i a b = ∑ k : Fin M, served (edf (fpJobs τ M)) (i, k) a b := by
  unfold served
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold fpSched
  cases h : edf (fpJobs τ M) t with
  | none => simp
  | some j =>
    obtain ⟨j1, j2⟩ := j
    by_cases hj : j1 = i
    · subst hj; simp [Prod.ext_iff, Finset.sum_ite_eq]
    · simp [Prod.ext_iff, hj]

/-- At most `⌈t / T⌉` jobs of a period-`T` task are released before `t`. -/
theorem card_released_le (T M t : ℕ) (hT : 0 < T) :
    (Finset.univ.filter fun k : Fin M => k * T < t).card ≤ cdiv t T := by
  have hsub : (Finset.univ.filter fun k : Fin M => k * T < t).map Fin.valEmbedding ⊆
      Finset.range (cdiv t T) := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_range]
    exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hk (le_cdiv_mul t T hT))
  simpa using Finset.card_le_card hsub

/-- The concrete fixed-priority schedule satisfies the critical-instant hypotheses for every task
`i` (with `M ≥ 1` jobs per task and positive periods). -/
theorem fpSched_criticalInstant {n : ℕ} (τ : Fin n → Task) (M : ℕ) (hM : 0 < M)
    (hT : ∀ i, 0 < (τ i).T) (i : Fin n) : FPCriticalInstant τ (fpSched τ M) i (higherPrio i) where
  work_bound j t := by
    classical
    have hs := edf_isEDF (fpJobs τ M)
    rw [served_fpSched]
    calc ∑ k : Fin M, served (edf (fpJobs τ M)) (j, k) 0 t
        = ∑ k ∈ Finset.univ.filter (fun k : Fin M => k * (τ j).T < t),
            served (edf (fpJobs τ M)) (j, k) 0 t := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs with hk
          · rfl
          · unfold served
            refine Finset.sum_eq_zero fun t' ht' => ?_
            rw [Finset.mem_Ico] at ht'
            rw [if_neg]
            intro h
            have := (hs.runs_pending t' (j, k) h).1
            simp only [fpJobs] at this
            omega
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin M => k * (τ j).T < t), (τ j).C :=
          Finset.sum_le_sum fun k _ => hs.served_le_cost (j, k) t
      _ = (Finset.univ.filter (fun k : Fin M => k * (τ j).T < t)).card * (τ j).C := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ cdiv t (τ j).T * (τ j).C := Nat.mul_le_mul_right _ (card_released_le _ M t (hT j))
  busy t h := by
    have hs := edf_isEDF (fpJobs τ M)
    let j₀ : Fin n × Fin M := (i, ⟨0, hM⟩)
    have hle : served (edf (fpJobs τ M)) j₀ 0 t ≤ served (fpSched τ M) i 0 t := by
      rw [served_fpSched]
      exact Finset.single_le_sum (f := fun k => served (edf (fpJobs τ M)) (i, k) 0 t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    obtain ⟨j', h1, h2⟩ := hs.edf_choice t j₀ (by simp [fpJobs, j₀])
      (lt_of_le_of_lt hle (by simpa [fpJobs, j₀] using h))
    refine ⟨j'.1, by simp [fpSched, h1], ?_⟩
    simp only [fpJobs, j₀] at h2
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact Or.inr (mem_higherPrio.mpr (Fin.lt_def.mpr hlt))
    · exact Or.inl (Fin.ext heq)

/-- **RTA is sound for the simulated fixed-priority scheduler.** If the response-time analysis of
task `i` (interference from all higher-priority tasks) returns `some R`, then in the concrete
preemptive fixed-priority schedule the critical-instant job of task `i` completes by `R ≤ D`. -/
theorem fpSched_rta_sound {n : ℕ} (τ : Fin n → Task) (M : ℕ) (hM : 0 < M)
    (hT : ∀ i, 0 < (τ i).T) (i : Fin n) {D R : ℕ}
    (h : rta (τ i).C ((higherPrio i).map τ) D = some R) :
    R ≤ D ∧ (τ i).C ≤ served (fpSched τ M) i 0 R :=
  fp_response_le_of_rta_eq_some τ _ i _ (higherPrio_nodup i) (not_mem_higherPrio i)
    (fpSched_criticalInstant τ M hM hT i) h

/-! ## Control-loop timing: latency and jitter from the RTA bound -/

/-- Timing trace of a periodic control task `i` with period `T` in schedule `s`: job `k` is
released at `k T`, reads the sensor when it starts (`start k`) and writes the actuator when it
finishes (`finish k`); it needs `C` slots of service in `[kT, finish k)`; and its response time is
bounded by `R` (e.g. from response-time analysis). -/
structure ControlTrace {n : ℕ} (s : Schedule n) (i : Fin n) (C T R : ℕ) where
  /-- sensor-sampling time of job `k` -/
  start : ℕ → ℕ
  /-- actuation time of job `k` -/
  finish : ℕ → ℕ
  release_le_start : ∀ k, k * T ≤ start k
  start_le_finish : ∀ k, start k ≤ finish k
  executes : ∀ k, C ≤ served s i (k * T) (finish k)
  response_le : ∀ k, finish k ≤ k * T + R

namespace ControlTrace

variable {n : ℕ} {s : Schedule n} {i : Fin n} {C T R : ℕ} (tr : ControlTrace s i C T R)
include tr

/-- Best-case response time: every job needs at least `C` slots after its release. -/
theorem C_le_response (k : ℕ) : k * T + C ≤ tr.finish k := by
  have h1 := tr.executes k
  have h2 := served_le s i (k * T) (tr.finish k)
  have h3 := tr.release_le_start k
  have h4 := tr.start_le_finish k
  omega

/-- Sensor-to-actuator latency is at most the worst-case response time `R`. -/
theorem latency_le (k : ℕ) : tr.finish k - tr.start k ≤ R := by
  have := tr.release_le_start k; have := tr.response_le k; omega

/-- If `R ≤ T` ("the sample period fits"), job `k` actuates no later than the next release, so
actuations happen once per period, in order. -/
theorem finish_le_next_release (hRT : R ≤ T) (k : ℕ) : tr.finish k ≤ (k + 1) * T := by
  have := tr.response_le k; rw [add_mul, one_mul]; omega

/-- Output (response-time) jitter is at most `R - C`. -/
theorem jitter_le (j k : ℕ) :
    |((tr.finish k : ℤ) - k * T) - ((tr.finish j : ℤ) - j * T)| ≤ (R : ℤ) - C := by
  have hk1 := tr.C_le_response k; have hk2 := tr.response_le k
  have hj1 := tr.C_le_response j; have hj2 := tr.response_le j
  rw [abs_le]; constructor <;> omega

/-- The actual sampling-to-actuation interval between consecutive actuations deviates from the
nominal period `T` by at most `R - C`. -/
theorem actuation_interval (k : ℕ) :
    (T : ℤ) - (R - C) ≤ (tr.finish (k + 1) : ℤ) - tr.finish k ∧
      (tr.finish (k + 1) : ℤ) - tr.finish k ≤ T + (R - C) := by
  have := tr.jitter_le k (k + 1)
  rw [abs_le] at this
  push_cast at this
  constructor <;> nlinarith [this.1, this.2]

end ControlTrace

section LLAsymptotics

open Filter Topology

/-- The Liu–Layland utilization bound `n (2^{1/n} - 1)` (as a real function). -/
noncomputable def llBound (x : ℝ) : ℝ := x * ((2 : ℝ) ^ (1 / x) - 1)

/-- `x (2^{1/x} - 1)` is antitone on `x > 0`: it is the secant slope of the convex function
`y ↦ 2^y` between `0` and `1/x`. -/
theorem llBound_antitoneOn : AntitoneOn llBound (Set.Ioi 0) := by
  intro m hm n hn hmn
  simp only [Set.mem_Ioi] at hm hn
  have hc := convexOn_rpow_left (b := 2) (by norm_num)
  have h := hc.secant_mono (a := 0) (x := 1 / n) (y := 1 / m) (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) (by positivity) (by positivity) (one_div_le_one_div_of_le hm hmn)
  simp only [Real.rpow_zero, sub_zero, div_div_eq_mul_div, div_one] at h
  unfold llBound
  linarith [mul_comm (n:ℝ) ((2:ℝ) ^ (1 / n) - 1), mul_comm (m:ℝ) ((2:ℝ) ^ (1 / m) - 1)]

/-- For `n = 2` the bound is `2(√2 - 1) ≈ 0.828`, matching `rm_two_tasks_schedulable`. -/
theorem llBound_two : llBound 2 = 2 * (Real.sqrt 2 - 1) := by
  rw [llBound, Real.sqrt_eq_rpow]

/-- For a single task the bound is `1`. -/
theorem llBound_one : llBound 1 = 1 := by norm_num [llBound]

/-- `n (2^{1/n} - 1) → ln 2 ≈ 0.693` as `n → ∞` (derivative of `2^y` at `0`). -/
theorem tendsto_llBound : Tendsto (fun n : ℕ => llBound n) atTop (𝓝 (Real.log 2)) := by
  have hd := (Real.hasStrictDerivAt_const_rpow (a := 2) (by norm_num) 0).hasDerivAt
  have h1 := hd.tendsto_slope_zero_right
  simp only [Real.rpow_zero, one_mul, zero_add, smul_eq_mul] at h1
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Set.mem_Ioi]; positivity
  refine (h1.comp h2).congr fun n => ?_
  simp [llBound]

/-- Hence `ln 2 ≤ n (2^{1/n} - 1)` for every `n ≥ 1`: any task set with `U ≤ ln 2` is below every
Liu–Layland threshold. -/
theorem log_two_le_llBound (n : ℕ) (hn : 1 ≤ n) : Real.log 2 ≤ llBound n := by
  have hanti : Antitone fun m : ℕ => llBound ((m + 1 : ℕ) : ℝ) := by
    refine antitone_nat_of_succ_le fun m => llBound_antitoneOn ?_ ?_ ?_
    · show (0 : ℝ) < ((m + 1 : ℕ) : ℝ); positivity
    · show (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ); positivity
    · push_cast; linarith
  have ht : Tendsto (fun m : ℕ => llBound ((m + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log 2)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_llBound
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hanti.le_of_tendsto ht m

end LLAsymptotics

end RealTime
