import RoboLean.RealTime

/-!
# Critical instant, EDF forever, and the general Liu–Layland bound

Discrete time `ℕ`, uniprocessor, preemptive scheduling. Builds on `RoboLean.RealTime`.

* **Critical instant theorem (response-time form)** `response_le`: for an *arbitrary* sporadic
  arrival pattern (`Arrivals`: any release offsets, minimum inter-arrival time `Tₖ` between jobs of
  task `k`, job costs `≤ Cₖ`, possibly infinitely many jobs) and *any* fixed-priority
  work-conserving schedule (`IsFP`), every job of task `i` completes within `R` of its release,
  where `R ≤ Tᵢ` is any pre-fixed point of `R = Cᵢ + ∑_{k<i} ⌈R/Tₖ⌉ Cₖ`. Proof: level-`i` quiet
  instants (`Quiet`); from any quiet instant another one follows within `R` (`exists_quiet`);
  apply it at the last quiet instant `≤` the release. No assumption on earlier jobs of task `i` or
  on higher-priority deadlines is needed (`R ≤ Tᵢ` ensures one job of task `i` per window).
  Corollaries: `response_le_of_rta`, `all_deadlines_met` (constrained deadlines `Dᵢ ≤ Tᵢ`),
  concrete simulated FP scheduler `fpSchedJ` (`fpSchedJ_isFP`), periodic tasks with offsets
  (`fpOffsets_response`), and every job of `RealTime.fpSched` (`fpSched_every_job`).
* **EDF forever** `edf_repeated_meets_forever`, `periodicExt_meets`, `schedulable_forever_iff`.
* **Liu–Layland bound, general `n`** `rm_ll_bound`, `rm_ll_schedulable`: rate-monotonic,
  implicit deadlines, `U ≤ n(2^{1/n}-1)` ⇒ every RTA succeeds ⇒ all deadlines met. Proof: period
  transformation `Tⱼ ↦ ⌊Tᵢ/Tⱼ⌋Tⱼ ∈ (Tᵢ/2, Tᵢ]` (demand only grows), sorting, RTA failure at the
  transformed periods, an explicit LP dual certificate (`ll_dual`), and AM–GM (`ll_real`).
-/

namespace RealTime
namespace CriticalInstant

open Finset

variable {n : ℕ}

/-- A general (sporadic) arrival pattern of jobs of the task set `τ`. -/
structure Arrivals (τ : Fin n → Task) (J : Type*) where
  /-- the task a job belongs to -/
  task : J → Fin n
  /-- release time -/
  r : J → ℕ
  /-- actual execution requirement -/
  c : J → ℕ
  /-- costs are bounded by the task's WCET -/
  c_le : ∀ j, c j ≤ (τ (task j)).C
  /-- minimum inter-arrival time `T` between distinct jobs of the same task -/
  sep : ∀ j j', j ≠ j' → task j = task j' →
    r j + (τ (task j)).T ≤ r j' ∨ r j' + (τ (task j)).T ≤ r j

variable {τ : Fin n → Task} {J : Type*} [DecidableEq J]

/-- Fixed-priority preemptive work-conserving schedule (lower task index = higher priority):
only pending jobs run, and whenever a job is pending the running job's task has priority at
least as high. (Order among jobs of the same task is arbitrary.) -/
structure IsFP (A : Arrivals τ J) (s : ℕ → Option J) : Prop where
  runs_pending : ∀ t j, s t = some j → A.r j ≤ t ∧ served s j 0 t < A.c j
  fp_choice : ∀ t j, A.r j ≤ t → served s j 0 t < A.c j →
    ∃ j', s t = some j' ∧ A.task j' ≤ A.task j

/-- Level-`i` quiet instant: every job of priority `≥` task `i` released before `t` is complete
at `t`. -/
def Quiet (A : Arrivals τ J) (s : ℕ → Option J) (i : Fin n) (t : ℕ) : Prop :=
  ∀ j, A.task j ≤ i → A.r j < t → A.c j ≤ served s j 0 t

theorem IsFP.served_le_cost {A : Arrivals τ J} {s : ℕ → Option J} (hs : IsFP A s) (j : J) :
    ∀ t, served s j 0 t ≤ A.c j := by
  intro t
  induction t with
  | zero => simp [served]
  | succ t ih =>
    rw [served_succ]
    split_ifs with h
    · have := (hs.runs_pending t j h).2; omega
    · omega

theorem card_sep_le (A : Arrivals τ J) (k : Fin n) (hT : 0 < (τ k).T) (q L : ℕ) (S : Finset J)
    (hS : ∀ j ∈ S, A.task j = k ∧ q ≤ A.r j ∧ A.r j < q + L) :
    S.card ≤ cdiv L (τ k).T := by
  have h := Finset.card_le_card_of_injOn (fun j => (A.r j - q) / (τ k).T) (t := Finset.range (cdiv L (τ k).T))
    (s := S) ?_ ?_
  · simpa using h
  · intro j hj
    obtain ⟨-, h1, h2⟩ := hS j hj
    simp only [coe_range, Set.mem_Iio]
    have e : cdiv L (τ k).T = (L - 1) / (τ k).T + 1 := by
      unfold cdiv
      rw [show L + (τ k).T - 1 = (L - 1) + (τ k).T by omega, Nat.add_div_right _ hT]
    rw [e, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  · intro j hj j' hj' heq
    simp only at heq
    by_contra hne
    obtain ⟨hk, h1, -⟩ := hS j hj
    obtain ⟨hk', h1', -⟩ := hS j' hj'
    have hsep := A.sep j j' hne (hk.trans hk'.symm)
    rw [hk] at hsep
    rcases hsep with h | h
    · have : (A.r j - q) / (τ k).T + 1 ≤ (A.r j' - q) / (τ k).T := by
        rw [← Nat.add_div_right _ hT]; exact Nat.div_le_div_right (by omega)
      omega
    · have : (A.r j' - q) / (τ k).T + 1 ≤ (A.r j - q) / (τ k).T := by
        rw [← Nat.add_div_right _ hT]; exact Nat.div_le_div_right (by omega)
      omega

theorem interference_higherPrio (i : Fin n) (R : ℕ) :
    interference ((higherPrio i).map τ) R =
      ∑ k ∈ univ.filter (· < i), cdiv R (τ k).T * (τ k).C := by
  have h1 : (higherPrio i).toFinset = univ.filter (· < i) := by
    ext k; simp [mem_higherPrio]
  rw [← h1, List.sum_toFinset _ (higherPrio_nodup i), interference, List.map_map]
  rfl

/-- **Busy windows are short.** From any level-`i` quiet instant `q`, another quiet instant
occurs within `(q, q + R]`. -/
theorem exists_quiet {A : Arrivals τ J} {s : ℕ → Option J} (hs : IsFP A s)
    (hT : ∀ k, 0 < (τ k).T) (i : Fin n) {R : ℕ}
    (hR : rtaStep (τ i).C ((higherPrio i).map τ) R ≤ R) (hRT : R ≤ (τ i).T) (hR0 : 0 < R)
    {q : ℕ} (hq : Quiet A s i q) : ∃ q', q < q' ∧ q' ≤ q + R ∧ Quiet A s i q' := by
  classical
  by_contra hno
  push Not at hno
  -- every slot of `[q, q+R)` runs a level-`i` job
  have hbusy : ∀ t, q ≤ t → t < q + R → ∃ j', s t = some j' ∧ A.task j' ≤ i := by
    intro t h1 h2
    have hnq := hno (t + 1) (by omega) (by omega)
    simp only [Quiet, not_forall, not_le] at hnq
    obtain ⟨j, hji, hjr, hjs⟩ := hnq
    have := served_mono_right s j 0 (Nat.le_add_right t 1)
    obtain ⟨j', h1', h2'⟩ := hs.fp_choice t j (by omega) (by omega)
    exact ⟨j', h1', h2'.trans hji⟩
  have hnq := hno (q + R) (by omega) le_rfl
  simp only [Quiet, not_forall, not_le] at hnq
  obtain ⟨js, hjsi, hjsr, hjss⟩ := hnq
  have hjsq : q ≤ A.r js := by
    by_contra h
    push Not at h
    have := hq js hjsi h
    have := served_mono_right s js 0 (show q ≤ q + R by omega)
    omega
  -- jobs running in the window
  set W : Finset J := insert js
    (((Finset.Ico q (q + R)).biUnion fun t => (s t).toFinset).filter fun j => A.task j ≤ i) with hW
  have hWprop : ∀ j ∈ W, A.task j ≤ i ∧ q ≤ A.r j ∧ A.r j < q + R := by
    intro j hj
    rw [hW, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ⟨hjsi, hjsq, hjsr⟩
    rw [Finset.mem_filter, Finset.mem_biUnion] at hj
    obtain ⟨⟨t, ht, hjt⟩, hji⟩ := hj
    rw [Finset.mem_Ico] at ht
    have hst : s t = some j := by simpa using hjt
    obtain ⟨hr, hsv⟩ := hs.runs_pending t j hst
    refine ⟨hji, ?_, by omega⟩
    by_contra h
    push Not at h
    have := hq j hji h
    have := served_mono_right s j 0 ht.1
    omega
  have hcount : R ≤ ∑ j ∈ W, served s j q (q + R) := by
    have hslot : ∀ t ∈ Finset.Ico q (q + R), 1 ≤ ∑ j ∈ W, (if s t = some j then 1 else 0) := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      obtain ⟨j', h1, h2⟩ := hbusy t ht.1 ht.2
      have hmem : j' ∈ W := by
        rw [hW]
        refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, h2⟩)
        exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_Ico.mpr ht, by simp [h1]⟩
      calc 1 = (if s t = some j' then 1 else 0) := by simp [h1]
        _ ≤ _ := Finset.single_le_sum (f := fun j => if s t = some j then 1 else 0)
            (fun _ _ => Nat.zero_le _) hmem
    calc R = ∑ _t ∈ Finset.Ico q (q + R), 1 := by simp
      _ ≤ ∑ t ∈ Finset.Ico q (q + R), ∑ j ∈ W, (if s t = some j then 1 else 0) :=
          Finset.sum_le_sum hslot
      _ = ∑ j ∈ W, served s j q (q + R) := by rw [Finset.sum_comm]; rfl
  have hwin : ∀ j, served s j q (q + R) ≤ served s j 0 (q + R) := by
    intro j
    rw [← served_add s j (Nat.zero_le q) (show q ≤ q + R by omega)]; omega
  have hlt : ∑ j ∈ W, served s j q (q + R) < ∑ j ∈ W, A.c j :=
    Finset.sum_lt_sum (fun j _ => (hwin j).trans (hs.served_le_cost j _))
      ⟨js, Finset.mem_insert_self _ _, lt_of_le_of_lt (hwin js) hjss⟩
  -- demand of the window jobs
  have hdem : ∑ j ∈ W, A.c j ≤ ∑ k ∈ univ.filter (· ≤ i), cdiv R (τ k).T * (τ k).C := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := A.task) (t := univ.filter (· ≤ i))
      (fun j hj => by simpa using (hWprop j hj).1)]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ∑ j ∈ W.filter (fun j => A.task j = k), A.c j
        ≤ ∑ j ∈ W.filter (fun j => A.task j = k), (τ k).C := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          rw [← hj.2]; exact A.c_le j
      _ = (W.filter (fun j => A.task j = k)).card * (τ k).C := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ cdiv R (τ k).T * (τ k).C := by
          refine Nat.mul_le_mul_right _ (card_sep_le A k (hT k) q R _ fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          obtain ⟨-, h2, h3⟩ := hWprop j hj.1
          exact ⟨hj.2, h2, h3⟩
  have hsplit : univ.filter (· ≤ i) = insert i (univ.filter (· < i)) := by
    ext k; simp [le_iff_lt_or_eq, or_comm]
  have hi1 : cdiv R (τ i).T ≤ 1 := by
    have e := cdiv_mul_self 1 (τ i).T (hT i)
    rw [one_mul] at e
    have := cdiv_mono (τ i).T hRT
    omega
  rw [hsplit, Finset.sum_insert (s := univ.filter (· < i)) (a := i) (by simp)] at hdem
  have hint := interference_higherPrio (τ := τ) i R
  unfold rtaStep at hR
  have : cdiv R (τ i).T * (τ i).C ≤ (τ i).C := by nlinarith
  omega

/-- **Critical instant theorem (Liu–Layland), response-time form.** In any fixed-priority
preemptive work-conserving uniprocessor schedule of an arbitrary sporadic arrival pattern
(arbitrary release offsets, minimum inter-arrival times `Tₖ`), every job of task `i` released at
time `a` completes by `a + R`, where `R` is any pre-fixed point of the RTA recurrence
`Cᵢ + ∑_{k<i} ⌈R/Tₖ⌉ Cₖ ≤ R` with `R ≤ Tᵢ`. -/
theorem response_le {A : Arrivals τ J} {s : ℕ → Option J} (hs : IsFP A s)
    (hT : ∀ k, 0 < (τ k).T) (i : Fin n) {R : ℕ}
    (hR : rtaStep (τ i).C ((higherPrio i).map τ) R ≤ R) (hRT : R ≤ (τ i).T)
    (j₀ : J) (hj₀ : A.task j₀ = i) : A.c j₀ ≤ served s j₀ (A.r j₀) (A.r j₀ + R) := by
  classical
  rcases Nat.eq_zero_or_pos R with hR0 | hR0
  · have h1 := A.c_le j₀
    have h2 := C_le_of_prefix hR
    rw [hj₀] at h1
    omega
  set a := A.r j₀
  have hq0 : Quiet A s i 0 := fun j _ h => absurd h (Nat.not_lt_zero _)
  set t₀ := Nat.findGreatest (Quiet A s i) a with ht₀
  have hq : Quiet A s i t₀ := Nat.findGreatest_spec (P := Quiet A s i) (Nat.zero_le a) hq0
  have ht₀a : t₀ ≤ a := Nat.findGreatest_le a
  obtain ⟨q', h1, h2, h3⟩ := exists_quiet hs hT i hR hRT hR0 hq
  have hq'a : a < q' := by
    by_contra h
    push Not at h
    exact Nat.findGreatest_is_greatest h1 h h3
  have hdone := h3 j₀ hj₀.le hq'a
  have hz : served s j₀ 0 a = 0 := by
    unfold served
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    rw [if_neg]
    intro h
    have := (hs.runs_pending t j₀ h).1
    omega
  have := served_mono_right s j₀ 0 (show q' ≤ a + R by omega)
  have := served_add s j₀ (Nat.zero_le a) (show a ≤ a + R by omega)
  omega

/-- `rta` form: if the response-time analysis with deadline `D ≤ Tᵢ` returns `some R`, every job
of task `i` (any release time, any sporadic arrival pattern) completes within `R ≤ D`. -/
theorem response_le_of_rta {A : Arrivals τ J} {s : ℕ → Option J} (hs : IsFP A s)
    (hT : ∀ k, 0 < (τ k).T) (i : Fin n) {D R : ℕ} (hDT : D ≤ (τ i).T)
    (h : rta (τ i).C ((higherPrio i).map τ) D = some R) (j₀ : J) (hj₀ : A.task j₀ = i) :
    R ≤ D ∧ A.c j₀ ≤ served s j₀ (A.r j₀) (A.r j₀ + R) := by
  obtain ⟨h1, -, h3, -⟩ := rta_sound h
  exact ⟨h3, response_le hs hT i h1.le (h3.trans hDT) j₀ hj₀⟩

/-- **Whole-task-set schedulability (constrained deadlines).** If for every task `i` the RTA with
relative deadline `Dᵢ ≤ Tᵢ` succeeds, then in every fixed-priority schedule of every sporadic
arrival pattern each job meets its deadline `r + D_{task}`. -/
theorem all_deadlines_met {A : Arrivals τ J} {s : ℕ → Option J} (hs : IsFP A s)
    (hT : ∀ k, 0 < (τ k).T) (D : Fin n → ℕ) (hDT : ∀ i, D i ≤ (τ i).T)
    (hrta : ∀ i, (rta (τ i).C ((higherPrio i).map τ) (D i)).isSome) (j : J) :
    A.c j ≤ served s j (A.r j) (A.r j + D (A.task j)) := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (hrta (A.task j))
  obtain ⟨h1, h2⟩ := response_le_of_rta hs hT (A.task j) (hDT _) hR j rfl
  exact h2.trans (served_mono_right s j _ (by omega))

/-! ### A concrete fixed-priority scheduler for arbitrary (finite) arrival patterns -/

/-- Job set whose EDF key is the task index, i.e. fixed-priority scheduling. -/
def fpJobSet (A : Arrivals τ J) : JobSet J where
  r := A.r
  d j := A.task j
  c := A.c

theorem isFP_of_isEDF {A : Arrivals τ J} {s : ℕ → Option J} (h : IsEDF (fpJobSet A) s) :
    IsFP A s where
  runs_pending := h.runs_pending
  fp_choice t j hr hlt := by
    obtain ⟨j', h1, h2⟩ := h.edf_choice t j hr hlt
    exact ⟨j', h1, Fin.le_def.mpr h2⟩

/-- The simulated preemptive fixed-priority schedule of a finite arrival pattern. -/
noncomputable def fpSchedJ [Fintype J] (A : Arrivals τ J) : ℕ → Option J := edf (fpJobSet A)

theorem fpSchedJ_isFP [Fintype J] (A : Arrivals τ J) : IsFP A (fpSchedJ A) :=
  isFP_of_isEDF (edf_isEDF _)

/-- Periodic tasks with arbitrary release offsets `O`: job `(i, m)` released at `m Tᵢ + Oᵢ`. -/
def periodicArrivals (τ : Fin n → Task) (O : Fin n → ℕ) (M : ℕ) :
    Arrivals τ (Fin n × Fin M) where
  task j := j.1
  r j := j.2 * (τ j.1).T + O j.1
  c j := (τ j.1).C
  c_le _ := le_rfl
  sep j j' hne htask := by
    obtain ⟨k, m⟩ := j
    obtain ⟨k', m'⟩ := j'
    simp only at htask
    subst htask
    have hm : (m : ℕ) ≠ m' := fun h => hne (by simp [Fin.ext h])
    simp only
    rcases Nat.lt_or_gt_of_ne hm with h | h
    · left; nlinarith
    · right; nlinarith

/-- **Concrete instance with offsets.** In the simulated fixed-priority schedule of periodic tasks
with arbitrary offsets, every job `(i, m)` completes within `R` of its release whenever the RTA of
task `i` returns `some R` for a deadline `D ≤ Tᵢ`. -/
theorem fpOffsets_response (τ : Fin n → Task) (O : Fin n → ℕ) (M : ℕ) (hT : ∀ k, 0 < (τ k).T)
    (i : Fin n) (m : Fin M) {D R : ℕ} (hDT : D ≤ (τ i).T)
    (h : rta (τ i).C ((higherPrio i).map τ) D = some R) :
    R ≤ D ∧ (τ i).C ≤ served (fpSchedJ (periodicArrivals τ O M)) (i, m)
      (m * (τ i).T + O i) (m * (τ i).T + O i + R) :=
  response_le_of_rta (A := periodicArrivals τ O M) (fpSchedJ_isFP _) hT i hDT h (i, m) rfl

/-- **Every job (not only the synchronous one) of `RealTime.fpSched`.** The job-level schedule
underlying `fpSched τ M` completes job `k` of task `i` within `[k Tᵢ, k Tᵢ + R)`. -/
theorem fpSched_every_job (τ : Fin n → Task) (M : ℕ) (hT : ∀ k, 0 < (τ k).T)
    (i : Fin n) (k : Fin M) {D R : ℕ} (hDT : D ≤ (τ i).T)
    (h : rta (τ i).C ((higherPrio i).map τ) D = some R) :
    R ≤ D ∧ (τ i).C ≤ served (edf (fpJobs τ M)) (i, k) (k * (τ i).T) (k * (τ i).T + R) :=
  fpOffsets_response τ (fun _ => 0) M hT i k hDT h

/-! ## EDF feasibility forever: repeating the hyperperiod schedule -/

/-- Every deadline of every job `k` of every task (no horizon). -/
def MeetsAllDeadlines (τ : Fin n → Task) (s : Schedule n) : Prop :=
  ∀ i k, (τ i).C ≤ served s i (k * (τ i).T) ((k + 1) * (τ i).T)

/-- Periodic extension of a schedule on `[0, H)`. -/
def periodicExt (s : Schedule n) (H : ℕ) : Schedule n := fun t => s (t % H)

theorem periodicExt_add (s : Schedule n) (H t : ℕ) : periodicExt s H (t + H) = periodicExt s H t := by
  simp [periodicExt]

theorem served_periodicExt (s : Schedule n) (i : Fin n) (H q a b : ℕ) (hb : b ≤ H) :
    served (periodicExt s H) i (q * H + a) (q * H + b) = served s i a b := by
  unfold served
  rw [add_comm (q * H) a, add_comm (q * H) b, ← Finset.sum_Ico_add']
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_Ico] at ht
  simp only [periodicExt, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : t < H)]

/-- **A schedule feasible over one common multiple `H` of the periods, repeated with period `H`,
meets every deadline forever.** -/
theorem periodicExt_meets {τ : Fin n → Task} (s : Schedule n) (H : ℕ) (hT : ∀ i, 0 < (τ i).T)
    (hH : 0 < H) (hdvd : ∀ i, (τ i).T ∣ H) (hs : MeetsDeadlinesUpTo τ s H) :
    MeetsAllDeadlines τ (periodicExt s H) := by
  intro i k
  obtain ⟨m, hm⟩ := hdvd i
  have hTi := hT i
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm; omega
  set q := k / m
  set k' := k % m
  have hk : k = q * m + k' := (Nat.div_add_mod' k m).symm
  have hk' : k' < m := Nat.mod_lt _ hmpos
  have e1 : k * (τ i).T = q * H + k' * (τ i).T := by rw [hk, hm]; ring
  have e2 : (k + 1) * (τ i).T = q * H + (k' + 1) * (τ i).T := by rw [hk, hm]; ring
  have hle : (k' + 1) * (τ i).T ≤ H := by rw [hm, mul_comm]; exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk')
  rw [e1, e2, served_periodicExt s i H q _ _ hle]
  exact hs i k' hle

/-- The EDF task-level schedule of the jobs of the first hyperperiod. -/
noncomputable def edfTaskSched (τ : Fin n → Task) : Schedule n :=
  fun t => (edf (periodicJobs τ (hyperperiod τ)) t).map Sigma.fst

theorem edfTaskSched_meets (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hU : utilization τ ≤ 1) : MeetsDeadlinesUpTo τ (edfTaskSched τ) (hyperperiod τ) := by
  set H := hyperperiod τ
  set js := periodicJobs τ H
  have hdem := periodicJobs_demandOK τ H hT hU
  let sj := edf js
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
      served (edfTaskSched τ) i (k * (τ i).T) ((k + 1) * (τ i).T) := by
    unfold served
    refine Finset.sum_le_sum fun t _ => ?_
    split_ifs with h1 h2 <;> simp_all [j, edfTaskSched, sj, js, H]
  omega

/-- **EDF forever.** For synchronous periodic implicit-deadline tasks with `U ≤ 1`, the EDF
schedule of the first hyperperiod, repeated with period `H`, meets every deadline of every job. -/
theorem edf_repeated_meets_forever (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hU : utilization τ ≤ 1) :
    MeetsAllDeadlines τ (periodicExt (edfTaskSched τ) (hyperperiod τ)) :=
  periodicExt_meets _ _ hT (hyperperiod_pos τ hT) (dvd_hyperperiod τ) (edfTaskSched_meets τ hT hU)

/-- **Exact infinite-horizon test.** A schedule meeting every deadline forever exists iff
`U ≤ 1`; the witness is periodic with period `H`. -/
theorem schedulable_forever_iff (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T) :
    (∃ s : Schedule n, MeetsAllDeadlines τ s) ↔ utilization τ ≤ 1 := by
  constructor
  · rintro ⟨s, hs⟩
    exact utilization_le_one_of_meets τ hT s fun i k _ => hs i k
  · intro hU
    exact ⟨_, edf_repeated_meets_forever τ hT hU⟩

/-! ## The Liu–Layland utilization bound for general `n` -/

/-- AM–GM consequence: `N` nonnegative reals with product `2` sum to at least `N 2^{1/N}`. -/
theorem amgm_two (N : ℕ) (hN : 0 < N) (z : ℕ → ℝ) (hz : ∀ k ∈ range N, 0 ≤ z k)
    (hprod : ∏ k ∈ range N, z k = 2) : (N : ℝ) * (2 : ℝ) ^ (1 / (N : ℝ)) ≤ ∑ k ∈ range N, z k := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.geom_mean_le_arith_mean_weighted (range N) (fun _ => 1 / (N : ℝ)) z
    (fun _ _ => by positivity) (by simp; field_simp) hz
  rw [Real.finsetProd_rpow _ _ hz, hprod, ← Finset.mul_sum] at h
  have := mul_le_mul_of_nonneg_left h hNr.le
  rwa [← mul_assoc, mul_one_div_cancel hNr.ne', one_mul] at this

theorem prod_ratio (p : ℕ → ℝ) (hp : ∀ k, 0 < p k) (r : ℕ) :
    ∏ k ∈ range r, p (k + 1) / p k = p r / p 0 := by
  induction r with
  | zero => simp [(hp 0).ne']
  | succ r ih =>
    rw [prod_range_succ, ih]
    field_simp [(hp r).ne', (hp 0).ne']

theorem double_sum (p c : ℕ → ℝ) (r : ℕ) :
    ∑ k ∈ range r, (1 / p k - 1 / p (k + 1)) * ∑ j ∈ range (k + 1), c j =
      ∑ j ∈ range r, c j * (1 / p j - 1 / p r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    ring

/-- **LP-duality core of the Liu–Layland bound.** Sorted periods `p 0 ≤ … ≤ p r` with
`p r ≤ 2 p 0` (`p r` = period of the task under analysis), costs `c`, and the RTA failure
constraints at the points `p k`: `p k + 1 ≤ ∑_{j ≤ r} c j + ∑_{j < k} c j`. Then
`∑ c j / p j ≥ 2 p 0 / p r + ∑_{k<r} p (k+1) / p k - (r+1) + 1 / p r`. -/
theorem ll_dual (r : ℕ) (p c : ℕ → ℝ) (hp : ∀ k, 0 < p k) (hmono : ∀ k < r, p k ≤ p (k + 1))
    (h2 : p r ≤ 2 * p 0)
    (hA : ∀ k ≤ r, p k + 1 ≤ ∑ j ∈ range (r + 1), c j + ∑ j ∈ range k, c j) :
    2 * p 0 / p r + ∑ k ∈ range r, p (k + 1) / p k - (r + 1) + 1 / p r ≤
      ∑ j ∈ range (r + 1), c j / p j := by
  set S := ∑ j ∈ range (r + 1), c j
  have hy0 : 0 ≤ 2 / p r - 1 / p 0 := by
    rw [sub_nonneg, div_le_div_iff₀ (hp 0) (hp r)]; linarith
  have hyk : ∀ k ∈ range r, 0 ≤ 1 / p k - 1 / p (k + 1) := by
    intro k hk
    rw [mem_range] at hk
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (hp k) (hmono k hk)
  -- weighted sum of the constraints
  have hw : (2 / p r - 1 / p 0) * (p 0 + 1) +
      ∑ k ∈ range r, (1 / p k - 1 / p (k + 1)) * (p (k + 1) + 1) ≤
      (2 / p r - 1 / p 0) * S +
      ∑ k ∈ range r, (1 / p k - 1 / p (k + 1)) * (S + ∑ j ∈ range (k + 1), c j) := by
    refine add_le_add (mul_le_mul_of_nonneg_left (by simpa using hA 0 (Nat.zero_le _)) hy0) ?_
    exact sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
      (hA (k + 1) (by rw [mem_range] at hk; omega)) (hyk k hk)
  have e1 : ∑ k ∈ range r, (1 / p k - 1 / p (k + 1)) * (p (k + 1) + 1) =
      ∑ k ∈ range r, (p (k + 1) / p k - 1) + (1 / p 0 - 1 / p r) := by
    rw [← sum_range_sub' (fun k => 1 / p k), ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    field_simp [(hp k).ne', (hp (k + 1)).ne']
  have e2 : ∑ k ∈ range r, (1 / p k - 1 / p (k + 1)) * (S + ∑ j ∈ range (k + 1), c j) =
      (1 / p 0 - 1 / p r) * S + ∑ j ∈ range r, c j * (1 / p j - 1 / p r) := by
    rw [← double_sum, ← sum_range_sub' (fun k => 1 / p k), sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => by ring
  have e3 : ∑ j ∈ range (r + 1), c j / p j = ∑ j ∈ range r, c j * (1 / p j - 1 / p r) +
      S * (1 / p r) := by
    have : ∀ j, c j / p j = c j * (1 / p j) := fun j => by ring
    simp only [S, this, sum_range_succ, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  rw [e1, e2] at hw
  rw [e3]
  have e4 : (2 / p r - 1 / p 0) * (p 0 + 1) = 2 * p 0 / p r - 1 + 2 / p r - 1 / p 0 := by
    field_simp [(hp 0).ne', (hp r).ne']; ring
  rw [e4] at hw
  have : (r : ℝ) = ∑ k ∈ range r, (1 : ℝ) := by simp
  have e5 : ∑ k ∈ range r, (p (k + 1) / p k - 1) = ∑ k ∈ range r, p (k + 1) / p k - r := by
    rw [sum_sub_distrib, this]
  rw [e5] at hw
  have e6 : (2 / p r - 1 / p 0) * S + (1 / p 0 - 1 / p r) * S = S * (1 / p r) := by ring
  have e7 : 2 / p r = 2 * (1 / p r) := by ring
  linarith

/-- Real form of the Liu–Layland worst case: under the hypotheses of `ll_dual`, the normalised
utilization strictly exceeds `(r+1)(2^{1/(r+1)} - 1)`. -/
theorem ll_real (r : ℕ) (p c : ℕ → ℝ) (hp : ∀ k, 0 < p k) (hmono : ∀ k < r, p k ≤ p (k + 1))
    (h2 : p r ≤ 2 * p 0)
    (hA : ∀ k ≤ r, p k + 1 ≤ ∑ j ∈ range (r + 1), c j + ∑ j ∈ range k, c j) :
    llBound ((r + 1 : ℕ) : ℝ) < ∑ j ∈ range (r + 1), c j / p j := by
  have hd := ll_dual r p c hp hmono h2 hA
  let z : ℕ → ℝ := fun k => if k = 0 then 2 * p 0 / p r else p k / p (k - 1)
  have hz : ∀ k ∈ range (r + 1), 0 ≤ z k := by
    intro k _
    simp only [z]
    split_ifs
    · have := hp 0; have := hp r; positivity
    · have := hp k; have := hp (k - 1); positivity
  have hsum : ∑ k ∈ range (r + 1), z k = 2 * p 0 / p r + ∑ k ∈ range r, p (k + 1) / p k := by
    rw [sum_range_succ', add_comm]
    simp [z]
  have hprod : ∏ k ∈ range (r + 1), z k = 2 := by
    rw [prod_range_succ']
    simp only [z, if_pos, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    rw [prod_ratio p hp r]
    field_simp [(hp 0).ne', (hp r).ne']
  have hag := amgm_two (r + 1) (Nat.succ_pos r) z hz hprod
  rw [hsum] at hag
  have hpos : 0 < 1 / p r := by have := hp r; positivity
  unfold llBound
  push_cast at hag ⊢
  nlinarith

/-- **Liu–Layland utilization bound, general `n`.** Rate-monotonic priorities (task index order
with nondecreasing periods), implicit deadlines, positive periods. If
`U ≤ n (2^{1/n} - 1)` then the response-time analysis of every task succeeds with deadline `Tᵢ`
(hence, by `response_le_of_rta`, every job of every task meets its deadline under any sporadic
arrival pattern and any fixed-priority work-conserving schedule). -/
theorem rm_ll_bound (τ : Fin n → Task) (hT : ∀ i, 0 < (τ i).T)
    (hRM : Monotone fun i => (τ i).T) (hU : utilization τ ≤ llBound n) (i : Fin n) :
    (rta (τ i).C ((higherPrio i).map τ) (τ i).T).isSome := by
  classical
  by_contra hno
  rw [rta_isSome_iff] at hno
  push Not at hno
  set T := (τ i).T with hTdef
  set m := (i : ℕ) with hm
  let Q : Fin n → ℕ := fun x => T / (τ x).T
  let P : Fin n → ℕ := fun x => Q x * (τ x).T
  have hQ1 : ∀ x, x ≤ i → 1 ≤ Q x := fun x hx =>
    (Nat.one_le_div_iff (hT x)).mpr (hRM hx)
  have hPT : ∀ x, P x ≤ T := fun x => Nat.div_mul_le_self T (τ x).T
  have hQi : Q i = 1 := Nat.div_self (hT i)
  have hPi : P i = T := by show Q i * (τ i).T = T; rw [hQi, one_mul]
  have h2P : ∀ x, x ≤ i → T < 2 * P x := by
    intro x hx
    have h1 := hQ1 x hx
    have h2 : T < (Q x + 1) * (τ x).T := by
      have := Nat.lt_div_mul_add (a := T) (hT x)
      simp only [Q]; nlinarith
    simp only [P]; nlinarith
  let σ : Fin m → Fin n := fun j => ⟨j, by omega⟩
  let π := Tuple.sort (fun j => P (σ j))
  have hπ : Monotone ((fun j => P (σ j)) ∘ π) := Tuple.monotone_sort _
  let G : ℕ → Fin n := fun k => if h : k < m then σ (π ⟨k, h⟩) else i
  have hGle : ∀ k, G k ≤ i := by
    intro k; simp only [G]; split_ifs with h
    · exact Fin.le_def.mpr (by simp [σ]; omega)
    · exact le_rfl
  have hGlt : ∀ k < m, G k < i := by
    intro k hk; simp only [G, dif_pos hk]; exact Fin.lt_def.mpr (by simp [σ]; omega)
  have hGm : G m = i := by simp [G]
  have hGmono : ∀ k k', k ≤ k' → k' ≤ m → P (G k) ≤ P (G k') := by
    intro k k' hkk hk'
    rcases Nat.lt_or_ge k' m with h | h
    · simp only [G, dif_pos h, dif_pos (lt_of_le_of_lt hkk h)]
      exact hπ (Fin.le_def.mpr hkk)
    · have : k' = m := by omega
      subst this; rw [hGm, hPi]; exact hPT _
  have hreindex : ∀ {M : Type} [AddCommMonoid M] (f : Fin n → M), ∑ x ∈ univ.filter (· < i), f x = ∑ k ∈ range m, f (G k) := by
    intro M _ f
    have e1 : ∑ j : Fin m, f (σ j) = ∑ x ∈ univ.filter (· < i), f x := by
      refine Finset.sum_bij (fun j _ => σ j) (fun j _ => ?_) (fun a _ b _ h => ?_)
        (fun x hx => ?_) (fun _ _ => rfl)
      · simp only [mem_filter, mem_univ, true_and]; exact Fin.lt_def.mpr (show (j : ℕ) < i from j.2)
      · simp only [σ, Fin.mk.injEq] at h; exact Fin.ext h
      · simp only [mem_filter, mem_univ, true_and] at hx
        exact ⟨⟨x, Fin.lt_def.mp hx⟩, mem_univ _, rfl⟩
    rw [← e1, ← Equiv.sum_comp π, ← Fin.sum_univ_eq_sum_range (fun k => f (G k)) m]
    refine sum_congr rfl fun j _ => ?_
    simp [G]
  -- the integer constraints
  let a : ℕ → ℕ := fun k => Q (G k) * (τ (G k)).C
  have hA : ∀ k ≤ m, P (G k) + 1 ≤ ∑ j ∈ range (m + 1), a j + ∑ j ∈ range k, a j := by
    intro k hk
    have hf := hno (P (G k)) (hPT _)
    unfold rtaStep at hf
    rw [interference_higherPrio (τ := τ), hreindex] at hf
    have hb : ∀ k' ∈ range m, cdiv (P (G k)) (τ (G k')).T * (τ (G k')).C ≤ 2 * a k' := by
      intro k' hk'
      rw [mem_range] at hk'
      have hc : cdiv (P (G k)) (τ (G k')).T ≤ 2 * Q (G k') := by
        have h1 := cdiv_mono (τ (G k')).T (hPT (G k))
        have h2 : cdiv T (τ (G k')).T ≤ Q (G k') + 1 := by
          unfold cdiv
          have := Nat.add_div_right T (hT (G k'))
          have := Nat.div_le_div_right (c := (τ (G k')).T) (show T + (τ (G k')).T - 1 ≤ T + (τ (G k')).T by omega)
          simp only [Q]; omega
        have := hQ1 _ (hGle k')
        omega
      simp only [a]; nlinarith
    have hb' : ∀ k' ∈ Ico k m, cdiv (P (G k)) (τ (G k')).T * (τ (G k')).C ≤ a k' := by
      intro k' hk'
      rw [mem_Ico] at hk'
      have hc : cdiv (P (G k)) (τ (G k')).T ≤ Q (G k') := by
        have h1 := cdiv_mono (τ (G k')).T (hGmono k k' hk'.1 hk'.2.le)
        rwa [show P (G k') = Q (G k') * (τ (G k')).T from rfl, cdiv_mul_self _ _ (hT _)] at h1
      simp only [a]; exact Nat.mul_le_mul_right _ hc
    rw [← sum_range_add_sum_Ico _ hk] at hf
    have s2 := sum_le_sum hb'
    have s1 : ∑ k' ∈ range k, cdiv (P (G k)) (τ (G k')).T * (τ (G k')).C ≤ ∑ k' ∈ range k, 2 * a k' :=
      sum_le_sum fun k' hk' => hb k' (by rw [mem_range] at hk' ⊢; omega)
    rw [← mul_sum] at s1
    have ham : a m = (τ i).C := by simp only [a, hGm, hQi, one_mul]
    rw [sum_range_succ, ham, ← sum_range_add_sum_Ico a hk]
    omega
  -- pass to the reals
  have hPpos : ∀ k, 0 < P (G k) := fun k => Nat.mul_pos (hQ1 _ (hGle k)) (hT _)
  have hreal := ll_real m (fun k => (P (G k) : ℝ)) (fun k => (a k : ℝ))
    (fun k => by exact_mod_cast hPpos k)
    (fun k hk => by exact_mod_cast hGmono k (k + 1) (Nat.le_succ k) hk)
    (by
      have := h2P (G 0) (hGle 0)
      simp only [hGm, hPi]; exact_mod_cast this.le)
    (fun k hk => by exact_mod_cast hA k hk)
  have hterm : ∀ k, (a k : ℝ) / (P (G k) : ℝ) = ((τ (G k)).C : ℝ) / (τ (G k)).T := by
    intro k
    have hq : (Q (G k) : ℝ) ≠ 0 := by have := hQ1 _ (hGle k); positivity
    simp only [a, P]; push_cast
    exact mul_div_mul_left _ _ hq
  simp only [hterm] at hreal
  have hsub : ∑ k ∈ range (m + 1), ((τ (G k)).C : ℝ) / (τ (G k)).T ≤ utilization τ := by
    rw [sum_range_succ, hGm, ← hreindex (fun x => ((τ x).C : ℝ) / (τ x).T), utilization]
    rw [add_comm, ← sum_insert (s := univ.filter (· < i)) (a := i) (f := fun x => ((τ x).C : ℝ) / (τ x).T) (by simp)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
  have hmn : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
  have hanti := llBound_antitoneOn (a := ((m + 1 : ℕ) : ℝ)) (b := (n : ℝ))
    (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; exact_mod_cast (show 0 < n by omega)) hmn
  linarith


/-- **Liu–Layland theorem, end to end.** Rate-monotonic priorities, implicit deadlines, positive
periods, `U ≤ n (2^{1/n} - 1)`: in every fixed-priority work-conserving schedule of every sporadic
arrival pattern (arbitrary offsets, minimum inter-arrival `Tₖ`) each job completes within one
period of its release. -/
theorem rm_ll_schedulable {J : Type*} [DecidableEq J] {τ : Fin n → Task} {A : Arrivals τ J}
    {s : ℕ → Option J} (hs : IsFP A s) (hT : ∀ i, 0 < (τ i).T)
    (hRM : Monotone fun i => (τ i).T) (hU : utilization τ ≤ llBound n) (j : J) :
    A.c j ≤ served s j (A.r j) (A.r j + (τ (A.task j)).T) :=
  all_deadlines_met hs hT (fun i => (τ i).T) (fun _ => le_rfl) (rm_ll_bound τ hT hRM hU) j

end CriticalInstant
end RealTime
