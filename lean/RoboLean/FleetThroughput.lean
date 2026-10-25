import Mathlib

/-!
# When do extra robots stop helping? Throughput on a single-lane loop

**Plain-English summary.**  Put `n` robots on a one-way circular track of `L` cells, at most one
robot per cell.  Every robot follows the most trivial navigation logic there is:
*"if the cell in front of me is free, move into it; otherwise wait."*  All robots decide
simultaneously.  (This is elementary cellular automaton **rule 184**, a.k.a. deterministic
parallel TASEP.)  The *throughput* of a step is the number of robots that move.

We prove, for every `L ≥ 1` and every starting configuration:

* **Safety / conservation** (`count_step`, `dest_injective`, `step_eq_true_iff`): the rule is
  collision-free and never creates or destroys robots.
* **Throughput ceiling** (`flow_le_min`, `total_flow_le`): in every single step at most
  `min n (L - n)` robots move — each mover is a robot *and* enters a distinct currently-empty
  cell.  So the average throughput over any horizon is `≤ min n (L - n)`, which as a function of
  fleet size peaks at `n = ⌊L/2⌋` (`min_le_half`).
* **Monotone relaxation** (`numBlocked_step_le`, `flow_le_flow_step`): the number of blocked
  robots never increases, so throughput never decreases over time.
* **Free flow at low density** (`freeFlow_eventually`): if `2n ≤ L` then from step `n - 1` on no
  robot is ever blocked and all `n` robots move every step.  (The transient `n - 1` is tight:
  see the `L = 6` example `111000`.)  The proof is a "jam light-cone" argument: a blocked robot at
  time `s` forces a window of `2s + 2` consecutive cells at time `0` to hold `≥ s + 2` robots.
* **Jammed regime** (`jammed_eventually`): if `2n ≥ L` then from step `L - n - 1` on exactly
  `L - n` robots move every step, derived from free flow via the **particle–hole symmetry**
  `step_reflect` (holes are robots driving backwards under the same rule).
* **Fundamental diagram** (`eventual_flow`): after at most `min n (L - n) - 1` steps throughput is
  exactly `min n (L - n)`, forever.

**Managerial reading** (`marginal_gain`, `marginal_loss`, `flow_eq_zero_of_full`): *on a loop of
`L` cells with move-if-free logic, the `k`-th robot adds one unit of steady-state throughput iff
`k ≤ L/2`; beyond that every extra robot costs one unit (for odd `L` the single robot
`k = (L+1)/2` is neutral, `marginal_plateau`); at `n = L` throughput is `0`.*  Hence
once the fleet exceeds half the track length, trivial logic is strictly counter-productive: one
needs a fleet manager (admission control / parking) or more track.

Configurations are `Fin L → Bool` (`true` = occupied); `count_eq_card` relates `count` to the
cardinality of the `Finset` of occupied cells.  Deadlock questions are handled separately in
`RoboLean.FleetDeadlock`.
-/

open Fin.NatCast Fin.CommRing Finset

namespace RoboLean.FleetThroughput

variable {L : ℕ} [NeZero L]

/-- A configuration of the loop: `c i = true` iff cell `i` holds a robot.  Cell `i + 1` is the
cell in front of cell `i` (indices wrap around mod `L`). -/
abbrev Config (L : ℕ) := Fin L → Bool

/-- One synchronous step of the move-if-free rule (rule 184): cell `i` is occupied afterwards iff
its robot was blocked (`c i ∧ c (i+1)`), or it was empty and the robot behind it moved in. -/
def step (c : Config L) : Config L := fun i => (c i && c (i + 1)) || (!c i && c (i - 1))
/-- The robot in cell `i` moves this step (it exists and the cell in front is empty). -/
def moves (c : Config L) (i : Fin L) : Bool := c i && !c (i + 1)
/-- The robot in cell `i` is blocked (the cell in front is occupied). -/
def blocked (c : Config L) (i : Fin L) : Bool := c i && c (i + 1)
/-- Fleet size: the number of occupied cells. -/
def count (c : Config L) : ℕ := ∑ i, (c i).toNat
/-- Throughput of one step: the number of robots that move. -/
def flow (c : Config L) : ℕ := ∑ i, (moves c i).toNat
/-- Number of blocked robots. -/
def numBlocked (c : Config L) : ℕ := ∑ i, (blocked c i).toNat
/-- Number of robots in the window of `m` consecutive cells starting at `a`. -/
def seg (c : Config L) (a : Fin L) (m : ℕ) : ℕ := ∑ k ∈ range m, (c (a + (k : Fin L))).toNat

/-- Local conservation law (continuity equation): occupancy change = inflow − outflow. -/
theorem step_local (c : Config L) (j : Fin L) :
    ((step c j).toNat : ℤ) = (c j).toNat + (moves c (j - 1)).toNat - (moves c j).toNat := by
  unfold step moves
  rw [sub_add_cancel]
  cases c (j - 1) <;> cases c j <;> cases c (j + 1) <;> rfl

theorem sum_shift (f : Fin L → ℕ) : ∑ i, f (i - 1) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)

/-- **Conservation.** A step never creates or destroys robots. -/
theorem count_step (c : Config L) : count (step c) = count c := by
  have h : ((count (step c) : ℕ) : ℤ) = count c := by
    unfold count
    push_cast
    simp_rw [step_local]
    rw [sum_sub_distrib, sum_add_distrib]
    have := sum_shift (fun i => (moves c i).toNat)
    have h2 : ∑ i, ((moves c (i - 1)).toNat : ℤ) = ∑ i, ((moves c i).toNat : ℤ) := by
      exact_mod_cast this
    rw [h2]; ring
  exact_mod_cast h

theorem moves_le (c : Config L) (i : Fin L) : (moves c i).toNat ≤ (c i).toNat := by
  unfold moves; cases c i <;> cases c (i+1) <;> decide

/-- At most `n` robots move. -/
theorem flow_le_count (c : Config L) : flow c ≤ count c := sum_le_sum fun i _ => moves_le c i

omit [NeZero L] in
/-- Robots plus empty cells fill the loop. -/
theorem count_add_holes (c : Config L) : count c + ∑ i, (!c i).toNat = L := by
  unfold count
  rw [← sum_add_distrib]
  have : ∀ i, (c i).toNat + (!c i).toNat = 1 := fun i => by cases c i <;> rfl
  simp [this]

/-- Each mover enters a distinct currently-empty cell, so `flow ≤ L - n`. -/
theorem flow_add_count_le (c : Config L) : flow c + count c ≤ L := by
  have h1 : flow c ≤ ∑ i, (!c i).toNat := by
    unfold flow
    rw [← sum_shift]
    refine sum_le_sum fun i _ => ?_
    unfold moves; rw [sub_add_cancel]; cases c (i-1) <;> cases c i <;> decide
  have := count_add_holes c
  omega

/-- Every robot either moves or is blocked. -/
theorem count_eq_flow_add_numBlocked (c : Config L) : count c = flow c + numBlocked c := by
  unfold count flow numBlocked
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold moves blocked; cases c i <;> cases c (i+1) <;> rfl

/-- A blocked robot at `b` after a step forces a blocked robot at `b + 1` before it. -/
theorem blocked_step (c : Config L) (b : Fin L) (h : blocked (step c) b = true) :
    blocked c (b + 1) = true := by
  unfold blocked step at *
  rw [add_sub_cancel_right] at h
  have e : b + 1 + 1 = b + 1 + 1 := rfl
  revert h
  cases c (b - 1) <;> cases c b <;> cases c (b+1) <;> cases c (b + 1 + 1) <;> decide

/-- **The number of blocked robots never increases.** -/
theorem numBlocked_step_le (c : Config L) : numBlocked (step c) ≤ numBlocked c := by
  unfold numBlocked
  calc ∑ i, (blocked (step c) i).toNat ≤ ∑ i, (blocked c (i + 1)).toNat :=
        sum_le_sum fun i _ => by
          have := blocked_step c i
          cases h : blocked (step c) i
          · simp
          · simp [this h]
    _ = ∑ i, (blocked c i).toNat := Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

/-- **Throughput never decreases over time.** -/
theorem flow_le_flow_step (c : Config L) : flow c ≤ flow (step c) := by
  have h1 := count_eq_flow_add_numBlocked c
  have h2 := count_eq_flow_add_numBlocked (step c)
  have h3 := numBlocked_step_le c
  rw [count_step] at h2
  omega


/-- Window version of the continuity equation. -/
theorem seg_step (c : Config L) (a : Fin L) (m : ℕ) :
    (seg (step c) a m : ℤ) = seg c a m + (moves c (a - 1)).toNat
      - (moves c (a + (m : Fin L) - 1)).toNat := by
  induction m with
  | zero => simp [seg]
  | succ m ih =>
    unfold seg at *
    push_cast at *
    rw [sum_range_succ, sum_range_succ, ih, step_local]
    have : a + ((m : Fin L) + 1) - 1 = a + (m : Fin L) := by ring
    rw [this]; ring

theorem seg_cons (c : Config L) (a : Fin L) (m : ℕ) :
    seg c (a - 1) (m + 2) = (c (a - 1)).toNat + seg c a m + (c (a + (m : Fin L))).toNat := by
  unfold seg
  rw [sum_range_succ, sum_range_succ']
  have h1 : ∀ k : ℕ, a - 1 + ((k + 1 : ℕ) : Fin L) = a + (k : Fin L) := fun k => by push_cast; ring
  simp only [h1, Nat.cast_zero, add_zero]
  ring

/-- One backward step of the jam light-cone. -/
theorem back_one (c : Config L) (a : Fin L) (m : ℕ)
    (h : blocked (step c) (a + (m : Fin L) - 1) = true) :
    blocked c (a - 1 + ((m + 2 : ℕ) : Fin L) - 1) = true ∧
      seg (step c) a m + 1 ≤ seg c (a - 1) (m + 2) := by
  have hb := blocked_step c _ h
  have e : a + (m : Fin L) - 1 + 1 = a - 1 + ((m + 2 : ℕ) : Fin L) - 1 := by push_cast; ring
  refine ⟨e ▸ hb, ?_⟩
  have hs := seg_step c a m
  have hc := seg_cons c a m
  have e2 : a + (m : Fin L) - 1 + 1 = a + (m : Fin L) := by ring
  unfold blocked at hb
  rw [e2] at hb
  have hcm : c (a + (m : Fin L)) = true := by
    revert hb; cases c (a + (m : Fin L)) <;> simp
  have hmv : (moves c (a + (m : Fin L) - 1)).toNat = 0 := by
    unfold moves; rw [e2, hcm]; simp
  have hmv2 := moves_le c (a - 1)
  rw [hcm] at hc
  simp only [Bool.toNat_true] at hc
  omega

/-- **Jam light-cone.** If the last robot of a window is blocked after `s` steps, then `s` steps
earlier the window widened by `s` on each side held at least `s` more robots (and also ends in a
blocked robot). -/
theorem back_iter (s : ℕ) : ∀ (c : Config L) (a : Fin L) (m : ℕ),
    blocked (step^[s] c) (a + (m : Fin L) - 1) = true →
    blocked c (a - (s : Fin L) + ((m + 2 * s : ℕ) : Fin L) - 1) = true ∧
      seg (step^[s] c) a m + s ≤ seg c (a - (s : Fin L)) (m + 2 * s) := by
  induction s with
  | zero => intro c a m h; simpa using h
  | succ s ih =>
    intro c a m h
    rw [Function.iterate_succ_apply'] at h
    obtain ⟨h1, h2⟩ := back_one _ a m h
    have e : a - 1 + ((m + 2 : ℕ) : Fin L) - 1 = (a - 1) + (((m + 2 : ℕ) : ℕ) : Fin L) - 1 := rfl
    obtain ⟨h3, h4⟩ := ih c (a - 1) (m + 2) h1
    have e1 : a - 1 - (s : Fin L) = a - ((s + 1 : ℕ) : Fin L) := by push_cast; ring
    have e2 : m + 2 + 2 * s = m + 2 * (s + 1) := by ring
    rw [e1, e2] at h3 h4
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by omega⟩

/-- A window of at most `L` cells holds at most `n` robots. -/
theorem seg_le_count (c : Config L) (a : Fin L) (m : ℕ) (hm : m ≤ L) : seg c a m ≤ count c := by
  unfold seg count
  rw [← sum_image (f := fun j => (c j).toNat) (g := fun k : ℕ => a + (k : Fin L))]
  · exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  · intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    have := congrArg Fin.val (add_left_cancel hxy)
    simp only [Fin.val_natCast] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this


/-- Conservation over any number of steps. -/
theorem count_iterate (c : Config L) (t : ℕ) : count (step^[t] c) = count c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', count_step, ih]

/-- Free flow: no robot has a robot directly in front of it. -/
def FreeFlow (c : Config L) : Prop := ∀ i, blocked c i = false

/-- In free flow the whole fleet just rotates one cell forward. -/
theorem step_of_freeFlow (c : Config L) (h : FreeFlow c) : step c = fun i => c (i - 1) := by
  funext i
  have h1 := h i
  have h2 := h (i - 1)
  unfold blocked at h1 h2
  rw [sub_add_cancel] at h2
  unfold step
  revert h1 h2
  cases c (i - 1) <;> cases c i <;> cases c (i + 1) <;> decide

/-- Free flow persists. -/
theorem freeFlow_step (c : Config L) (h : FreeFlow c) : FreeFlow (step c) := by
  intro i
  rw [step_of_freeFlow c h]
  have := h (i - 1)
  unfold blocked at *
  simp only [add_sub_cancel_right]
  rwa [sub_add_cancel] at this

theorem freeFlow_iterate (c : Config L) (h : FreeFlow c) (t : ℕ) : FreeFlow (step^[t] c) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact freeFlow_step _ ih

theorem numBlocked_eq_zero (c : Config L) (h : FreeFlow c) : numBlocked c = 0 := by
  unfold numBlocked
  exact sum_eq_zero fun i _ => by rw [h i]; rfl

/-- In free flow every robot moves. -/
theorem flow_eq_count_of_freeFlow (c : Config L) (h : FreeFlow c) : flow c = count c := by
  rw [count_eq_flow_add_numBlocked, numBlocked_eq_zero c h, add_zero]

theorem freeFlow_of_count_eq_zero (c : Config L) (h : count c = 0) : FreeFlow c := by
  intro i
  unfold count at h
  rw [sum_eq_zero_iff] at h
  have := h i (mem_univ _)
  unfold blocked
  cases hc : c i
  · rfl
  · rw [hc] at this; simp at this

/-- At low density (`2n ≤ L`, `n ≥ 1`), the fleet is in free flow at step `n - 1`. -/
theorem freeFlow_at (c : Config L) (n : ℕ) (hn : count c = n) (h1 : 1 ≤ n) (h2 : 2 * n ≤ L) :
    FreeFlow (step^[n - 1] c) := by
  intro b
  by_contra hb
  rw [Bool.not_eq_false] at hb
  set s := n - 1 with hs
  have hb' : blocked (step^[s] c) (b + ((1 : ℕ) : Fin L) - 1) = true := by
    simpa using hb
  obtain ⟨h3, h4⟩ := back_iter s c b 1 hb'
  have hd : seg (step^[s] c) b 1 = 1 := by
    unfold blocked at hb
    unfold seg; simp only [range_one, sum_singleton, Nat.cast_zero, add_zero]
    revert hb; cases step^[s] c b <;> simp
  unfold blocked at h3
  have h5 : c (b - (s : Fin L) + ((1 + 2 * s : ℕ) : Fin L)) = true := by
    rw [sub_add_cancel] at h3
    revert h3; cases c (b - (s : Fin L) + ((1 + 2 * s : ℕ) : Fin L)) <;> simp
  have h6 : seg c (b - (s : Fin L)) (1 + 2 * s + 1) =
      seg c (b - (s : Fin L)) (1 + 2 * s) + 1 := by
    unfold seg; rw [sum_range_succ, h5]; rfl
  have h7 := seg_le_count c (b - (s : Fin L)) (1 + 2 * s + 1) (by omega)
  omega

/-- **Free-flow theorem (low density).** If at most half the cells hold robots, then from
step `n - 1` on, no robot is ever blocked and every robot moves every step. -/
theorem freeFlow_eventually (c : Config L) (n : ℕ) (hn : count c = n) (h2 : 2 * n ≤ L)
    (t : ℕ) (ht : n - 1 ≤ t) : FreeFlow (step^[t] c) ∧ flow (step^[t] c) = n := by
  have hff : FreeFlow (step^[t] c) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact freeFlow_of_count_eq_zero _ (by rw [count_iterate, hn, h0])
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
      rw [add_comm, Function.iterate_add_apply]
      exact freeFlow_iterate _ (freeFlow_at c n hn h0 h2) k
  exact ⟨hff, by rw [flow_eq_count_of_freeFlow _ hff, count_iterate, hn]⟩


/-- Particle–hole reflection: swap robots and empty cells and reverse the direction. -/
def reflect (c : Config L) : Config L := fun i => !c (-i)

/-- **Particle–hole symmetry**: reflection commutes with the dynamics. -/
theorem step_reflect (c : Config L) : step (reflect c) = reflect (step c) := by
  funext i
  simp only [step, reflect]
  have e1 : -(i + 1) = -i - 1 := by ring
  have e2 : -(i - 1) = -i + 1 := by ring
  rw [e1, e2]
  cases c (-i) <;> cases c (-i - 1) <;> cases c (-i + 1) <;> rfl

theorem iterate_reflect (c : Config L) (t : ℕ) : step^[t] (reflect c) = reflect (step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_reflect]

omit [NeZero L] in
/-- Reflection turns `n` robots into `L - n` robots. -/
theorem count_reflect (c : Config L) : count (reflect c) = L - count c := by
  have h := count_add_holes c
  have : count (reflect c) = ∑ i, (!c i).toNat := by
    unfold count reflect
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  omega

/-- Reflection preserves throughput (each robot–hole swap is counted once either way). -/
theorem flow_reflect (c : Config L) : flow (reflect c) = flow c := by
  unfold flow
  have hinv : Function.Involutive (fun i : Fin L => -i - 1) := fun i => by ring
  refine Fintype.sum_bijective _ hinv.bijective _ _ (fun i => ?_)
  unfold moves reflect
  have e1 : -(i + 1) = -i - 1 := by ring
  have e3 : -i - 1 + 1 = -i := by ring
  rw [e1, e3]
  cases c (-i) <;> cases c (-i - 1) <;> rfl

/-- **Jammed regime.** If at least half the cells hold robots, then from step `L - n - 1` on,
exactly `L - n` robots move every step (every empty cell is refilled every step). -/
theorem jammed_eventually (c : Config L) (n : ℕ) (hn : count c = n) (hnL : n ≤ L)
    (h2 : L ≤ 2 * n) (t : ℕ) (ht : L - n - 1 ≤ t) : flow (step^[t] c) = L - n := by
  have hr : count (reflect c) = L - n := by rw [count_reflect, hn]
  obtain ⟨_, hf⟩ := freeFlow_eventually (reflect c) (L - n) hr (by omega) t ht
  rwa [iterate_reflect, flow_reflect] at hf

/-- **Throughput ceiling.** In any configuration, at most `min n (L - n)` robots move. -/
theorem flow_le_min (c : Config L) : flow c ≤ min (count c) (L - count c) := by
  have := flow_le_count c
  have := flow_add_count_le c
  omega

/-- **Cumulative throughput ceiling** over any horizon `T`. -/
theorem total_flow_le (c : Config L) (T : ℕ) :
    ∑ t ∈ range T, flow (step^[t] c) ≤ T * min (count c) (L - count c) := by
  calc ∑ t ∈ range T, flow (step^[t] c) ≤ ∑ _t ∈ range T, min (count c) (L - count c) :=
        sum_le_sum fun t _ => by simpa [count_iterate] using flow_le_min (step^[t] c)
    _ = T * min (count c) (L - count c) := by simp

/-- **Fundamental diagram.** After at most `min n (L-n) - 1` steps the throughput is exactly
`min n (L - n)`, which is also the maximum possible at any step. -/
theorem eventual_flow (c : Config L) (n : ℕ) (hn : count c = n) (t : ℕ)
    (ht : min n (L - n) - 1 ≤ t) : flow (step^[t] c) = min n (L - n) := by
  have hnL : n ≤ L := by
    rw [← hn]; have := count_add_holes c; omega
  rcases le_total (2 * n) L with h | h
  · rw [(freeFlow_eventually c n hn h t (by omega)).2]; omega
  · rw [jammed_eventually c n hn hnL h t (by omega)]; omega

/-! ### Collision-freeness -/

/-- Where the robot in cell `i` ends up after the step. -/
def dest (c : Config L) (i : Fin L) : Fin L := if moves c i then i + 1 else i

omit [NeZero L] in
/-- `count` is the cardinality of the `Finset` of occupied cells. -/
theorem count_eq_card (c : Config L) : count c = (univ.filter fun i => c i = true).card := by
  rw [card_filter]; unfold count; congr 1; funext i; cases c i <;> rfl

/-- **No collisions**: two distinct robots never end up in the same cell. -/
theorem dest_injective (c : Config L) {i j : Fin L} (hi : c i = true) (hj : c j = true)
    (h : dest c i = dest c j) : i = j := by
  unfold dest moves at h
  by_cases mi : c (i + 1) = true <;> by_cases mj : c (j + 1) = true <;>
    simp_all

/-- The occupied cells after a step are exactly the destinations of the robots. -/
theorem step_eq_true_iff (c : Config L) (j : Fin L) :
    step c j = true ↔ ∃ i, c i = true ∧ dest c i = j := by
  constructor
  · intro h
    unfold step at h
    by_cases hj : c j = true
    · refine ⟨j, hj, ?_⟩
      unfold dest moves; simp_all
    · refine ⟨j - 1, by simp_all, ?_⟩
      unfold dest moves; simp_all
  · rintro ⟨i, hi, rfl⟩
    unfold dest moves step
    by_cases m : c (i + 1) = true <;> simp_all

/-! ### Fleet-size corollaries -/

/-- A completely full loop has zero throughput. -/
theorem flow_eq_zero_of_full (c : Config L) (h : count c = L) : flow c = 0 := by
  have := flow_le_min c; omega

omit [NeZero L] in
/-- The steady-state throughput `min n (L - n)` never exceeds `L / 2`, attained at `n = L / 2`. -/
theorem min_le_half (n : ℕ) : min n (L - n) ≤ L / 2 ∧ min (L / 2) (L - L / 2) = L / 2 := by
  omega

omit [NeZero L] in
/-- **Marginal gain.** For `k ≤ L/2` the `k`-th robot adds exactly one unit of throughput. -/
theorem marginal_gain (k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ L) :
    min k (L - k) = min (k - 1) (L - (k - 1)) + 1 := by omega

omit [NeZero L] in
/-- **Plateau (odd `L` only).** The robot number `k = (L + 1) / 2` adds nothing. -/
theorem marginal_plateau (k : ℕ) (hk : 2 * k = L + 1) :
    min k (L - k) = min (k - 1) (L - (k - 1)) := by omega

omit [NeZero L] in
/-- **Marginal loss.** For `L/2 + 1 ≤ k ≤ L` the `k`-th robot removes exactly one unit. -/
theorem marginal_loss (k : ℕ) (hk : L + 2 ≤ 2 * k) (hkL : k ≤ L) :
    min (k - 1) (L - (k - 1)) = min k (L - k) + 1 := by omega

/-- Every fleet size `n ≤ L` is realizable (robots in cells `0, …, n-1`). -/
theorem exists_config (n : ℕ) (h : n ≤ L) : ∃ c : Config L, count c = n := by
  refine ⟨fun i => decide (i.val < n), ?_⟩
  unfold count
  rw [Fin.sum_univ_eq_sum_range (fun k => (decide (k < n)).toNat) L]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sum_range_add]
  have h1 : ∑ k ∈ range n, (decide (k < n)).toNat = ∑ _k ∈ range n, 1 :=
    sum_congr rfl fun k hk => by simp [mem_range.mp hk]
  have h2 : ∑ k ∈ range d, (decide (n + k < n)).toNat = 0 :=
    sum_eq_zero fun k _ => by simp
  rw [h1, h2]; simp

/-- **Fundamental diagram, managerial form.**  For a fleet of `n` robots (any start), the
long-run throughput is exactly `min n (L - n)`; it is the best possible at every step; and
going from `n - 1` to `n` robots helps iff `2n ≤ L`. -/
theorem fundamental_diagram (c : Config L) :
    (∀ t, flow (step^[t] c) ≤ min (count c) (L - count c)) ∧
    (∀ t, min (count c) (L - count c) - 1 ≤ t →
      flow (step^[t] c) = min (count c) (L - count c)) := by
  refine ⟨fun t => ?_, fun t ht => eventual_flow c _ rfl t ht⟩
  simpa [count_iterate] using flow_le_min (step^[t] c)

/-! ### Exhaustive sanity checks on a loop of 6 cells (all 64 configurations, by `decide`) -/

/-- Configuration whose occupied cells are the set bits of `k`. -/
def ofBits (L : ℕ) (k : ℕ) : Config L := fun i => k.testBit i.val

example : ∀ k : Fin 64, count (step (ofBits 6 k)) = count (ofBits 6 k) := by decide

example : ∀ k : Fin 64,
    flow (ofBits 6 k) ≤ min (count (ofBits 6 k)) (6 - count (ofBits 6 k)) := by decide

example : ∀ k : Fin 64, flow (ofBits 6 k) ≤ flow (step (ofBits 6 k)) := by decide

/-- After `min n (6 - n) - 1` steps every configuration on 6 cells is at its steady throughput. -/
example : ∀ k : Fin 64,
    flow (step^[min (count (ofBits 6 k)) (6 - count (ofBits 6 k)) - 1] (ofBits 6 k)) =
      min (count (ofBits 6 k)) (6 - count (ofBits 6 k)) := by decide

/-- The transient bound `n - 1` is tight: `111000` needs 2 steps to reach throughput 3. -/
example : flow (ofBits 6 0b000111) = 1 ∧ flow (step (ofBits 6 0b000111)) = 2 ∧
    flow (step^[2] (ofBits 6 0b000111)) = 3 := by decide

/-- Steady throughput on 6 cells as fleet size goes 0,1,…,6: rises to 3 at n = 3, then falls. -/
example : (List.range 7).map (fun n => min n (6 - n)) = [0, 1, 2, 3, 2, 1, 0] := by decide

end RoboLean.FleetThroughput
