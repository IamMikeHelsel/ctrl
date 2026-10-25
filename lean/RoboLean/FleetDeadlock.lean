import Mathlib

/-!
# Fleet-management threshold theorem

**Plain-English statement (for engineers).**
Model a warehouse/factory roadmap as a finite *directed* graph of cells (a lane segment
`u → v` means a robot may drive from cell `u` to cell `v`; a two-way aisle is a pair of
opposite edges). Each robot occupies one cell, at most one robot per cell. Every robot has
its own route planner that, at each moment, names some adjacent "next cell" it wants --
arbitrary, selfish, uncoordinated. The only traffic rule is the trivial local one:

> *a robot may advance iff the cell it wants is currently empty.*

Then:

* **Safety (`reachable_injective`).** Under one-at-a-time (asynchronous) moves, the rule
  never produces a collision, whatever the routes and whatever the move order.
* **Deadlock = circular wait on a roadmap cycle (`deadlocked_iff_blocker`,
  `deadlock_has_cycle`, `cycle_admits_deadlock`, `exists_deadlock_iff`).** A deadlock
  (nobody can move) always contains a circular wait `r₁ → r₂ → … → r_k → r₁` of robots, each
  wanting the cell of the next, whose cells form a directed cycle of `k ≤ n` distinct cells
  in the roadmap; conversely every directed cycle of `k` cells can be filled by `k` robots
  into a deadlock.
* **Main theorem (`fleet_threshold`, `fleet_never_stuck`).** If the roadmap has **no
  directed cycle of length `≤ n`** (its directed girth exceeds `n`), then a fleet of
  `n ≥ 1` robots can **never** be deadlocked: in every configuration, for every choice of
  routes, some robot can move. So *you do not need a fleet manager for deadlock avoidance
  until the fleet size reaches the directed girth of the roadmap.*
* **Tightness (`threshold_is_exact`, `two_way_edge_deadlock`).** For each `k ≥ 2` the
  one-way loop of `k` cells has no cycle shorter than `k`, and `k` robots on it deadlock.
  Any two-way aisle (a cycle of length 2) lets just **two** robots deadlock head-on: with
  bidirectional lanes you need coordination from the second robot on.
* **DAG roadmaps (`acyclic_parked`).** With no directed cycles at all, any number of robots
  is free of circular waits: if some robots are still driving, either one of them can move
  or one of them is stuck directly behind a *parked* robot (one that has stopped, e.g. at
  its goal). Parked robots are a genuine second source of blocking that this theorem does
  not remove.
* **One-way loop (`ring_*`).** On a one-way loop of `L` cells with `1 ≤ n < L` robots some
  robot can always move; under the synchronous "rule 184" update (every robot whose next
  cell is empty advances, all at once) the update is collision-free, makes progress every
  tick, and in fact **every** robot advances at least once in every window of `n`
  consecutive ticks (`ring_sync_window`). With `n = L` nobody can ever move.

**Exact hypotheses / honest limitations of the model.**
1. Space is discretised into cells; a robot occupies exactly one cell; moves are atomic hops
   along roadmap edges. Robots spanning several cells, continuous kinematics, braking
   distances, sensing/communication errors are *not* modelled.
2. "Next cell empty" means empty *now*: a robot may not move into a cell that is being
   vacated in the same instant (conservative; this is what makes the rule safe).
3. "Deadlock" means the instantaneous condition "no robot can move" given the robots'
   current wishes. Routes are completely arbitrary and may change at every step (the main
   theorem quantifies over all routes), but the asynchronous results do **not** promise
   that every robot reaches its goal: livelock, starvation of an individual robot, and
   throughput are outside their scope. (The synchronous one-way-loop result is the
   exception: there we prove per-robot progress.)
4. Every robot that wants to move must name a roadmap-adjacent cell (`ValidRoutes`).
   Robots with no wish (parked) are handled separately in `fleet_threshold_parked`.
5. The synchronous rule is only safe when no two movable robots aim at the same cell; at a
   lane merge it collides (`sync_unsafe_at_merge`). All general-graph results therefore use
   the asynchronous (one move at a time) semantics.
-/

open Function

namespace FleetDeadlock

variable {V : Type*}

/-- `c` traces a directed cycle of exactly `k ≥ 1` distinct cells: `c 0, c 1, …, c (k-1)` are
pairwise distinct, each has a roadmap edge to the next, and the sequence repeats with period
`k` (so `c (k-1) → c 0` is also an edge). `k = 1` is a self-loop, `k = 2` a two-way edge. -/
def IsDirectedCycle (adj : V → V → Prop) (k : ℕ) (c : ℕ → V) : Prop :=
  0 < k ∧ (∀ t, c (t + k) = c t) ∧ (∀ t, adj (c t) (c (t + 1))) ∧ Set.InjOn c (Set.Iio k)

/-- The roadmap has no directed cycle of length `≤ n`, i.e. its directed girth is `> n`. -/
def NoCycleUpTo (adj : V → V → Prop) (n : ℕ) : Prop :=
  ∀ k c, k ≤ n → ¬ IsDirectedCycle adj k c

variable {n : ℕ}

/-- The trivial local rule: robot `i` may move iff no robot currently occupies the cell
`next i` it wants. -/
def CanMove (pos next : Fin n → V) (i : Fin n) : Prop := ∀ j, pos j ≠ next i
/-- Deadlock: no robot can move. -/
def Deadlocked (pos next : Fin n → V) : Prop := ∀ i, ¬ CanMove pos next i
/-- Every robot's wish is a cell adjacent (along a directed roadmap edge) to its current cell.
The routes are otherwise arbitrary (each robot's own planner, no coordination). -/
def ValidRoutes (adj : V → V → Prop) (pos next : Fin n → V) : Prop := ∀ i, adj (pos i) (next i)

/-- One asynchronous move: some robot `i` moves along a roadmap edge to a cell `v` that is
currently unoccupied. The target `v` is arbitrary, so routes may change from step to step. -/
def Step (adj : V → V → Prop) (pos pos' : Fin n → V) : Prop :=
  ∃ i v, adj (pos i) v ∧ (∀ j, pos j ≠ v) ∧ pos' = update pos i v

theorem IsDirectedCycle.periodic {adj : V → V → Prop} {k : ℕ} {c : ℕ → V}
    (hc : IsDirectedCycle adj k c) (r q : ℕ) : c (r + k * q) = c r := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hc.2.1, ih]

theorem IsDirectedCycle.mod {adj : V → V → Prop} {k : ℕ} {c : ℕ → V}
    (hc : IsDirectedCycle adj k c) (t : ℕ) : c (t % k) = c t := by
  conv_rhs => rw [← Nat.mod_add_div t k]
  rw [hc.periodic]

/-- **Safety, one step.** A legal move keeps at most one robot per cell. -/
theorem step_preserves_injective {adj : V → V → Prop} {pos pos' : Fin n → V}
    (hinj : Injective pos) (h : Step adj pos pos') : Injective pos' := by
  obtain ⟨i, v, -, hfree, rfl⟩ := h
  intro j k hjk
  by_cases hj : j = i <;> by_cases hk : k = i
  · rw [hj, hk]
  · subst hj; simp [hk] at hjk; exact absurd hjk.symm (hfree k)
  · subst hk; simp [hj] at hjk; exact absurd hjk (hfree j)
  · simp [hj, hk] at hjk; exact hinj hjk

/-- **Safety.** Starting from a collision-free configuration, any finite sequence of legal
asynchronous moves (with any, possibly changing, routes) stays collision-free. -/
theorem reachable_injective {adj : V → V → Prop} {pos pos' : Fin n → V}
    (hinj : Injective pos) (h : Relation.ReflTransGen (Step adj) pos pos') : Injective pos' := by
  classical
  induction h with
  | refl => exact hinj
  | tail _ hs ih => exact step_preserves_injective ih hs

/-- **Deadlock characterisation.** The fleet is deadlocked iff "the robot occupying my next
cell" is a well-defined function `f` on robots. -/
theorem deadlocked_iff_blocker (pos next : Fin n → V) :
    Deadlocked pos next ↔ ∃ f : Fin n → Fin n, ∀ i, pos (f i) = next i := by
  constructor
  · intro h
    have : ∀ i, ∃ j, pos j = next i := fun i => by simpa [CanMove] using h i
    choose f hf using this
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩ i hi
    exact hi (f i) (hf i)

/-- Combinatorial core: if every robot (in a finite nonempty set `ι`) has a successor robot whose
cell is roadmap-adjacent to its own, then following successors yields a directed cycle of
`k ≤ |ι|` distinct occupied cells in the roadmap. -/
theorem exists_cycle_of_successor {ι : Type*} [Fintype ι] [Nonempty ι]
    (adj : V → V → Prop) (pos : ι → V) (hinj : Injective pos) (f : ι → ι)
    (hf : ∀ i, adj (pos i) (pos (f i))) :
    ∃ k, k ≤ Fintype.card ι ∧ ∃ r : ℕ → ι,
      IsDirectedCycle adj k (pos ∘ r) ∧ ∀ t, r (t + 1) = f (r t) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have key : ∀ a b : ℕ, a < b → b ≤ Fintype.card ι → f^[a] i0 = f^[b] i0 →
      ∃ k, k ≤ Fintype.card ι ∧ ∃ r : ℕ → ι,
        IsDirectedCycle adj k (pos ∘ r) ∧ ∀ t, r (t + 1) = f (r t) := by
    intro a b hab hb he
    have hper : IsPeriodicPt f (b - a) (f^[a] i0) := by
      show f^[b - a] (f^[a] i0) = f^[a] i0
      rw [← iterate_add_apply, Nat.sub_add_cancel hab.le]; exact he.symm
    have hpos := hper.minimalPeriod_pos (by omega)
    have hle := hper.minimalPeriod_le (by omega)
    refine ⟨minimalPeriod f (f^[a] i0), by omega, fun t => f^[t] (f^[a] i0),
      ⟨hpos, ?_, ?_, ?_⟩, fun t => iterate_succ_apply' _ _ _⟩
    · intro t
      simp only [comp_apply]
      rw [iterate_add_apply, iterate_minimalPeriod]
    · intro t
      simp only [comp_apply]
      rw [iterate_succ_apply']
      exact hf _
    · exact hinj.comp_injOn iterate_injOn_Iio_minimalPeriod
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin (Fintype.card ι + 1) => f^[t] i0) (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key a b h (by omega) he
  · exact key b a h (by omega) he.symm

/-- **Deadlock ⇒ circular wait.** In a deadlock of `n ≥ 1` robots there are robots
`r 0, r 1, …` (periodic with period `k ≤ n`), each wanting the cell of the next, whose cells
form a directed cycle of `k` distinct cells in the roadmap. -/
theorem deadlock_has_cycle {adj : V → V → Prop} {pos next : Fin n → V}
    (hn : 0 < n) (hinj : Injective pos) (hval : ValidRoutes adj pos next)
    (hdead : Deadlocked pos next) :
    ∃ k, k ≤ n ∧ ∃ r : ℕ → Fin n,
      IsDirectedCycle adj k (pos ∘ r) ∧ ∀ t, next (r t) = pos (r (t + 1)) := by
  obtain ⟨f, hf⟩ := (deadlocked_iff_blocker pos next).1 hdead
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk, r, hc, hr⟩ := exists_cycle_of_successor adj pos hinj f
    (fun i => by rw [hf]; exact hval i)
  exact ⟨k, by simpa using hk, r, hc, fun t => by rw [hr, hf]⟩

/-- On a roadmap without self-loops every directed cycle has length `≥ 2` (see also
`blocker_ne_self`). -/
theorem cycle_length_ge_two {adj : V → V → Prop} (hloop : ∀ v, ¬ adj v v)
    {k : ℕ} {c : ℕ → V} (hc : IsDirectedCycle adj k c) : 2 ≤ k := by
  obtain ⟨hk, hper, hadj, -⟩ := hc
  by_contra h
  have : k = 1 := by omega
  subst this
  exact hloop (c 0) (by simpa [hper 0] using hadj 0)

/-- A directed cycle of length 2 is exactly a two-way edge between two distinct cells. -/
theorem cycle_two_iff (adj : V → V → Prop) :
    (∃ c, IsDirectedCycle adj 2 c) ↔ ∃ u v, u ≠ v ∧ adj u v ∧ adj v u := by
  constructor
  · rintro ⟨c, -, hper, hadj, hinj⟩
    refine ⟨c 0, c 1, fun h => ?_, hadj 0, ?_⟩
    · exact absurd (hinj (by simp) (by simp) h) (by norm_num)
    · simpa [hper 0] using hadj 1
  · rintro ⟨u, v, huv, h1, h2⟩
    refine ⟨fun t => if t % 2 = 0 then u else v, by norm_num, ?_, ?_, ?_⟩
    · intro t; simp [Nat.add_mod_right]
    · intro t
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · have : (t + 1) % 2 = 1 := by omega
        simp [h, this, h1]
      · have : (t + 1) % 2 = 0 := by omega
        simp [h, this, h2]
    · intro a ha b hb hab
      simp only [Set.mem_Iio] at ha hb
      interval_cases a <;> interval_cases b <;> simp_all [eq_comm]

/-- **MAIN THEOREM (fleet-management threshold).** If the roadmap has no directed cycle of
length `≤ n`, then in every collision-free configuration of `n ≥ 1` robots, whatever adjacent
next cell each robot wants, at least one robot can move. -/
theorem fleet_threshold {adj : V → V → Prop} (hgirth : NoCycleUpTo adj n)
    (hn : 0 < n) (pos next : Fin n → V) (hinj : Injective pos)
    (hval : ValidRoutes adj pos next) : ∃ i, CanMove pos next i := by
  by_contra h
  push Not at h
  obtain ⟨k, hk, r, hc, -⟩ := deadlock_has_cycle hn hinj hval h
  exact hgirth k _ hk hc


/-- In a deadlock on a roadmap without self-loops, no robot is blocked by itself. -/
theorem blocker_ne_self {adj : V → V → Prop} (hloop : ∀ v, ¬ adj v v) {pos next : Fin n → V}
    (hval : ValidRoutes adj pos next) {f : Fin n → Fin n} (hf : ∀ i, pos (f i) = next i)
    (i : Fin n) : f i ≠ i := by
  intro h
  exact hloop (pos i) (by simpa [← hf i, h] using hval i)

/-- **Never stuck.** Under the girth hypothesis, from every configuration reachable by legal
moves and for every choice of routes, some robot can follow its route, and doing so is a legal
move. -/
theorem fleet_never_stuck {adj : V → V → Prop} (hgirth : NoCycleUpTo adj n) (hn : 0 < n)
    {pos₀ pos : Fin n → V} (hinj : Injective pos₀)
    (hreach : Relation.ReflTransGen (Step adj) pos₀ pos) (next : Fin n → V)
    (hval : ValidRoutes adj pos next) :
    ∃ i, CanMove pos next i ∧ Step adj pos (update pos i (next i)) := by
  obtain ⟨i, hi⟩ := fleet_threshold hgirth hn pos next (reachable_injective hinj hreach) hval
  exact ⟨i, hi, i, next i, hval i, hi, rfl⟩

/-- **Main theorem with parked robots.** Some robots are `active` (they want an adjacent next
cell); the others are parked and want nothing. If the roadmap has no directed cycle of length
`≤ n` and some robot is active, then either an active robot can move, or some active robot's
next cell is occupied by a parked robot. (Circular waits are impossible; waiting on a parked
robot is the only remaining kind of blocking.) -/
theorem fleet_threshold_parked {adj : V → V → Prop} (hgirth : NoCycleUpTo adj n)
    (active : Fin n → Prop) (pos next : Fin n → V) (hinj : Injective pos)
    (hval : ∀ i, active i → adj (pos i) (next i)) (hact : ∃ i, active i) :
    (∃ i, active i ∧ CanMove pos next i) ∨
      (∃ i j, active i ∧ ¬ active j ∧ pos j = next i) := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ i : {i // active i}, ∃ j : {i // active i}, pos j.1 = next i.1 := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j, pos j = next i.1 := by simpa [CanMove] using h1 i.1 i.2
    by_cases hja : active j
    · exact ⟨⟨j, hja⟩, hj⟩
    · exact absurd hj (h2 i.1 j i.2 hja)
  choose f hf using hb
  obtain ⟨i0, hi0⟩ := hact
  have : Nonempty {i // active i} := ⟨⟨i0, hi0⟩⟩
  obtain ⟨k, hk, r, hc, -⟩ := exists_cycle_of_successor adj (fun i : {i // active i} => pos i.1)
    (hinj.comp Subtype.val_injective) f (fun i => by rw [hf]; exact hval i.1 i.2)
  have hcard : Fintype.card {i // active i} ≤ n := by
    simpa using Fintype.card_subtype_le (fun i : Fin n => active i)
  exact hgirth k _ (hk.trans hcard) hc

/-- **DAG roadmaps (e.g. pure one-way flow with no loops), any fleet size.** Either an active
robot can move or an active robot is waiting directly on a parked robot. -/
theorem acyclic_parked {adj : V → V → Prop} (hacyc : ∀ k c, ¬ IsDirectedCycle adj k c)
    (active : Fin n → Prop) (pos next : Fin n → V) (hinj : Injective pos)
    (hval : ∀ i, active i → adj (pos i) (next i)) (hact : ∃ i, active i) :
    (∃ i, active i ∧ CanMove pos next i) ∨
      (∃ i j, active i ∧ ¬ active j ∧ pos j = next i) :=
  fleet_threshold_parked (fun k c _ => hacyc k c) active pos next hinj hval hact

/-- **Converse.** Every directed cycle of `k` cells admits a deadlock of `k` robots (fill the
cycle, each robot wanting the next cell). -/
theorem cycle_admits_deadlock {adj : V → V → Prop} {k : ℕ} {c : ℕ → V}
    (hc : IsDirectedCycle adj k c) :
    ∃ pos next : Fin k → V, Injective pos ∧ ValidRoutes adj pos next ∧ Deadlocked pos next := by
  refine ⟨fun i => c i, fun i => c (i + 1), ?_, fun i => hc.2.2.1 i, ?_⟩
  · intro a b hab
    exact Fin.ext (hc.2.2.2 a.2 b.2 hab)
  · rw [deadlocked_iff_blocker]
    refine ⟨fun i => ⟨(i + 1) % k, Nat.mod_lt _ hc.1⟩, fun i => ?_⟩
    exact hc.mod _

/-- **Exact characterisation.** Some fleet of between 1 and `n` robots can be deadlocked on the
roadmap iff the roadmap has a directed cycle of length `≤ n`. I.e. the smallest deadlockable
fleet size equals the directed girth. -/
theorem exists_deadlock_iff (adj : V → V → Prop) (n : ℕ) :
    (∃ m, 0 < m ∧ m ≤ n ∧ ∃ pos next : Fin m → V,
        Injective pos ∧ ValidRoutes adj pos next ∧ Deadlocked pos next) ↔
      ∃ k c, k ≤ n ∧ IsDirectedCycle adj k c := by
  constructor
  · rintro ⟨m, hm, hmn, pos, next, hinj, hval, hdead⟩
    obtain ⟨k, hk, r, hc, -⟩ := deadlock_has_cycle hm hinj hval hdead
    exact ⟨k, _, hk.trans hmn, hc⟩
  · rintro ⟨k, c, hk, hc⟩
    exact ⟨k, hc.1, hk, cycle_admits_deadlock hc⟩

theorem not_noCycleUpTo_iff (adj : V → V → Prop) (n : ℕ) :
    ¬ NoCycleUpTo adj n ↔ ∃ k c, k ≤ n ∧ IsDirectedCycle adj k c := by
  simp [NoCycleUpTo]

/-- **Bidirectional lanes need coordination at n = 2.** Any two-way edge `u ⇄ v` lets two
robots deadlock head-on. -/
theorem two_way_edge_deadlock {adj : V → V → Prop} {u v : V} (huv : u ≠ v)
    (h1 : adj u v) (h2 : adj v u) :
    ∃ pos next : Fin 2 → V, Injective pos ∧ ValidRoutes adj pos next ∧ Deadlocked pos next := by
  obtain ⟨c, hc⟩ := (cycle_two_iff adj).2 ⟨u, v, huv, h1, h2⟩
  exact cycle_admits_deadlock hc

/-- If every cell is occupied (`n ≥ |V|`), no legal move exists at all. -/
theorem full_roadmap_frozen [Fintype V] {adj : V → V → Prop} {pos : Fin n → V}
    (hinj : Injective pos) (hfull : Fintype.card V ≤ n) (pos' : Fin n → V) :
    ¬ Step adj pos pos' := by
  rintro ⟨i, v, -, hfree, -⟩
  have hsurj : Surjective pos :=
    ((Fintype.bijective_iff_injective_and_card pos).2
      ⟨hinj, le_antisymm (by simpa using Fintype.card_le_of_injective pos hinj) (by simpa using hfull)⟩).2
  obtain ⟨j, hj⟩ := hsurj v
  exact hfree j hj

/-! ### Ring -/

/-- The one-way loop of `L` cells: `ZMod L` with edges `a → a + 1`. -/
def ringAdj (L : ℕ) (a b : ZMod L) : Prop := b = a + 1

theorem ring_walk {L : ℕ} {c : ℕ → ZMod L} (h : ∀ t, ringAdj L (c t) (c (t + 1))) (t : ℕ) :
    c t = c 0 + t := by
  induction t with
  | zero => simp
  | succ t ih => rw [h t, ih]; push_cast; ring

/-- The one-way loop of `L` cells has no directed cycle of length `≤ L - 1`. -/
theorem ring_noCycleUpTo (L : ℕ) : NoCycleUpTo (ringAdj L) (L - 1) := by
  intro k c hk hc
  have h := ring_walk hc.2.2.1 k
  rw [← zero_add k, hc.2.1 0, zero_add] at h
  have h0 : ((k : ℕ) : ZMod L) = 0 := by
    have := congrArg (fun x => x - c 0) h
    simpa using this.symm
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hc.1 h0
  have := hc.1
  omega

/-- The one-way loop of `L ≥ 1` cells is itself a directed cycle of length `L`. -/
theorem ring_cycle (L : ℕ) [NeZero L] :
    IsDirectedCycle (ringAdj L) L (fun t => (t : ZMod L)) := by
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne L), fun t => by simp, fun t => by simp [ringAdj], ?_⟩
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b L).1 hab
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this


/-- **Tightness.** For every `k ≥ 2` there is a roadmap (the one-way `k`-loop) with no directed
cycle of length `< k` on which `k` robots deadlock. So the threshold `n < girth` cannot be
improved. -/
theorem threshold_is_exact (k : ℕ) (hk : 2 ≤ k) :
    NoCycleUpTo (ringAdj k) (k - 1) ∧
      ∃ pos next : Fin k → ZMod k,
        Injective pos ∧ ValidRoutes (ringAdj k) pos next ∧ Deadlocked pos next := by
  have : NeZero k := ⟨by omega⟩
  exact ⟨ring_noCycleUpTo k, cycle_admits_deadlock (ring_cycle k)⟩

/-- On the one-way loop the only route is "go to the next cell" (`ring_routes_forced`). -/
def ringNext {L : ℕ} (pos : Fin n → ZMod L) : Fin n → ZMod L := fun i => pos i + 1

theorem ring_routes_forced {L : ℕ} (pos next : Fin n → ZMod L)
    (h : ValidRoutes (ringAdj L) pos next) : next = ringNext pos := funext h

/-- One-way loop, `1 ≤ n < L` robots: some robot can always move. -/
theorem ring_some_robot_moves {L : ℕ} (hn : 0 < n) (hnL : n < L) (pos : Fin n → ZMod L)
    (hinj : Injective pos) : ∃ i, CanMove pos (ringNext pos) i :=
  fleet_threshold (fun k c hk => ring_noCycleUpTo L k c (by omega)) hn pos _ hinj (fun _ => rfl)

/-- One-way loop completely full (`n = L`): deadlocked. -/
theorem ring_full_deadlocked {L : ℕ} [NeZero L] (pos : Fin L → ZMod L) (hinj : Injective pos) :
    Deadlocked pos (ringNext pos) := by
  intro i hi
  have hsurj : Surjective pos :=
    ((Fintype.bijective_iff_injective_and_card pos).2 ⟨hinj, by simp⟩).2
  obtain ⟨j, hj⟩ := hsurj (ringNext pos i)
  exact hi j hj

/-- One-way loop completely full: no asynchronous move is possible, ever. -/
theorem ring_full_frozen {L : ℕ} [NeZero L] (pos : Fin L → ZMod L) (hinj : Injective pos)
    (pos' : Fin L → ZMod L) : ¬ Step (ringAdj L) pos pos' :=
  full_roadmap_frozen hinj (by simp) pos'

section Sync

variable [DecidableEq V]

instance (pos next : Fin n → V) (i : Fin n) : Decidable (CanMove pos next i) := by
  unfold CanMove; infer_instance

/-- Synchronous update: every robot whose next cell is currently empty moves, simultaneously. -/
def syncStep (pos next : Fin n → V) : Fin n → V :=
  fun i => if CanMove pos next i then next i else pos i

/-- The synchronous update is collision-free provided no two movable robots want the same
cell. -/
theorem syncStep_injective {pos next : Fin n → V} (hinj : Injective pos)
    (hdist : ∀ i j, CanMove pos next i → CanMove pos next j → next i = next j → i = j) :
    Injective (syncStep pos next) := by
  intro i j hij
  unfold syncStep at hij
  by_cases hi : CanMove pos next i <;> by_cases hj : CanMove pos next j <;>
    simp only [hi, hj, if_true, if_false] at hij
  · exact hdist i j hi hj hij
  · exact absurd hij.symm (hi j)
  · exact absurd hij (hj i)
  · exact hinj hij

/-- **Caveat.** On a general roadmap the synchronous rule is unsafe: at a merge `0 → 2 ← 1`,
two robots that both see cell 2 empty move into it at the same time. -/
theorem sync_unsafe_at_merge :
    ∃ (adj : Fin 3 → Fin 3 → Prop) (pos next : Fin 2 → Fin 3),
      Injective pos ∧ ValidRoutes adj pos next ∧ (∀ i, CanMove pos next i) ∧
        ¬ Injective (syncStep pos next) := by
  refine ⟨fun a b => a ≠ 2 ∧ b = 2, ![0, 1], ![2, 2], ?_, ?_, ?_, ?_⟩
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro h
    exact absurd (h (a₁ := 0) (a₂ := 1) (by decide)) (by decide)

theorem ring_one_ne_zero {L : ℕ} (hL : 2 ≤ L) : (1 : ZMod L) ≠ 0 := by
  intro h
  have : ((1 : ℕ) : ZMod L) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd one_pos this
  omega

/-- On the one-way loop the synchronous rule is collision-free. -/
theorem ring_sync_injective {L : ℕ} {pos : Fin n → ZMod L} (hinj : Injective pos) :
    Injective (syncStep pos (ringNext pos)) :=
  syncStep_injective hinj (fun _ _ _ _ h => hinj (add_right_cancel h))

/-- One-way loop, `1 ≤ n < L`: every synchronous tick moves at least one robot. -/
theorem ring_sync_progress {L : ℕ} (hn : 0 < n) (hnL : n < L) (pos : Fin n → ZMod L)
    (hinj : Injective pos) : ∃ i, syncStep pos (ringNext pos) i ≠ pos i := by
  obtain ⟨i, hi⟩ := ring_some_robot_moves hn hnL pos hinj
  refine ⟨i, ?_⟩
  simp only [syncStep, hi, if_true, ringNext]
  intro h
  exact ring_one_ne_zero (L := L) (by omega) (by simpa using h)

/-- One-way loop full (`n = L`): the synchronous update does nothing. -/
theorem ring_sync_full_frozen {L : ℕ} [NeZero L] (pos : Fin L → ZMod L) (hinj : Injective pos) :
    syncStep pos (ringNext pos) = pos := by
  funext i
  simp [syncStep, ring_full_deadlocked pos hinj i]


/-- One synchronous tick on the one-way loop. -/
def ringSync {L : ℕ} (pos : Fin n → ZMod L) : Fin n → ZMod L := syncStep pos (ringNext pos)

theorem ringSync_iterate_injective {L : ℕ} {pos : Fin n → ZMod L} (hinj : Injective pos)
    (t : ℕ) : Injective (ringSync^[t] pos) := by
  induction t with
  | zero => exact hinj
  | succ t ih => rw [iterate_succ_apply']; exact ring_sync_injective ih

theorem ringSync_blocked {L : ℕ} {pos : Fin n → ZMod L} {i : Fin n}
    (hi : ¬ CanMove pos (ringNext pos) i) : ringSync pos i = pos i := by
  simp [ringSync, syncStep, hi]

theorem ringSync_vacate {L : ℕ} {pos : Fin n → ZMod L} (hinj : Injective pos) {j : Fin n}
    {y : ZMod L} (hj : pos j = y) (hfree : ∀ k, pos k ≠ y + 1) (k : Fin n) :
    ringSync pos k ≠ y := by
  by_cases hk : CanMove pos (ringNext pos) k
  · simp only [ringSync, syncStep, hk, if_true, ringNext]
    intro h
    exact hk j (by rw [hj, ringNext, h])
  · rw [ringSync_blocked hk]
    intro h
    have hkj : k = j := hinj (h.trans hj.symm)
    subst hkj
    exact hk (fun k' => by rw [ringNext, h]; exact hfree k')

/-- If the cell `m ≥ 1` positions ahead of robot `i` is empty, robot `i` gets to move within
`m` synchronous ticks (a jam ahead dissolves from the front, one robot per tick). -/
theorem ring_wait_bound {L : ℕ} (m : ℕ) : ∀ (pos : Fin n → ZMod L), Injective pos →
    ∀ i, 1 ≤ m → (∀ k, pos k ≠ pos i + m) →
      ∃ t < m, CanMove (ringSync^[t] pos) (ringNext (ringSync^[t] pos)) i := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro pos hinj i hm hfree
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · have : m = 1 := by omega
    subst this
    exact ⟨0, one_pos, fun k => by simpa [ringNext] using hfree k⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  by_cases hprev : ∀ k, pos k ≠ pos i + ((m + 1 : ℕ) : ZMod L)
  · obtain ⟨t, ht, hc⟩ := ih (m + 1) (by omega) pos hinj i (by omega) hprev
    exact ⟨t, by omega, hc⟩
  push Not at hprev
  obtain ⟨j, hj⟩ := hprev
  by_cases hi : CanMove pos (ringNext pos) i
  · exact ⟨0, by omega, hi⟩
  have hstay := ringSync_blocked hi
  have hvac := ringSync_vacate hinj hj (fun k => by
    have := hfree k; push_cast at this ⊢; rwa [add_assoc, show (m : ZMod L) + 1 + 1 = m + 2 by ring])
  obtain ⟨t, ht, hc⟩ := ih (m + 1) (by omega) (ringSync pos) (ring_sync_injective hinj) i
    (by omega) (fun k => by rw [hstay]; exact hvac k)
  exact ⟨t + 1, by omega, by rw [iterate_succ_apply]; exact hc⟩

/-- With `n < L`, among the `n` cells directly ahead of any robot at least one is empty. -/
theorem ring_free_ahead {L : ℕ} (hnL : n < L) (pos : Fin n → ZMod L) (i : Fin n) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ ∀ k, pos k ≠ pos i + m := by
  by_contra h
  push Not at h
  have hall : ∀ m : Fin (n + 1), ∃ k, pos k = pos i + (m : ℕ) := by
    intro m
    rcases Nat.eq_zero_or_pos (m : ℕ) with h0 | h0
    · exact ⟨i, by simp [h0]⟩
    · exact h m h0 (by omega)
  choose g hg using hall
  have ginj : Injective g := by
    intro a b hab
    have h1 : ((a : ℕ) : ZMod L) = ((b : ℕ) : ZMod L) := by
      have := (hg a).symm.trans ((congrArg pos hab).trans (hg b))
      exact add_left_cancel this
    have := (ZMod.natCast_eq_natCast_iff' a b L).1 h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this
  have := Fintype.card_le_of_injective g ginj
  simp at this

/-- **Per-robot progress (one-way loop, synchronous).** With `n < L`, every robot moves within
the first `n` ticks. -/
theorem ring_sync_every_robot_moves {L : ℕ} (hnL : n < L) (pos : Fin n → ZMod L)
    (hinj : Injective pos) (i : Fin n) :
    ∃ t < n, ringSync^[t + 1] pos i ≠ ringSync^[t] pos i := by
  obtain ⟨m, hm1, hmn, hfree⟩ := ring_free_ahead hnL pos i
  obtain ⟨t, ht, hc⟩ := ring_wait_bound m pos hinj i hm1 hfree
  refine ⟨t, by omega, ?_⟩
  rw [iterate_succ_apply']
  simp only [ringSync, syncStep, hc, if_true, ringNext]
  intro h
  have : 2 ≤ L := by have := i.pos; omega
  exact ring_one_ne_zero this (by simpa using h)

/-- **Per-robot progress, every window.** With `n < L`, every robot moves at least once in
every window of `n` consecutive synchronous ticks. -/
theorem ring_sync_window {L : ℕ} (hnL : n < L) (pos : Fin n → ZMod L)
    (hinj : Injective pos) (s : ℕ) (i : Fin n) :
    ∃ t, s ≤ t ∧ t < s + n ∧ ringSync^[t + 1] pos i ≠ ringSync^[t] pos i := by
  obtain ⟨t, ht, h⟩ := ring_sync_every_robot_moves hnL (ringSync^[s] pos)
    (ringSync_iterate_injective hinj s) i
  refine ⟨t + s, by omega, by omega, ?_⟩
  rw [← iterate_add_apply, ← iterate_add_apply] at h
  rwa [show t + 1 + s = t + s + 1 by omega] at h

end Sync

end FleetDeadlock
