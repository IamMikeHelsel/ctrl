import Mathlib

/-!
# Robot search and path planning

1. **Cow path / linear search.** A robot at `0 ∈ ℝ` looks for a target at an unknown point
   `x` with `|x| ≥ 1`. The geometric strategy with ratio `r > 1` makes excursions
   `0 → (-r)^0 → 0 → (-r)^1 → 0 → (-r)^2 → …`. We model the first-hit cost honestly and prove
   it is at most `(1 + 2r²/(r-1)) |x|`, so at most `9 |x|` for the doubling strategy `r = 2`.
2. **Optimality of doubling among geometric strategies.** The worst-case ratio of the
   geometric strategy is exactly `1 + 2r²/(r-1)` (least upper bound), which is `≥ 9` with
   equality iff `r = 2`.
3. **Heuristic search.** On a digraph with edge costs `w : V → V → ℝ≥0∞`, a consistent
   heuristic is admissible, and `f = g + h` is nondecreasing along walks (A\* monotonicity).
4. **Bellman optimality.** The shortest-path distance satisfies `d g = 0`,
   `d u = ⨅ v, w u v + d v` (`u ≠ g`, also as a `Finset.inf` on finite `V`), and is the greatest
   consistent function.
5. **Grid navigation.** On `ℤ²` with 4-connected unit moves, Manhattan distance is consistent,
   admissible, and equal to the true shortest-path distance.
-/

noncomputable section

open Finset

namespace RoboLean.Search

/-! ## 1–2. The cow path problem -/

namespace CowPath

/-- The `i`-th turn point of the geometric strategy with ratio `r`: `(-r)^i`, alternating
sides of the origin with geometrically growing distance. -/
def turnPoint (r : ℝ) (i : ℕ) : ℝ := (-r) ^ i

/-- During excursion `i` the robot walks from `0` out to `turnPoint r i` and back, so it
visits exactly the points of the segment between `0` and `turnPoint r i`. -/
def Reaches (r : ℝ) (i : ℕ) (x : ℝ) : Prop := x ∈ Set.uIcc 0 (turnPoint r i)

/-- Index of the first excursion that visits `x` (`0` by convention if none does). -/
def firstHit (r x : ℝ) : ℕ := sInf {i | Reaches r i x}

/-- Length of the full round trip `0 → turnPoint r i → 0`. -/
def excursionLength (r : ℝ) (i : ℕ) : ℝ := 2 * |turnPoint r i|

/-- Total distance the robot travels before it first stands on `x`: all completed excursions
before the first one that visits `x`, plus the outward distance `|x|` of that excursion. -/
def cost (r x : ℝ) : ℝ := ∑ i ∈ range (firstHit r x), excursionLength r i + |x|

/-- The competitive ratio `1 + 2r²/(r-1)` of the geometric strategy. -/
def ratio (r : ℝ) : ℝ := 1 + 2 * r ^ 2 / (r - 1)

lemma excursionLength_eq {r : ℝ} (hr : 0 ≤ r) (i : ℕ) : excursionLength r i = 2 * r ^ i := by
  simp [excursionLength, turnPoint, abs_pow, abs_of_nonneg hr]

/-- Explicit description of `Reaches`: excursion `i` covers `[0, r^i]` for even `i` and
`[-r^i, 0]` for odd `i`. -/
lemma reaches_iff {r : ℝ} (hr : 0 ≤ r) (i : ℕ) (x : ℝ) :
    Reaches r i x ↔ (Even i ∧ 0 ≤ x ∧ x ≤ r ^ i) ∨ (Odd i ∧ -r ^ i ≤ x ∧ x ≤ 0) := by
  have hp : 0 ≤ r ^ i := pow_nonneg hr i
  rcases Nat.even_or_odd i with he | ho
  · have hn : ¬ Odd i := Nat.not_odd_iff_even.mpr he
    simp only [Reaches, turnPoint, he.neg_pow, Set.uIcc_of_le hp, Set.mem_Icc]
    tauto
  · have hn : ¬ Even i := Nat.not_even_iff_odd.mpr ho
    simp only [Reaches, turnPoint, ho.neg_pow, Set.uIcc_of_ge (neg_nonpos.mpr hp),
      Set.mem_Icc]
    tauto

/-- Excursions `k` and `k + 2` are on the same side; if `k + 2` reaches `x` but `k` does not,
then `x` lies strictly beyond `r^k`. -/
lemma lt_abs_of_reaches_add_two {r : ℝ} (hr : 0 ≤ r) {k : ℕ} {x : ℝ}
    (h2 : Reaches r (k + 2) x) (h0 : ¬ Reaches r k x) : r ^ k < |x| := by
  rw [reaches_iff hr] at h2 h0
  have e : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
  have o : Odd (k + 2) ↔ Odd k := by simp [Nat.odd_add]
  rw [e, o] at h2
  rcases h2 with ⟨he, h1, -⟩ | ⟨ho, -, h1⟩
  · rw [abs_of_nonneg h1]; by_contra H; exact h0 (Or.inl ⟨he, h1, not_lt.mp H⟩)
  · rw [abs_of_nonpos h1]; by_contra H
    exact h0 (Or.inr ⟨ho, by linarith [not_lt.mp H], h1⟩)

/-- For `r > 1` every point is eventually visited. -/
lemma exists_reaches {r : ℝ} (hr : 1 < r) (x : ℝ) : ∃ i, Reaches r i x := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt |x| hr
  have h1 : r ^ n ≤ r ^ (2 * n) := pow_le_pow_right₀ hr.le (by omega)
  have h2 : r ^ n ≤ r ^ (2 * n + 1) := pow_le_pow_right₀ hr.le (by omega)
  rcases le_total 0 x with hx | hx
  · refine ⟨2 * n, (reaches_iff (by linarith) _ _).mpr (Or.inl ⟨even_two_mul n, hx, ?_⟩)⟩
    rw [abs_of_nonneg hx] at hn; linarith
  · refine ⟨2 * n + 1, (reaches_iff (by linarith) _ _).mpr
      (Or.inr ⟨odd_two_mul_add_one n, ?_, hx⟩)⟩
    rw [abs_of_nonpos hx] at hn; linarith

lemma reaches_firstHit {r : ℝ} (hr : 1 < r) (x : ℝ) : Reaches r (firstHit r x) x :=
  Nat.sInf_mem (exists_reaches hr x)

/-- No excursion before `firstHit r x` visits `x`. -/
lemma not_reaches_of_lt_firstHit {r x : ℝ} {i : ℕ} (hi : i < firstHit r x) :
    ¬ Reaches r i x :=
  Nat.notMem_of_lt_sInf hi

lemma firstHit_le {r x : ℝ} {i : ℕ} (hi : Reaches r i x) : firstHit r x ≤ i :=
  Nat.sInf_le hi

/-- Closed form of the cost: `2 · Σ_{i<j} r^i + |x|` where `j = firstHit r x`. -/
lemma cost_eq {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    cost r x = 2 * ∑ i ∈ range (firstHit r x), r ^ i + |x| := by
  simp [cost, excursionLength_eq hr, mul_sum]

/-- **Upper bound for the geometric strategy.** For `r > 1` and `|x| ≥ 1`, the robot reaches
`x` after travelling at most `(1 + 2r²/(r-1)) |x|`. -/
theorem cost_le_ratio_mul {r x : ℝ} (hr : 1 < r) (hx : 1 ≤ |x|) :
    cost r x ≤ ratio r * |x| := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hA : 2 ≤ 2 * r ^ 2 / (r - 1) := by
    rw [le_div_iff₀ hr1]; nlinarith
  have hA0 : 0 ≤ 2 * r ^ 2 / (r - 1) := by linarith
  rw [cost_eq hr0, ratio]
  have hj := reaches_firstHit hr x
  rcases h : firstHit r x with _ | _ | k
  · simp; nlinarith
  · simp; nlinarith
  · rw [h] at hj
    have hk : r ^ k < |x| :=
      lt_abs_of_reaches_add_two hr0 hj (not_reaches_of_lt_firstHit (by omega))
    have hs : (∑ i ∈ range (k + 2), r ^ i) * (r - 1) = r ^ (k + 2) - 1 := geom_sum_mul r _
    have hs' : 2 * ∑ i ∈ range (k + 2), r ^ i ≤ 2 * r ^ 2 / (r - 1) * r ^ k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr1]
      nlinarith [pow_succ r k, pow_succ r (k + 1)]
    nlinarith

/-- **Cow path, doubling strategy.** With turn points `(-2)^i`, the distance travelled before
first reaching any target `x` with `|x| ≥ 1` is at most `9 |x|`. -/
theorem doubling_cost_le (x : ℝ) (hx : 1 ≤ |x|) : cost 2 x ≤ 9 * |x| := by
  have := cost_le_ratio_mul (r := 2) (by norm_num) hx
  norm_num [ratio] at this
  linarith

/-- Concrete form for the doubling strategy: cost is `2 · Σ_{i<j} 2^i + |x|`, where `j` is the
least index whose excursion covers `x`, i.e. the least `j` with `2^j ≥ |x|` on `x`'s side. -/
lemma doubling_cost_eq (x : ℝ) :
    cost 2 x = 2 * ∑ i ∈ range (firstHit 2 x), (2 : ℝ) ^ i + |x| :=
  cost_eq (by norm_num) x

/-- If `x > r^(2m)` then no excursion with index `< 2m + 2` visits `x`: the even ones stop
short of `x`, the odd ones go the other way. -/
lemma le_firstHit {r x : ℝ} (hr : 1 < r) (m : ℕ) (hx : r ^ (2 * m) < x) :
    2 * m + 2 ≤ firstHit r x := by
  by_contra H
  push Not at H
  have hrx := reaches_firstHit hr x
  rw [reaches_iff (by linarith)] at hrx
  have hxpos : 0 < x := lt_of_le_of_lt (pow_nonneg (by linarith) _) hx
  rcases hrx with ⟨he, -, hle⟩ | ⟨-, -, hle⟩
  · obtain ⟨t, ht⟩ := he
    have : r ^ firstHit r x ≤ r ^ (2 * m) := pow_le_pow_right₀ hr.le (by omega)
    linarith
  · linarith

/-- Lower bound on the cost from a lower bound on the first-hit index (excursion lengths are
nonnegative). -/
lemma cost_ge_of_le_firstHit {r x : ℝ} (hr : 0 ≤ r) {j : ℕ} (hj : j ≤ firstHit r x) :
    2 * ∑ i ∈ range j, r ^ i + |x| ≤ cost r x := by
  rw [cost_eq hr]
  have := sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hj)
    (f := fun i => r ^ i) (fun i _ _ => pow_nonneg hr i)
  linarith

/-- **Tightness.** For every `r > 1` and `ε > 0` there is a target `x` with `|x| ≥ 1` (just
beyond a turn point `r^(2m)`) whose cost is at least `(ratio r - ε) |x|`. -/
theorem exists_cost_ge {r : ℝ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, 1 ≤ |x| ∧ (ratio r - ε) * |x| ≤ cost r x := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  set A := 2 * r ^ 2 / (r - 1) with hAdef
  have hA : 0 < A := by positivity
  have hAr : A * (r - 1) = 2 * r ^ 2 := by rw [hAdef]; field_simp
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 / (r - 1) + 1) / ε) hr
  have hn2 : r ^ n ≤ r ^ (2 * n) := pow_le_pow_right₀ hr.le (by omega)
  set P := r ^ (2 * n) with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hr.le
  have hPε : 2 / (r - 1) + 1 ≤ ε * P := by
    rw [div_lt_iff₀ hε] at hn; nlinarith
  have h2 : 2 / (r - 1) * (r - 1) = 2 := by field_simp
  refine ⟨P + 1 / A, ?_, ?_⟩
  · rw [abs_of_pos (by positivity)]; have : 0 < 1 / A := by positivity
    linarith
  · have hxP : P < P + 1 / A := by have : 0 < 1 / A := by positivity
                                   linarith
    have hc := cost_ge_of_le_firstHit hr0 (le_firstHit hr n hxP)
    have hs : (∑ i ∈ range (2 * n + 2), r ^ i) * (r - 1) = r ^ (2 * n + 2) - 1 :=
      geom_sum_mul r _
    have hpow : r ^ (2 * n + 2) = P * r ^ 2 := by rw [hP, pow_add]
    -- `Σ = A P - 2/(r-1)`, divided out by `r - 1`
    have hsum : ∑ i ∈ range (2 * n + 2), r ^ i = A * P / 2 - 1 / (r - 1) := by
      field_simp
      rw [hAdef]; field_simp
      nlinarith [hs, hpow]
    rw [hsum, abs_of_pos (by positivity)] at hc
    rw [abs_of_pos (by positivity), ratio, ← hAdef]
    have hAinv : A * (1 / A) = 1 := by field_simp
    have h1r : 2 * (1 / (r - 1)) = 2 / (r - 1) := by ring
    nlinarith [mul_pos hε (show 0 < 1 / A by positivity)]

/-- **The worst-case ratio of the geometric strategy is exactly `1 + 2r²/(r-1)`**: it is the
least upper bound of `cost r x / |x|` over all targets with `|x| ≥ 1`. -/
theorem isLUB_ratio {r : ℝ} (hr : 1 < r) :
    IsLUB {c | ∃ x : ℝ, 1 ≤ |x| ∧ c = cost r x / |x|} (ratio r) := by
  constructor
  · rintro c ⟨x, hx, rfl⟩
    rw [div_le_iff₀ (by linarith)]
    exact cost_le_ratio_mul hr hx
  · intro b hb
    by_contra H
    push Not at H
    obtain ⟨x, hx, hc⟩ := exists_cost_ge hr (ε := (ratio r - b) / 2) (by linarith)
    have := hb ⟨x, hx, rfl⟩
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith

/-- **Doubling is optimal among geometric strategies (the algebra).** For `r > 1`,
`1 + 2r²/(r-1) ≥ 9`. -/
theorem nine_le_ratio {r : ℝ} (hr : 1 < r) : 9 ≤ ratio r := by
  have hr1 : 0 < r - 1 := by linarith
  have : 8 ≤ 2 * r ^ 2 / (r - 1) := by
    rw [le_div_iff₀ hr1]; nlinarith [sq_nonneg (r - 2)]
  unfold ratio; linarith

/-- Equality case: `1 + 2r²/(r-1) = 9` iff `r = 2`. -/
theorem ratio_eq_nine_iff {r : ℝ} (hr : 1 < r) : ratio r = 9 ↔ r = 2 := by
  have hr1 : r - 1 ≠ 0 := by intro h; linarith
  constructor
  · intro h
    unfold ratio at h
    have : 2 * r ^ 2 = 8 * (r - 1) := by
      field_simp at h; linarith
    nlinarith [sq_nonneg (r - 2)]
  · rintro rfl; norm_num [ratio]

/-- The doubling strategy's worst-case ratio is exactly `9`. -/
theorem isLUB_doubling : IsLUB {c | ∃ x : ℝ, 1 ≤ |x| ∧ c = cost 2 x / |x|} 9 := by
  have h := isLUB_ratio (r := 2) (by norm_num)
  have : ratio 2 = 9 := by norm_num [ratio]
  rwa [this] at h

/-- **No geometric strategy beats 9.** For every ratio `r > 1` and every `ε > 0` there is a
target `x`, `|x| ≥ 1`, that costs the geometric strategy at least `(9 - ε)|x|`. -/
theorem no_geometric_beats_nine {r : ℝ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, 1 ≤ |x| ∧ (9 - ε) * |x| ≤ cost r x := by
  obtain ⟨x, hx, hc⟩ := exists_cost_ge hr hε
  refine ⟨x, hx, le_trans ?_ hc⟩
  have := nine_le_ratio hr
  nlinarith

end CowPath

/-! ## 3–4. Heuristic search and Bellman optimality

Edge costs are a plain function `w : V → V → ℝ≥0∞` (a missing edge has cost `⊤`). -/

namespace WGraph

open scoped ENNReal

variable {V : Type*}

/-- A walk in the complete digraph on `V`, from `u` to `v`. -/
inductive Walk : V → V → Type _
  | nil (u : V) : Walk u u
  | cons (u : V) {v t : V} (p : Walk v t) : Walk u t

namespace Walk

/-- Cost of a walk: the sum of its edge costs. -/
def cost (w : V → V → ℝ≥0∞) : {u t : V} → Walk u t → ℝ≥0∞
  | _, _, nil _ => 0
  | _, _, @cons _ u v _ p => w u v + cost w p

/-- Concatenation of walks. -/
def append : {u v t : V} → Walk u v → Walk v t → Walk u t
  | _, _, _, nil _, q => q
  | _, _, _, cons u p, q => cons u (append p q)

@[simp] lemma cost_nil (w : V → V → ℝ≥0∞) (u : V) : (nil u).cost w = 0 := rfl

@[simp] lemma cost_cons (w : V → V → ℝ≥0∞) (u : V) {v t : V} (p : Walk v t) :
    (cons u p).cost w = w u v + p.cost w := rfl

lemma cost_append (w : V → V → ℝ≥0∞) {u v t : V} (p : Walk u v) (q : Walk v t) :
    (p.append q).cost w = p.cost w + q.cost w := by
  induction p with
  | nil => simp [append]
  | cons u p ih => simp [append, ih, add_assoc]

end Walk

/-- A heuristic `h` is *consistent* (monotone) for goal `g` if `h g = 0` and
`h u ≤ w u v + h v` for every edge. -/
def Consistent (w : V → V → ℝ≥0∞) (g : V) (h : V → ℝ≥0∞) : Prop :=
  h g = 0 ∧ ∀ u v, h u ≤ w u v + h v

/-- Shortest-path distance to the goal: infimum of the costs of all walks to `g`. -/
def dist (w : V → V → ℝ≥0∞) (g : V) (u : V) : ℝ≥0∞ := ⨅ p : Walk u g, p.cost w

/-- A heuristic is *admissible* if it never overestimates the true distance. -/
def Admissible (w : V → V → ℝ≥0∞) (g : V) (h : V → ℝ≥0∞) : Prop := ∀ u, h u ≤ dist w g u

/-- Telescoping consistency along a walk: `h u ≤ cost p + h t`. -/
lemma le_cost_add {w : V → V → ℝ≥0∞} {h : V → ℝ≥0∞} (hc : ∀ u v, h u ≤ w u v + h v)
    {u t : V} (p : Walk u t) : h u ≤ p.cost w + h t := by
  induction p with
  | nil => simp
  | @cons u v t p ih =>
    simp only [Walk.cost_cons]
    calc h u ≤ w u v + h v := hc u v
      _ ≤ w u v + (p.cost w + h t) := by gcongr
      _ = _ := by rw [add_assoc]

/-- **Consistent ⇒ admissible**, path form: a consistent heuristic is bounded by the cost of
every walk to the goal. -/
lemma Consistent.le_cost {w : V → V → ℝ≥0∞} {g : V} {h : V → ℝ≥0∞} (hc : Consistent w g h)
    {u : V} (p : Walk u g) : h u ≤ p.cost w := by
  simpa [hc.1] using le_cost_add hc.2 p

/-- **Consistent ⇒ admissible**: `h u ≤ dist w g u` for all `u`. -/
theorem Consistent.admissible {w : V → V → ℝ≥0∞} {g : V} {h : V → ℝ≥0∞}
    (hc : Consistent w g h) : Admissible w g h :=
  fun _ => le_iInf fun p => hc.le_cost p

/-- **`f = g + h` is nondecreasing along any walk (A\* monotonicity).** If the search has
reached `v` along `p` (so `g(v) = cost p`) and then continues along `q` to `t`, the
`f`-value `cost p + h v` at `v` is at most the `f`-value `cost (p ++ q) + h t` at `t`. -/
theorem f_monotone {w : V → V → ℝ≥0∞} {h : V → ℝ≥0∞} (hc : ∀ u v, h u ≤ w u v + h v)
    {s v t : V} (p : Walk s v) (q : Walk v t) :
    p.cost w + h v ≤ (p.append q).cost w + h t := by
  rw [Walk.cost_append, add_assoc]
  gcongr
  exact le_cost_add hc q

/-- One-edge form of A\* monotonicity: `g u + h u ≤ (g u + w u v) + h v`. -/
theorem f_le_succ {w : V → V → ℝ≥0∞} {h : V → ℝ≥0∞} (hc : ∀ u v, h u ≤ w u v + h v)
    (gu : ℝ≥0∞) (u v : V) : gu + h u ≤ (gu + w u v) + h v := by
  rw [add_assoc]; gcongr; exact hc u v

/-- Bellman: the goal is at distance `0`. -/
@[simp] theorem dist_self (w : V → V → ℝ≥0∞) (g : V) : dist w g g = 0 :=
  le_antisymm (iInf_le_of_le (Walk.nil g) (by simp)) bot_le

/-- Bellman inequality: `dist u ≤ w u v + dist v` (prepend the edge `u → v`). -/
theorem dist_le_add (w : V → V → ℝ≥0∞) (g u v : V) : dist w g u ≤ w u v + dist w g v := by
  rw [dist, dist, ENNReal.add_iInf]
  exact le_iInf fun p => iInf_le_of_le (Walk.cons u p) le_rfl

/-- The distance is itself a consistent heuristic. -/
theorem consistent_dist (w : V → V → ℝ≥0∞) (g : V) : Consistent w g (dist w g) :=
  ⟨dist_self w g, dist_le_add w g⟩

/-- **Bellman optimality equation** (off the goal): `d u = ⨅ v, w u v + d v` for `u ≠ g`. -/
theorem dist_eq_iInf (w : V → V → ℝ≥0∞) (g : V) {u : V} (hu : u ≠ g) :
    dist w g u = ⨅ v, (w u v + dist w g v) := by
  refine le_antisymm (le_iInf fun v => dist_le_add w g u v) ?_
  refine le_iInf fun p => ?_
  cases p with
  | nil => exact absurd rfl hu
  | @cons _ v _ q =>
    simp only [Walk.cost_cons]
    exact iInf_le_of_le v (by gcongr; exact iInf_le _ q)

/-- **Bellman optimality, finite graph (Finset form).** On a finite vertex set, for `u ≠ g`,
`d u = min_{v ∈ V} (w u v + d v)`. -/
theorem dist_eq_finset_inf [Fintype V] (w : V → V → ℝ≥0∞) (g : V) {u : V} (hu : u ≠ g) :
    dist w g u = Finset.univ.inf (fun v => w u v + dist w g v) := by
  rw [dist_eq_iInf w g hu, Finset.inf_univ_eq_iInf]

/-- **`dist` is the greatest consistent function.** Among all `h` with `h g = 0` and
`h u ≤ w u v + h v`, the shortest-path distance is the greatest. -/
theorem isGreatest_dist (w : V → V → ℝ≥0∞) (g : V) :
    IsGreatest {h | Consistent w g h} (dist w g) :=
  ⟨consistent_dist w g, fun _ hh u => Consistent.admissible hh u⟩

end WGraph

/-! ## 5. Grid navigation on `ℤ²` -/

namespace Grid

open scoped ENNReal
open WGraph

/-- Two grid cells are 4-adjacent if they differ by a unit step in exactly one coordinate. -/
def Adj (u v : ℤ × ℤ) : Prop := (u.1 - v.1).natAbs + (u.2 - v.2).natAbs = 1

instance : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Unit cost for a 4-connected move, `⊤` (no edge) otherwise. -/
def w (u v : ℤ × ℤ) : ℝ≥0∞ := if Adj u v then 1 else ⊤

/-- Manhattan distance `|Δx| + |Δy|`. -/
def manhattan (u g : ℤ × ℤ) : ℕ := (u.1 - g.1).natAbs + (u.2 - g.2).natAbs

/-- A single 4-connected move changes the Manhattan distance to `g` by at most `1`. -/
lemma manhattan_le_succ {u v g : ℤ × ℤ} (h : Adj u v) : manhattan u g ≤ manhattan v g + 1 := by
  unfold Adj at h; unfold manhattan; omega

/-- **Manhattan distance is a consistent heuristic** for 4-connected unit moves. -/
theorem consistent_manhattan (g : ℤ × ℤ) :
    Consistent w g (fun u => (manhattan u g : ℝ≥0∞)) := by
  refine ⟨by simp [manhattan], fun u v => ?_⟩
  unfold w
  split_ifs with h
  · have := manhattan_le_succ (g := g) h
    change ((manhattan u g : ℕ) : ℝ≥0∞) ≤ 1 + (manhattan v g : ℕ)
    rw [add_comm]; exact_mod_cast this
  · simp

/-- Hence Manhattan distance is admissible. -/
theorem admissible_manhattan (g : ℤ × ℤ) :
    Admissible w g (fun u => (manhattan u g : ℝ≥0∞)) :=
  (consistent_manhattan g).admissible

/-- From any cell other than `g` there is a 4-neighbour one step closer to `g`. -/
lemma exists_step {u g : ℤ × ℤ} {n : ℕ} (h : manhattan u g = n + 1) :
    ∃ v, Adj u v ∧ manhattan v g = n := by
  unfold manhattan at h
  by_cases h1 : u.1 < g.1
  · exact ⟨(u.1 + 1, u.2), by simp [Adj], by simp [manhattan]; omega⟩
  by_cases h2 : g.1 < u.1
  · exact ⟨(u.1 - 1, u.2), by simp [Adj], by simp [manhattan]; omega⟩
  by_cases h3 : u.2 < g.2
  · exact ⟨(u.1, u.2 + 1), by simp [Adj], by simp [manhattan]; omega⟩
  · exact ⟨(u.1, u.2 - 1), by simp [Adj], by simp [manhattan]; omega⟩

/-- An explicit monotone staircase path of cost exactly the Manhattan distance. -/
lemma exists_path (g : ℤ × ℤ) : ∀ (n : ℕ) (u : ℤ × ℤ), manhattan u g = n →
    ∃ p : Walk u g, p.cost w = n := by
  intro n
  induction n with
  | zero =>
    intro u hu
    have : u = g := by
      unfold manhattan at hu; ext <;> omega
    subst this; exact ⟨Walk.nil u, by simp⟩
  | succ n ih =>
    intro u hu
    obtain ⟨v, hv, hvn⟩ := exists_step hu
    obtain ⟨p, hp⟩ := ih v hvn
    refine ⟨Walk.cons u p, ?_⟩
    simp [w, hv, hp, add_comm]

/-- **Manhattan distance is the exact shortest-path length on the 4-connected grid.** -/
theorem dist_eq_manhattan (g u : ℤ × ℤ) : dist w g u = manhattan u g := by
  refine le_antisymm ?_ (admissible_manhattan g u)
  obtain ⟨p, hp⟩ := exists_path g _ u rfl
  exact hp ▸ iInf_le _ p

end Grid

end RoboLean.Search
