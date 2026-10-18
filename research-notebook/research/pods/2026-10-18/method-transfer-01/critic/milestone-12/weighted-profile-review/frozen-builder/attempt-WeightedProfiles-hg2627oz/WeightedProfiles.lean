import Erdos128.OneStepSaving

/-!
Actual neighborhood profiles for an affine moment certificate.
The graph API and neighborhood endpoint construction are attributed upstream
work. New public bridge lemmas below expose their exact means and costs and
derive the moment criterion. Upstream source files remain unchanged.
-/
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

namespace Erdos128.ProfileBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V]

def indicator (H : SimpleGraph V) (v : V) (u : V) : ℚ := by
  classical
  exact if H.Adj v u then 1 else 0

def neighborValue (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (f : V → ℚ) (v : V) : ℚ := by
  classical
  exact ∑ u ∈ H.neighborFinset v, W.weight u * f u

def twoLevel (H : SimpleGraph V) (v : V) (a b : ℚ) : V → ℚ :=
  fun u => a + b * indicator H v u

theorem mean_affine (W : RatProbabilityWeight V) (a b : ℚ) (f : V → ℚ) :
    weightedMean W (fun v => a + b * f v) = a + b * weightedMean W f := by
  unfold weightedMean
  calc
    _ = ∑ v, (a * W.weight v + b * (W.weight v * f v)) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, W.sum_eq_one]
      ring

theorem mean_indicator (H : SimpleGraph V) (W : RatProbabilityWeight V) (v : V) :
    weightedMean W (indicator H v) = weightedDegree H W v := by
  classical
  simp [weightedMean, indicator, weightedDegree, H.neighborFinset_eq_filter,
    Finset.sum_filter]

theorem mean_twoLevel (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (v : V) (a b : ℚ) :
    weightedMean W (twoLevel H v a b) = a + b * weightedDegree H W v := by
  rw [twoLevel, mean_affine, mean_indicator]

theorem neighbor_affine (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (a b : ℚ) (f : V → ℚ) (v : V) :
    neighborValue H W (fun u => a + b * f u) v =
      a * weightedDegree H W v + b * neighborValue H W f v := by
  classical
  unfold neighborValue weightedDegree
  calc
    _ = ∑ u ∈ H.neighborFinset v,
        (a * W.weight u + b * (W.weight u * f u)) := by
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem mean_degree (H : SimpleGraph V) (W : RatProbabilityWeight V) :
    weightedMean W (weightedDegree H W) = 2 * edgeMass H W :=
  (two_mul_edgeMass H W).symm

theorem mean_second_degree (H : SimpleGraph V) (W : RatProbabilityWeight V) :
    weightedMean W (weightedSecondDegree H W) =
      weightedMean W (fun v => weightedDegree H W v ^ 2) := by
  classical
  simpa [weightedMean, weightedSecondDegree, weightedDegree, pow_two, mul_assoc]
    using weighted_neighbor_sum_swap H W.weight
      (fun v => W.weight v * weightedDegree H W v)

theorem indicator_degree (H : SimpleGraph V) (W : RatProbabilityWeight V) (v : V) :
    weightedMean W (fun u => indicator H v u * weightedDegree H W u) =
      weightedSecondDegree H W v := by
  classical
  simp [weightedMean, indicator, weightedSecondDegree,
    H.neighborFinset_eq_filter, Finset.sum_filter]

theorem mean_neighbor_indicator (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (v : V) :
    weightedMean W (neighborValue H W (indicator H v)) =
      weightedSecondDegree H W v := by
  classical
  unfold weightedMean neighborValue
  calc
    _ = ∑ u, (W.weight u * indicator H v u) *
        ∑ z ∈ H.neighborFinset u, W.weight z := by
      exact weighted_neighbor_sum_swap H W.weight (fun u => W.weight u * indicator H v u)
    _ = weightedMean W (fun u => indicator H v u * weightedDegree H W u) := by
      unfold weightedMean weightedDegree
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := indicator_degree H W v

theorem indicator_quadratic_zero (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (v : V) :
    (∑ u, W.weight u * indicator H v u * neighborValue H W (indicator H v) u) = 0 := by
  classical
  have hind := H.isIndepSet_neighborSet_of_triangleFree htri v
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : H.Adj v u
  · have hinner : neighborValue H W (indicator H v) u = 0 := by
      unfold neighborValue
      apply Finset.sum_eq_zero
      intro z hz
      have huz : H.Adj u z := (H.mem_neighborFinset u z).mp hz
      have hn : ¬ H.Adj v z := by
        intro hvz
        exact (hind hu hvz huz.ne) huz
      simp [indicator, hn]
    simp [hinner]
  · simp [indicator, hu]

theorem objective_twoLevel (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (v : V) (a b : ℚ) :
    weightedObjective H W (fun _ => 0) (twoLevel H v a b) =
      a ^ 2 * edgeMass H W + a * b * weightedSecondDegree H W v := by
  classical
  have hsum :
      (∑ u, W.weight u * (a + b * indicator H v u) *
        (a * weightedDegree H W u + b * neighborValue H W (indicator H v) u)) =
      a ^ 2 * weightedMean W (weightedDegree H W) +
        a * b * weightedMean W (neighborValue H W (indicator H v)) +
        a * b * weightedMean W (fun u => indicator H v u * weightedDegree H W u) +
        b ^ 2 * (∑ u, W.weight u * indicator H v u * neighborValue H W (indicator H v) u) := by
    calc
      _ = ∑ u, (a ^ 2 * (W.weight u * weightedDegree H W u) +
          a * b * (W.weight u * neighborValue H W (indicator H v) u) +
          a * b * (W.weight u * (indicator H v u * weightedDegree H W u)) +
          b ^ 2 * (W.weight u * indicator H v u * neighborValue H W (indicator H v) u)) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, weightedMean]
  change (1 / 2 : ℚ) *
      (∑ u, W.weight u * (a + b * indicator H v u) *
        neighborValue H W (fun z => a + b * indicator H v z) u) +
      weightedMean W (fun u => 0 * twoLevel H v a b u) = _
  simp only [neighbor_affine, zero_mul, weightedMean_const]
  rw [hsum, mean_degree, mean_neighbor_indicator, indicator_degree,
    indicator_quadratic_zero H W htri v]
  ring

def lowProfile (H : SimpleGraph V) (W : RatProbabilityWeight V) (α : ℚ) (v : V) : V → ℚ :=
  twoLevel H v (α / (1 - weightedDegree H W v)) (-α / (1 - weightedDegree H W v))

def highProfile (H : SimpleGraph V) (W : RatProbabilityWeight V) (α : ℚ) (v : V) : V → ℚ :=
  twoLevel H v 1 (-(1 - α) / weightedDegree H W v)

theorem low_profile_unit (H : SimpleGraph V) (W : RatProbabilityWeight V)
    {α : ℚ} (ha0 : 0 < α) (ha1 : α < 1) (v : V)
    (hd : weightedDegree H W v ≤ 1 - α) :
    IsUnitProfile (lowProfile H W α v) := by
  have hz : 0 < 1 - weightedDegree H W v := by
    linarith [weightedDegree_lt_one H W v]
  intro u
  by_cases hu : H.Adj v u
  · simp [lowProfile, twoLevel, indicator, hu]
  · simp only [lowProfile, twoLevel, indicator, if_neg hu, mul_zero, add_zero]
    exact ⟨(div_pos ha0 hz).le, (div_le_one hz).mpr (by linarith)⟩

theorem low_profile_mean (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (α : ℚ) (v : V) :
    weightedMean W (lowProfile H W α v) = α := by
  have hz : 1 - weightedDegree H W v ≠ 0 := by
    linarith [weightedDegree_lt_one H W v]
  rw [lowProfile, mean_twoLevel]
  field_simp [hz]
  ring

theorem low_profile_cost (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (α : ℚ) (v : V) :
    weightedObjective H W (fun _ => 0) (lowProfile H W α v) =
      α ^ 2 * (edgeMass H W - weightedSecondDegree H W v) /
        (1 - weightedDegree H W v) ^ 2 := by
  rw [lowProfile, objective_twoLevel H W htri]
  ring

theorem high_profile_unit (H : SimpleGraph V) (W : RatProbabilityWeight V)
    {α : ℚ} (ha0 : 0 < α) (ha1 : α < 1) (v : V)
    (hd : 1 - α < weightedDegree H W v) :
    IsUnitProfile (highProfile H W α v) := by
  have hb : 0 < 1 - α := by linarith
  have hd0 : 0 < weightedDegree H W v := by linarith
  have hr : 0 < (1 - α) / weightedDegree H W v := div_pos hb hd0
  have hr1 : (1 - α) / weightedDegree H W v < 1 := (div_lt_one hd0).mpr hd
  intro u
  by_cases hu : H.Adj v u
  · simp only [highProfile, twoLevel, indicator, if_pos hu, mul_one, neg_div]
    constructor <;> linarith
  · simp [highProfile, twoLevel, indicator, hu]

theorem high_profile_mean (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (α : ℚ) (v : V) (hd : weightedDegree H W v ≠ 0) :
    weightedMean W (highProfile H W α v) = α := by
  rw [highProfile, mean_twoLevel]
  field_simp [hd]
  ring

theorem high_profile_cost (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (α : ℚ) (v : V) :
    weightedObjective H W (fun _ => 0) (highProfile H W α v) =
      edgeMass H W - (1 - α) * weightedSecondDegree H W v / weightedDegree H W v := by
  rw [highProfile, objective_twoLevel H W htri]
  ring

theorem profile_boundary (H : SimpleGraph V) (W : RatProbabilityWeight V)
    {α : ℚ} (ha0 : 0 < α) (ha1 : α < 1) (v : V)
    (hd : weightedDegree H W v = 1 - α) :
    lowProfile H W α v = highProfile H W α v := by
  have ha : α ≠ 0 := ha0.ne'
  have hb : 1 - α ≠ 0 := by linarith
  funext u
  simp only [lowProfile, highProfile, twoLevel, hd]
  field_simp [ha, hb]
  ring

theorem exists_affine_profile (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (α T L : ℚ) (ha0 : 0 < α) (ha1 : α < 1)
    (hlo : ∀ d : ℚ, 0 ≤ d → d ≤ 1 - α →
      edgeMass H W - (T / α ^ 2) * (1 - d) ^ 2 - d ^ 2 ≤
        L * (d - 2 * edgeMass H W))
    (hhi : ∀ d : ℚ, 1 - α < d → d < 1 →
      d * (edgeMass H W - T) / (1 - α) - d ^ 2 ≤
        L * (d - 2 * edgeMass H W)) :
    ∃ π : V → ℚ, IsUnitProfile π ∧ weightedMean W π = α ∧
      weightedObjective H W (fun _ => 0) π ≤ T := by
  classical
  by_contra hnone
  have hb : 0 < 1 - α := by linarith
  have ha2 : 0 < α ^ 2 := sq_pos_of_pos ha0
  have hpoint (v : V) :
      weightedSecondDegree H W v - weightedDegree H W v ^ 2 <
        L * (weightedDegree H W v - 2 * edgeMass H W) := by
    let d := weightedDegree H W v
    let s := weightedSecondDegree H W v
    have hd0 : 0 ≤ d := weightedDegree_nonneg H W v
    have hd1 : d < 1 := weightedDegree_lt_one H W v
    by_cases hdb : d ≤ 1 - α
    · have hcost : T < weightedObjective H W (fun _ => 0) (lowProfile H W α v) := by
        apply lt_of_not_ge
        intro h
        exact hnone ⟨lowProfile H W α v, low_profile_unit H W ha0 ha1 v hdb,
          low_profile_mean H W α v, h⟩
      rw [low_profile_cost H W htri] at hcost
      have hz2 : 0 < (1 - d) ^ 2 := sq_pos_of_pos (by linarith)
      have hc : T * (1 - d) ^ 2 < α ^ 2 * (edgeMass H W - s) :=
        (lt_div_iff₀ hz2).mp hcost
      have hs : T / α ^ 2 * (1 - d) ^ 2 < edgeMass H W - s := by
        rw [show T / α ^ 2 * (1 - d) ^ 2 = (T * (1 - d) ^ 2) / α ^ 2 by ring]
        apply (div_lt_iff₀ ha2).mpr
        nlinarith
      have hl := hlo d hd0 hdb
      dsimp [d, s] at *
      linarith
    · have hdb' : 1 - α < d := lt_of_not_ge hdb
      have hdpos : 0 < d := by linarith
      have hcost : T < weightedObjective H W (fun _ => 0) (highProfile H W α v) := by
        apply lt_of_not_ge
        intro h
        exact hnone ⟨highProfile H W α v, high_profile_unit H W ha0 ha1 v hdb',
          high_profile_mean H W α v hdpos.ne', h⟩
      rw [high_profile_cost H W htri] at hcost
      have hfrac : (1 - α) * s / d < edgeMass H W - T := by linarith
      have hc := (div_lt_iff₀ hdpos).mp hfrac
      have hs : s < d * (edgeMass H W - T) / (1 - α) := by
        apply (lt_div_iff₀ hb).mpr
        nlinarith
      have hh := hhi d hdb' hd1
      dsimp [d, s] at *
      linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hw := W.sum_eq_one
    rw [hz, Finset.sum_empty] at hw
    norm_num at hw
  have hstrict :
      (∑ v, W.weight v * (weightedSecondDegree H W v - weightedDegree H W v ^ 2)) <
        ∑ v, W.weight v * (L * (weightedDegree H W v - 2 * edgeMass H W)) := by
    apply Finset.sum_lt_sum
    · intro v _
      exact (mul_lt_mul_of_pos_left (hpoint v) (W.positive v)).le
    · obtain ⟨v, hv⟩ := hne
      exact ⟨v, hv, mul_lt_mul_of_pos_left (hpoint v) (W.positive v)⟩
  have hleft :
      (∑ v, W.weight v * (weightedSecondDegree H W v - weightedDegree H W v ^ 2)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    change weightedMean W (weightedSecondDegree H W) -
      weightedMean W (fun v => weightedDegree H W v ^ 2) = 0
    rw [mean_second_degree]
    ring
  have hright :
      (∑ v, W.weight v * (L * (weightedDegree H W v - 2 * edgeMass H W))) = 0 := by
    change weightedMean W (fun v => L * (weightedDegree H W v - 2 * edgeMass H W)) = 0
    rw [show (fun v => L * (weightedDegree H W v - 2 * edgeMass H W)) =
        (fun v => -L * (2 * edgeMass H W) + L * weightedDegree H W v) by funext v; ring]
    rw [mean_affine, mean_degree]
    ring
  rw [hleft, hright] at hstrict
  exact (lt_irrefl 0) hstrict

end
end Erdos128.ProfileBridge
