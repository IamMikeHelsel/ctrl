import Erdos128.CubicNeighborhood

set_option linter.style.header false

/-!
# One centered-neighborhood saving step

The linear term in the objective is completely arbitrary.  The proof uses
the two feasible endpoints on the line through a centered neighborhood and
averages them with barycentric weights, so every linear contribution cancels.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V]

private def weightedNeighborValue (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (f : V → ℚ) (x : V) : ℚ := by
  classical
  exact ∑ y ∈ H.neighborFinset x, W.weight y * f y

private def weightedQuadraticQ (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (f : V → ℚ) : ℚ :=
  (1 / 2 : ℚ) *
    ∑ x, W.weight x * f x * weightedNeighborValue H W f x

private def neighborhoodIndicator (H : SimpleGraph V) (x : V) : V → ℚ := by
  classical
  exact fun y ↦ if H.Adj x y then 1 else 0

private def centeredNeighborhood (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (x : V) : V → ℚ :=
  fun y ↦ neighborhoodIndicator H x y - weightedDegree H W x

private def radiusPlus (α d : ℚ) : ℚ :=
  min ((1 - α) / (1 - d)) (α / d)

private def radiusMinus (α d : ℚ) : ℚ :=
  min (α / (1 - d)) ((1 - α) / d)

private def weightedEdgeDirectional (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (α : ℚ) (φ : V → ℚ) : ℚ :=
  (1 / 2 : ℚ) *
    ∑ x, W.weight x *
      (α * weightedNeighborValue H W φ x +
        φ x * (α * weightedDegree H W x))

private def weightedDirectional (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (ψ : V → ℚ) (α : ℚ) (φ : V → ℚ) : ℚ :=
  weightedEdgeDirectional H W α φ + weightedMean W (fun x ↦ ψ x * φ x)

private theorem weightedNeighborValue_add_mul
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (α t : ℚ) (φ : V → ℚ) (x : V) :
    weightedNeighborValue H W (fun y ↦ α + t * φ y) x =
      α * weightedDegree H W x + t * weightedNeighborValue H W φ x := by
  classical
  unfold weightedNeighborValue weightedDegree
  rw [show (∑ y ∈ H.neighborFinset x, W.weight y * (α + t * φ y)) =
      ∑ y ∈ H.neighborFinset x,
        (α * W.weight y + t * (W.weight y * φ y)) by
    apply Finset.sum_congr rfl
    intro y _
    ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem weightedMean_add_mul
    (W : RatProbabilityWeight V) (α t : ℚ) (φ : V → ℚ) :
    weightedMean W (fun x ↦ α + t * φ x) =
      α + t * weightedMean W φ := by
  unfold weightedMean
  rw [show (∑ x, W.weight x * (α + t * φ x)) =
      ∑ x, (α * W.weight x + t * (W.weight x * φ x)) by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, W.sum_eq_one]
  ring

private theorem weightedNeighborValue_const
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (α : ℚ) (x : V) :
    weightedNeighborValue H W (fun _ ↦ α) x = α * weightedDegree H W x := by
  simpa using weightedNeighborValue_add_mul H W α 0 (fun _ ↦ 0) x

private theorem weightedQuadraticQ_perturb
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (α t : ℚ) (φ : V → ℚ) :
    weightedQuadraticQ H W (fun x ↦ α + t * φ x) =
      weightedQuadraticQ H W (fun _ ↦ α) +
        t * weightedEdgeDirectional H W α φ +
        t ^ 2 * weightedQuadraticQ H W φ := by
  classical
  unfold weightedQuadraticQ weightedEdgeDirectional
  simp_rw [weightedNeighborValue_add_mul, weightedNeighborValue_const]
  have hsum :
      (∑ x, W.weight x * (α + t * φ x) *
          (α * weightedDegree H W x + t * weightedNeighborValue H W φ x)) =
        (∑ x, W.weight x * α * (α * weightedDegree H W x)) +
          t * (∑ x, W.weight x *
            (α * weightedNeighborValue H W φ x +
              φ x * (α * weightedDegree H W x))) +
          t ^ 2 * (∑ x, W.weight x * φ x * weightedNeighborValue H W φ x) := by
    calc
      _ = ∑ x, (W.weight x * α * (α * weightedDegree H W x) +
          t * (W.weight x *
            (α * weightedNeighborValue H W φ x +
              φ x * (α * weightedDegree H W x))) +
          t ^ 2 * (W.weight x * φ x * weightedNeighborValue H W φ x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum]
  ring

private theorem weightedLinear_perturb
    (W : RatProbabilityWeight V) (ψ φ : V → ℚ) (α t : ℚ) :
    weightedMean W (fun x ↦ ψ x * (α + t * φ x)) =
      weightedMean W (fun x ↦ ψ x * α) +
        t * weightedMean W (fun x ↦ ψ x * φ x) := by
  unfold weightedMean
  rw [show (∑ x, W.weight x * (ψ x * (α + t * φ x))) =
      ∑ x, (W.weight x * (ψ x * α) +
        t * (W.weight x * (ψ x * φ x))) by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem weightedObjective_perturb
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (ψ φ : V → ℚ) (α t : ℚ) :
    weightedObjective H W ψ (fun x ↦ α + t * φ x) =
      weightedObjective H W ψ (fun _ ↦ α) +
        t * weightedDirectional H W ψ α φ +
        t ^ 2 * weightedQuadraticQ H W φ := by
  have hquad := weightedQuadraticQ_perturb H W α t φ
  have hlin := weightedLinear_perturb W ψ φ α t
  change weightedQuadraticQ H W (fun x ↦ α + t * φ x) +
      weightedMean W (fun x ↦ ψ x * (α + t * φ x)) =
    weightedQuadraticQ H W (fun _ ↦ α) +
      weightedMean W (fun x ↦ ψ x * α) +
        t * weightedDirectional H W ψ α φ +
        t ^ 2 * weightedQuadraticQ H W φ
  rw [hquad, hlin]
  unfold weightedDirectional
  ring

private theorem weightedObjective_chord
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (ψ φ : V → ℚ) (α tPlus tMinus : ℚ)
    (ht : 0 < tPlus + tMinus) :
    (tMinus / (tPlus + tMinus)) *
        weightedObjective H W ψ (fun x ↦ α + tPlus * φ x) +
      (tPlus / (tPlus + tMinus)) *
        weightedObjective H W ψ (fun x ↦ α - tMinus * φ x) =
      weightedObjective H W ψ (fun _ ↦ α) +
        tPlus * tMinus * weightedQuadraticQ H W φ := by
  rw [show (fun x ↦ α - tMinus * φ x) =
      (fun x ↦ α + (-tMinus) * φ x) by funext x; ring]
  rw [weightedObjective_perturb H W ψ φ α tPlus,
    weightedObjective_perturb H W ψ φ α (-tMinus)]
  field_simp [ht.ne']
  ring

private theorem neighborhoodIndicator_mean
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    weightedMean W (neighborhoodIndicator H x) = weightedDegree H W x := by
  classical
  unfold weightedMean neighborhoodIndicator weightedDegree
  simp [H.neighborFinset_eq_filter, Finset.sum_filter]

private theorem centeredNeighborhood_mean_zero
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    weightedMean W (centeredNeighborhood H W x) = 0 := by
  unfold centeredNeighborhood
  rw [show weightedMean W
      (fun y ↦ neighborhoodIndicator H x y - weightedDegree H W x) =
      weightedMean W (neighborhoodIndicator H x) -
        weightedMean W (fun _ ↦ weightedDegree H W x) by
    unfold weightedMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring]
  rw [neighborhoodIndicator_mean, weightedMean_const]
  ring

private theorem indicator_degree_moment
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    weightedMean W
        (fun y ↦ neighborhoodIndicator H x y * weightedDegree H W y) =
      weightedSecondDegree H W x := by
  classical
  unfold weightedMean neighborhoodIndicator weightedSecondDegree
  simp [H.neighborFinset_eq_filter, Finset.sum_filter]

private theorem neighborIndicator_sum_mean
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    weightedMean W (weightedNeighborValue H W (neighborhoodIndicator H x)) =
      weightedSecondDegree H W x := by
  classical
  unfold weightedMean
  calc
    (∑ y, W.weight y * weightedNeighborValue H W (neighborhoodIndicator H x) y) =
        ∑ z, (W.weight z * neighborhoodIndicator H x z) *
          ∑ y ∈ H.neighborFinset z, W.weight y := by
      unfold weightedNeighborValue
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (weighted_neighbor_sum_swap H W.weight
          (fun z ↦ W.weight z * neighborhoodIndicator H x z))
    _ = weightedSecondDegree H W x := by
      rw [show (∑ z, (W.weight z * neighborhoodIndicator H x z) *
          ∑ y ∈ H.neighborFinset z, W.weight y) =
          weightedMean W
            (fun z ↦ neighborhoodIndicator H x z * weightedDegree H W z) by
        unfold weightedMean weightedDegree
        apply Finset.sum_congr rfl
        intro z _
        ring]
      exact indicator_degree_moment H W x

private theorem weightedQuadraticQ_indicator_zero
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (x : V) :
    weightedQuadraticQ H W (neighborhoodIndicator H x) = 0 := by
  classical
  have hind := H.isIndepSet_neighborSet_of_triangleFree htri x
  unfold weightedQuadraticQ
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : H.Adj x y
  · have hinner : weightedNeighborValue H W (neighborhoodIndicator H x) y = 0 := by
      unfold weightedNeighborValue
      apply Finset.sum_eq_zero
      intro z hz
      have hyz : H.Adj y z := (H.mem_neighborFinset y z).mp hz
      have hnxyz : ¬ H.Adj x z := by
        intro hxz
        exact (hind hy hxz hyz.ne) hyz
      simp [neighborhoodIndicator, hnxyz]
    simp [neighborhoodIndicator, hy, hinner]
  · simp [neighborhoodIndicator, hy]

private theorem centeredNeighborhood_quadratic
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (x : V) :
    weightedQuadraticQ H W (centeredNeighborhood H W x) =
      -cubicScore H W x := by
  classical
  let h : V → ℚ := neighborhoodIndicator H x
  let d : ℚ := weightedDegree H W x
  have hneighbor (y : V) :
      weightedNeighborValue H W (centeredNeighborhood H W x) y =
        weightedNeighborValue H W h y - d * weightedDegree H W y := by
    unfold weightedNeighborValue centeredNeighborhood h d
    rw [show (∑ z ∈ H.neighborFinset y,
        W.weight z * (neighborhoodIndicator H x z - weightedDegree H W x)) =
        ∑ z ∈ H.neighborFinset y,
          (W.weight z * neighborhoodIndicator H x z -
            weightedDegree H W x * W.weight z) by
      apply Finset.sum_congr rfl
      intro z _
      ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [weightedDegree]
  unfold weightedQuadraticQ
  simp_rw [hneighbor]
  have hsum :
      (∑ y, W.weight y * centeredNeighborhood H W x y *
          (weightedNeighborValue H W h y - d * weightedDegree H W y)) =
        (∑ y, W.weight y * h y * weightedNeighborValue H W h y) -
          d * weightedMean W
            (fun y ↦ h y * weightedDegree H W y) -
          d * weightedMean W (weightedNeighborValue H W h) +
          d ^ 2 * weightedMean W (weightedDegree H W) := by
    rw [show (∑ y, W.weight y * centeredNeighborhood H W x y *
        (weightedNeighborValue H W h y - d * weightedDegree H W y)) =
        ∑ y, (W.weight y * h y * weightedNeighborValue H W h y -
          d * (W.weight y * (h y * weightedDegree H W y)) -
          d * (W.weight y * weightedNeighborValue H W h y) +
          d ^ 2 * (W.weight y * weightedDegree H W y)) by
      apply Finset.sum_congr rfl
      intro y _
      dsimp [centeredNeighborhood, h, d]
      ring]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, weightedMean]
  rw [hsum]
  have hQ0 := weightedQuadraticQ_indicator_zero H W htri x
  have hfirst :
      (∑ y, W.weight y * h y * weightedNeighborValue H W h y) = 0 := by
    dsimp [weightedQuadraticQ] at hQ0
    linarith
  rw [hfirst, indicator_degree_moment, neighborIndicator_sum_mean]
  rw [show weightedMean W (weightedDegree H W) = 2 * edgeMass H W by
    simpa using (two_mul_edgeMass H W).symm]
  dsimp [cubicScore, d]
  ring

private theorem centered_plus_unit
    (H : SimpleGraph V) (W : RatProbabilityWeight V) {x : V} {α t : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hd0 : 0 < weightedDegree H W x) (hd1 : weightedDegree H W x < 1)
    (ht0 : 0 ≤ t)
    (htz : t ≤ (1 - α) / (1 - weightedDegree H W x))
    (htd : t ≤ α / weightedDegree H W x) :
    IsUnitProfile (fun y ↦ α + t * centeredNeighborhood H W x y) := by
  intro y
  by_cases hy : H.Adj x y
  · have hz : 0 < 1 - weightedDegree H W x := by linarith
    have hub : t * (1 - weightedDegree H W x) ≤ 1 - α :=
      (le_div_iff₀ hz).mp htz
    simp [centeredNeighborhood, neighborhoodIndicator, hy]
    constructor <;> nlinarith
  · have hlb : t * weightedDegree H W x ≤ α :=
      (le_div_iff₀ hd0).mp htd
    simp [centeredNeighborhood, neighborhoodIndicator, hy]
    constructor <;> nlinarith

private theorem centered_minus_unit
    (H : SimpleGraph V) (W : RatProbabilityWeight V) {x : V} {α t : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hd0 : 0 < weightedDegree H W x) (hd1 : weightedDegree H W x < 1)
    (ht0 : 0 ≤ t)
    (htz : t ≤ α / (1 - weightedDegree H W x))
    (htd : t ≤ (1 - α) / weightedDegree H W x) :
    IsUnitProfile (fun y ↦ α - t * centeredNeighborhood H W x y) := by
  intro y
  by_cases hy : H.Adj x y
  · have hz : 0 < 1 - weightedDegree H W x := by linarith
    have hlb : t * (1 - weightedDegree H W x) ≤ α :=
      (le_div_iff₀ hz).mp htz
    simp [centeredNeighborhood, neighborhoodIndicator, hy]
    constructor <;> nlinarith
  · have hub : t * weightedDegree H W x ≤ 1 - α :=
      (le_div_iff₀ hd0).mp htd
    simp [centeredNeighborhood, neighborhoodIndicator, hy]
    constructor <;> nlinarith

private theorem centerRadiusQ_eq_of_le_half {α : ℚ} (hα : α ≤ 1 / 2) :
    centerRadiusQ α = α := by
  unfold centerRadiusQ
  exact min_eq_left (by linarith)

private theorem centerRadiusQ_symm (α : ℚ) :
    centerRadiusQ (1 - α) = centerRadiusQ α := by
  unfold centerRadiusQ
  have : 1 - (1 - α) = α := by ring
  rw [this, min_comm]

private theorem radius_product_lower_of_le_half
    {α d : ℚ} (hα0 : 0 ≤ α) (hαh : α ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d < 1) :
    savingLQ α ≤ radiusPlus α d * radiusMinus α d := by
  have hz : 0 < 1 - d := by linarith
  have ha1 : α ≤ 1 := by linarith
  have hc : centerRadiusQ α = α := centerRadiusQ_eq_of_le_half hαh
  by_cases hda : d ≤ α
  · have hp : radiusPlus α d = (1 - α) / (1 - d) := by
      apply min_eq_left
      apply (div_le_div_iff₀ hz hd0).2
      nlinarith
    have hm : radiusMinus α d = α / (1 - d) := by
      apply min_eq_left
      apply (div_le_div_iff₀ hz hd0).2
      nlinarith
    rw [hp, hm]
    have hnum : 0 ≤ α * (1 - α) := mul_nonneg hα0 (by linarith)
    have hzsq : 0 < (1 - d) ^ 2 := sq_pos_of_pos hz
    have hbound : α * (1 - α) ≤
        ((1 - α) / (1 - d)) * (α / (1 - d)) := by
      rw [show ((1 - α) / (1 - d)) * (α / (1 - d)) =
          (α * (1 - α)) / (1 - d) ^ 2 by
        field_simp [hz.ne']]
      apply (le_div_iff₀ hzsq).2
      have hzle : (1 - d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
      nlinarith [mul_nonneg hnum (sub_nonneg.mpr hzle)]
    unfold savingLQ
    rw [hc]
    exact (min_le_right _ _).trans hbound
  · have had : α ≤ d := le_of_not_ge hda
    by_cases hdtop : d ≤ 1 - α
    · have hp : radiusPlus α d = α / d := by
        apply min_eq_right
        apply (div_le_div_iff₀ hd0 hz).2
        nlinarith
      have hm : radiusMinus α d = α / (1 - d) := by
        apply min_eq_left
        apply (div_le_div_iff₀ hz hd0).2
        nlinarith
      rw [hp, hm]
      have hdz : 0 < d * (1 - d) := mul_pos hd0 hz
      have hquarter : 4 * (d * (1 - d)) ≤ 1 := by
        nlinarith [sq_nonneg (2 * d - 1)]
      have hbound : 4 * α ^ 2 ≤ (α / d) * (α / (1 - d)) := by
        rw [show (α / d) * (α / (1 - d)) = α ^ 2 / (d * (1 - d)) by
          field_simp [hd0.ne', hz.ne']]
        apply (le_div_iff₀ hdz).2
        nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hquarter)]
      unfold savingLQ
      rw [hc]
      exact (min_le_left _ _).trans hbound
    · have htop : 1 - α ≤ d := le_of_not_ge hdtop
      have hp : radiusPlus α d = α / d := by
        apply min_eq_right
        apply (div_le_div_iff₀ hd0 hz).2
        nlinarith
      have hm : radiusMinus α d = (1 - α) / d := by
        apply min_eq_right
        apply (div_le_div_iff₀ hd0 hz).2
        nlinarith
      rw [hp, hm]
      have hdsq : 0 < d ^ 2 := sq_pos_of_pos hd0
      have hnum : 0 ≤ α * (1 - α) := mul_nonneg hα0 (by linarith)
      have hbound : α * (1 - α) ≤ (α / d) * ((1 - α) / d) := by
        rw [show (α / d) * ((1 - α) / d) = α * (1 - α) / d ^ 2 by
          field_simp [hd0.ne']]
        apply (le_div_iff₀ hdsq).2
        have hdsqle : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
        nlinarith [mul_nonneg hnum (sub_nonneg.mpr hdsqle)]
      unfold savingLQ
      rw [hc]
      exact (min_le_right _ _).trans hbound

private theorem radius_product_lower
    {α d : ℚ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hd0 : 0 < d) (hd1 : d < 1) :
    savingLQ α ≤ radiusPlus α d * radiusMinus α d := by
  by_cases hah : α ≤ 1 / 2
  · exact radius_product_lower_of_le_half hα0 hah hd0 hd1
  · let β : ℚ := 1 - α
    have hβ0 : 0 ≤ β := by dsimp [β]; linarith
    have hβh : β ≤ 1 / 2 := by dsimp [β]; linarith
    have h := radius_product_lower_of_le_half hβ0 hβh hd0 hd1
    dsimp [β] at h
    unfold savingLQ at h
    rw [centerRadiusQ_symm α] at h
    simpa [savingLQ, radiusPlus, radiusMinus, mul_comm] using h

private theorem savingLQ_nonneg {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ savingLQ α := by
  have hc0 : 0 ≤ centerRadiusQ α := by
    unfold centerRadiusQ
    exact le_min hα0 (by linarith)
  have hc1 : centerRadiusQ α ≤ 1 := by
    exact (min_le_left _ _).trans hα1
  unfold savingLQ
  exact le_min (by positivity) (mul_nonneg hc0 (by linarith))

/-- A constant rational profile can be replaced, at the same weighted mean,
by a unit profile saving at least `4 L(α) μ³` in an arbitrary quadratic-plus-
linear objective on a triangle-free weighted graph. -/
theorem exists_oneStepSaving
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (htri : H.CliqueFree 3) (ψ : V → ℚ) (α : ℚ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ π : V → ℚ,
      IsUnitProfile π ∧ weightedMean W π = α ∧
        weightedObjective H W ψ π ≤
          weightedObjective H W ψ (fun _ ↦ α) -
            4 * savingLQ α * edgeMass H W ^ 3 := by
  classical
  have hL0 : 0 ≤ savingLQ α := savingLQ_nonneg hα0 hα1
  by_cases hμ : 0 < edgeMass H W
  · by_cases ha0 : α = 0
    · subst α
      refine ⟨fun _ ↦ 0, ?_, by simp [weightedMean], ?_⟩
      · intro x
        exact ⟨le_rfl, by norm_num⟩
      · simp [savingLQ, centerRadiusQ]
    · by_cases ha1 : α = 1
      · subst α
        refine ⟨fun _ ↦ 1, ?_, weightedMean_one W, ?_⟩
        · intro x
          exact ⟨by norm_num, le_rfl⟩
        · simp [savingLQ, centerRadiusQ]
      · have ha0' : 0 < α := lt_of_le_of_ne hα0 (Ne.symm ha0)
        have ha1' : α < 1 := lt_of_le_of_ne hα1 ha1
        obtain ⟨x, hdx, hscore⟩ := exists_cubic_neighborhood H W hμ
        let d : ℚ := weightedDegree H W x
        let φ : V → ℚ := centeredNeighborhood H W x
        let tPlus : ℚ := radiusPlus α d
        let tMinus : ℚ := radiusMinus α d
        have hd0 : 0 < d := by simpa [d] using hdx
        have hd1 : d < 1 := by simpa [d] using weightedDegree_lt_one H W x
        have hz : 0 < 1 - d := by linarith
        have htp0 : 0 < tPlus := by
          dsimp [tPlus, radiusPlus]
          exact lt_min (div_pos (by linarith) hz) (div_pos ha0' hd0)
        have htm0 : 0 < tMinus := by
          dsimp [tMinus, radiusMinus]
          exact lt_min (div_pos ha0' hz) (div_pos (by linarith) hd0)
        let πPlus : V → ℚ := fun y ↦ α + tPlus * φ y
        let πMinus : V → ℚ := fun y ↦ α - tMinus * φ y
        have hpUnit : IsUnitProfile πPlus := by
          apply centered_plus_unit H W hα0 hα1 hdx (weightedDegree_lt_one H W x) htp0.le
          · simpa [tPlus, d, radiusPlus] using
              (min_le_left ((1 - α) / (1 - d)) (α / d))
          · simpa [tPlus, d, radiusPlus] using
              (min_le_right ((1 - α) / (1 - d)) (α / d))
        have hmUnit : IsUnitProfile πMinus := by
          apply centered_minus_unit H W hα0 hα1 hdx (weightedDegree_lt_one H W x) htm0.le
          · simpa [tMinus, d, radiusMinus] using
              (min_le_left (α / (1 - d)) ((1 - α) / d))
          · simpa [tMinus, d, radiusMinus] using
              (min_le_right (α / (1 - d)) ((1 - α) / d))
        have hpMean : weightedMean W πPlus = α := by
          dsimp [πPlus, φ]
          rw [weightedMean_add_mul, centeredNeighborhood_mean_zero]
          ring
        have hmMean : weightedMean W πMinus = α := by
          rw [show πMinus = (fun y ↦ α + (-tMinus) * φ y) by
            funext y
            dsimp [πMinus]
            ring]
          rw [weightedMean_add_mul]
          have hφ := centeredNeighborhood_mean_zero H W x
          simpa [φ, hφ]
        have hquad : weightedQuadraticQ H W φ = -cubicScore H W x := by
          simpa [φ] using centeredNeighborhood_quadratic H W htri x
        have hchord := weightedObjective_chord H W ψ φ α tPlus tMinus
          (add_pos htp0 htm0)
        rw [hquad] at hchord
        have hrad : savingLQ α ≤ tPlus * tMinus := by
          simpa [tPlus, tMinus, d] using radius_product_lower hα0 hα1 hd0 hd1
        have hscore0 : 0 ≤ cubicScore H W x := by
          exact (by positivity : 0 ≤ 4 * edgeMass H W ^ 3).trans hscore
        have hsaving :
            4 * savingLQ α * edgeMass H W ^ 3 ≤
              tPlus * tMinus * cubicScore H W x := by
          calc
            4 * savingLQ α * edgeMass H W ^ 3 =
                savingLQ α * (4 * edgeMass H W ^ 3) := by ring
            _ ≤ savingLQ α * cubicScore H W x :=
              mul_le_mul_of_nonneg_left hscore hL0
            _ ≤ (tPlus * tMinus) * cubicScore H W x :=
              mul_le_mul_of_nonneg_right hrad hscore0
        let qPlus := weightedObjective H W ψ πPlus
        let qMinus := weightedObjective H W ψ πMinus
        let qAvg := weightedObjective H W ψ (fun _ ↦ α) -
          tPlus * tMinus * cubicScore H W x
        have hchord' :
            (tMinus / (tPlus + tMinus)) * qPlus +
                (tPlus / (tPlus + tMinus)) * qMinus = qAvg := by
          dsimp [qPlus, qMinus, qAvg, πPlus, πMinus]
          linarith [hchord]
        have hwp : 0 < tMinus / (tPlus + tMinus) :=
          div_pos htm0 (add_pos htp0 htm0)
        have hwm : 0 < tPlus / (tPlus + tMinus) :=
          div_pos htp0 (add_pos htp0 htm0)
        have hweights :
            tMinus / (tPlus + tMinus) + tPlus / (tPlus + tMinus) = 1 := by
          field_simp [(add_pos htp0 htm0).ne']
          ring
        have hchoice : qPlus ≤ qAvg ∨ qMinus ≤ qAvg := by
          by_contra hn
          push Not at hn
          have hpos1 : 0 < (tMinus / (tPlus + tMinus)) * (qPlus - qAvg) :=
            mul_pos hwp (sub_pos.mpr hn.1)
          have hpos2 : 0 < (tPlus / (tPlus + tMinus)) * (qMinus - qAvg) :=
            mul_pos hwm (sub_pos.mpr hn.2)
          have hzero :
              (tMinus / (tPlus + tMinus)) * (qPlus - qAvg) +
                (tPlus / (tPlus + tMinus)) * (qMinus - qAvg) = 0 := by
            calc
              _ = ((tMinus / (tPlus + tMinus)) * qPlus +
                    (tPlus / (tPlus + tMinus)) * qMinus) -
                  ((tMinus / (tPlus + tMinus)) +
                    (tPlus / (tPlus + tMinus))) * qAvg := by ring
              _ = 0 := by rw [hchord', hweights]; ring
          linarith [add_pos hpos1 hpos2]
        have hAvgBound : qAvg ≤
            weightedObjective H W ψ (fun _ ↦ α) -
              4 * savingLQ α * edgeMass H W ^ 3 := by
          dsimp [qAvg]
          linarith
        rcases hchoice with hp | hm
        · exact ⟨πPlus, hpUnit, hpMean, hp.trans hAvgBound⟩
        · exact ⟨πMinus, hmUnit, hmMean, hm.trans hAvgBound⟩
  · have hμ0 : edgeMass H W = 0 :=
      le_antisymm (not_lt.mp hμ) (edgeMass_nonneg H W)
    refine ⟨fun _ ↦ α, ?_, weightedMean_const W α, ?_⟩
    · intro x
      exact ⟨hα0, hα1⟩
    · rw [hμ0]
      simp

end

end Erdos128
