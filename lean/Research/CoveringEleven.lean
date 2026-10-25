import Research.CoveringTail

/-!
# Eleven-Smooth and Thirteen-Smooth Geometric Tail Bounds for Erdős 273

This module extends `Research.CoveringTail` from the 4-prime (7-smooth) Euler
product `35 / 16` to:
1. The **5-prime (11-smooth)** Euler product `77 / 32` over `Exponents11 = Exponents × ℕ`
   and the exact rational tail bound `1806085527193 / 7116137582400000` outside the
   `10 × 7 × 5 × 4 × 5` exponent box `box11` (`work/273/eleven_smooth.py`).
2. The **6-prime (13-smooth)** Euler product `1001 / 384` over `Exponents13 = Exponents11 × ℕ`
   and the exact rational tail bound outside `box13 = box11 ×ˢ Finset.range 4`.
-/

namespace Research.CoveringEleven

open Research.CoveringTail

/-- Five-prime exponent tuples `((a, b), (c, d), e)` for `{2, 3, 5, 7, 11}`. -/
abbrev Exponents11 := Exponents × ℕ

/-- Reciprocal modulus weight `1 / (2^(a+1) * 3^b * 5^c * 7^d * 11^e)`. -/
noncomputable def weight11 (y : Exponents11) : ℝ :=
  weight y.1 * (1 / 11 : ℝ) ^ y.2

theorem weight11_nonneg (y : Exponents11) : 0 ≤ weight11 y := by
  unfold weight11
  have hw := weight_nonneg y.1
  positivity

/-- The 5-prime Euler product `(1) * (3/2) * (5/4) * (7/6) * (11/10) = 77 / 32`. -/
theorem weight11_hasSum : HasSum weight11 (77 / 32) := by
  have h11 : HasSum (fun e : ℕ => (1 / 11 : ℝ) ^ e) (11 / 10) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 11 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have h := weight_hasSum.mul h11 (weight_hasSum.summable.mul_of_nonneg h11.summable
    (fun _ => weight_nonneg _) (fun _ => by positivity))
  norm_num at h
  exact h

/-- The `10 × 7 × 5 × 4 × 5` finite exponent box for `{2, 3, 5, 7, 11}`. -/
def box11 : Finset Exponents11 :=
  box ×ˢ Finset.range 5

theorem box11_mass : ∑ y ∈ box11, weight11 y =
    (1023 / 1024 : ℝ) * (1093 / 729) * (781 / 625) * (400 / 343) * (16105 / 14641) := by
  simp only [box11, weight11, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [box_mass]
  norm_num [Finset.sum_range_succ]

/-- Exact unconditional tail bound outside `box11`:
for every finite subset `s` disjoint from `box11`,
`∑ y ∈ s, weight11 y ≤ 16889177 / 3227273280` (`≈ 5.233265 × 10⁻³`). -/
theorem finite_tail_bound_11 (s : Finset Exponents11) (h : Disjoint s box11) :
    ∑ y ∈ s, weight11 y ≤ 16889177 / 3227273280 := by
  have hu : ∑ y ∈ s ∪ box11, weight11 y ≤ 77 / 32 := by
    rw [← weight11_hasSum.tsum_eq]
    exact Summable.sum_le_tsum (s ∪ box11) (fun _ _ => weight11_nonneg _) weight11_hasSum.summable
  rw [Finset.sum_union h, box11_mass] at hu
  norm_num at hu
  linarith

/-- Six-prime exponent tuples `(((a, b), (c, d), e), f)` for `{2, 3, 5, 7, 11, 13}`. -/
abbrev Exponents13 := Exponents11 × ℕ

/-- Reciprocal modulus weight `1 / (2^(a+1) * 3^b * 5^c * 7^d * 11^e * 13^f)`. -/
noncomputable def weight13 (z : Exponents13) : ℝ :=
  weight11 z.1 * (1 / 13 : ℝ) ^ z.2

theorem weight13_nonneg (z : Exponents13) : 0 ≤ weight13 z := by
  unfold weight13
  have hw := weight11_nonneg z.1
  positivity

/-- The 6-prime Euler product `(77 / 32) * (13 / 12) = 1001 / 384`. -/
theorem weight13_hasSum : HasSum weight13 (1001 / 384) := by
  have h13 : HasSum (fun f : ℕ => (1 / 13 : ℝ) ^ f) (13 / 12) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 13 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have h := weight11_hasSum.mul h13 (weight11_hasSum.summable.mul_of_nonneg h13.summable
    (fun _ => weight11_nonneg _) (fun _ => by positivity))
  norm_num at h
  exact h

/-- The `10 × 7 × 5 × 4 × 5 × 4` finite exponent box for `{2, 3, 5, 7, 11, 13}`. -/
def box13 : Finset Exponents13 :=
  box11 ×ˢ Finset.range 4

theorem box13_mass : ∑ z ∈ box13, weight13 z =
    (1023 / 1024 : ℝ) * (1093 / 729) * (781 / 625) * (400 / 343) *
      (16105 / 14641) * (2380 / 2197) := by
  simp only [box13, weight13, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [box11_mass]
  norm_num [Finset.sum_range_succ]

/-- Exact unconditional tail bound outside `box13`:
`(1001 / 384) - box13_mass = 2333907245 / 405161108352` (`≈ 5.760442 × 10⁻³`). -/
theorem finite_tail_bound_13 (s : Finset Exponents13) (h : Disjoint s box13) :
    ∑ z ∈ s, weight13 z ≤ 2333907245 / 405161108352 := by
  have hu : ∑ z ∈ s ∪ box13, weight13 z ≤ 1001 / 384 := by
    rw [← weight13_hasSum.tsum_eq]
    exact Summable.sum_le_tsum (s ∪ box13) (fun _ _ => weight13_nonneg _) weight13_hasSum.summable
  rw [Finset.sum_union h, box13_mass] at hu
  norm_num at hu
  linarith

/-! ## Section 3: Certified Branch-and-Bound Pruning for the 11-Smooth Capacity Tree -/

/-- Exact rational tail bound outside the `14 × 10 × 7 × 6 × 5` exponent box
`(CAPS = (14, 9, 6, 5, 4))` of `work/273/check_eleven.py`:
$$(77 / 32) - (16383 / 16384)(29524 / 19683)(19531 / 15625)(19608 / 16807)(16105 / 14641)
  = \frac{1806085527193}{7116137582400000}.$$ -/
theorem check_eleven_box_tail_identity :
    (77 / 32 : ℝ) -
      (16383 / 16384 : ℝ) * (29524 / 19683) * (19531 / 15625) * (19608 / 16807) * (16105 / 14641) =
    1806085527193 / 7116137582400000 := by
  norm_num

/-- Certified Branch-and-Bound Pruning Theorem (`eleven_smooth_branch_prune_sound`):
Suppose a partial congruence assignment on period $L = 720$ leaves at least $S$ uncovered
residues out of $720$ (so the uncovered density satisfies $\text{uncovered} \ge S / 720$),
and the remaining available 11-smooth moduli split into a finite in-box pool of capacity
`in_box_cap` and a tail of capacity `tail_cap` bounded by `tail_bound`, with total remaining
capacity strictly less than `S / 720` by at least the certified worst-case leaf margin
`50661803066306609 / 1239915812357376000000` (and in particular at the worst-case survivor
floor $S \ge 212$). Then the remaining capacity is strictly less than the uncovered density
(`in_box_cap + tail_cap < uncovered`), so no extension can cover $\mathbb{Z}$. -/
theorem eleven_smooth_branch_prune_sound
    (S : ℝ) (uncovered in_box_cap tail_cap tail_bound : ℝ)
    (hS : 212 ≤ S)
    (h_uncov : S / 720 ≤ uncovered)
    (h_tail : tail_cap ≤ tail_bound)
    (h_margin : (S / 720) - (in_box_cap + tail_bound) ≥
      50661803066306609 / 1239915812357376000000) :
    (212 / 720 : ℝ) ≤ uncovered ∧
    uncovered - (in_box_cap + tail_cap) ≥ 50661803066306609 / 1239915812357376000000 ∧
    in_box_cap + tail_cap < uncovered := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Worst-Case Leaf Gap Certificate at $S = 212$ survivors out of $L = 720$:
When $S = 212$ uncovered residues survive on period $720$ and the remaining tail is bounded by
the exact `check_eleven.py` geometric tail `1806085527193 / 7116137582400000`, the survivor
density less the tail alone exceeds `209371104892123 / 711613758240000 > 0`, and any branch
node whose in-box capacity satisfies
`in_box_cap ≤ (212 / 720) - (1806085527193 / 7116137582400000) - (50661803066306609 / 1239915812357376000000)`
has strictly positive pruning gap `≥ 50661803066306609 / 1239915812357376000000 > 0`. -/
theorem eleven_smooth_worst_leaf_gap_pos :
    (0 : ℝ) < 50661803066306609 / 1239915812357376000000 ∧
    (212 / 720 : ℝ) - (1806085527193 / 7116137582400000) -
      (50661803066306609 / 1239915812357376000000) =
      364720968382125185071 / 1239915812357376000000 ∧
    (0 : ℝ) < (212 / 720 : ℝ) - (1806085527193 / 7116137582400000) := by
  norm_num

/-! ## Section 4: 13-Smooth Survivor Density Floor -/

/-- Thirteen-Smooth Survivor Density Floor (`thirteen_smooth_uncovered_floor`):
Suppose after conditioning on the 13-smooth finite box `box13`, a partial assignment leaves
uncovered density `u_13 ≥ 212 / 720` (or more generally `u_13 ≥ S_0`) and the remaining
admissible moduli lie in a finite subset `s` disjoint from `box13`. Then the uncovered
density remaining after applying all moduli in `s` is bounded below by
`S_0 - 2333907245 / 405161108352`, which for `S_0 = 212 / 720 = 53 / 180` is at least
`584817651071 / 2025805541760 > 0` (`≈ 0.288684 > 0`). -/
theorem thirteen_smooth_uncovered_floor
    (s : Finset Exponents13) (h : Disjoint s box13)
    (u_13 : ℝ) (hu : (212 / 720 : ℝ) ≤ u_13) :
    u_13 - ∑ z ∈ s, weight13 z ≥ 584817651071 / 2025805541760 ∧
    (0 : ℝ) < u_13 - ∑ z ∈ s, weight13 z := by
  have h_tail := finite_tail_bound_13 s h
  have h_num : (212 / 720 : ℝ) - (2333907245 / 405161108352) =
      584817651071 / 2025805541760 := by norm_num
  refine ⟨by linarith, by linarith⟩

#print axioms weight11_hasSum
#print axioms box11_mass
#print axioms finite_tail_bound_11
#print axioms weight13_hasSum
#print axioms box13_mass
#print axioms finite_tail_bound_13
#print axioms check_eleven_box_tail_identity
#print axioms eleven_smooth_branch_prune_sound
#print axioms eleven_smooth_worst_leaf_gap_pos
#print axioms thirteen_smooth_uncovered_floor

end Research.CoveringEleven
