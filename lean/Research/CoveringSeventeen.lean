import Research.CoveringEleven

/-!
# Seventeen-Smooth and Nineteen-Smooth Geometric Tail Bounds for Erdős 273

This module extends `Research.CoveringEleven` from the 5-prime (11-smooth, `77 / 32`)
and 6-prime (13-smooth, `1001 / 384`) Euler products to:
1. The **7-prime (17-smooth)** Euler product `17017 / 6144` over `Exponents17 = Exponents13 × ℕ`
   and the exact rational tail bound `736489091029 / 110203821471744` outside the
   `10 × 7 × 5 × 4 × 5 × 4 × 3` exponent box `box17`.
2. The **8-prime (19-smooth)** Euler product `323323 / 110592` over `Exponents19 = Exponents17 × ℕ`
   and the exact rational tail bound `198373075945637 / 26522386367533056` outside
   `box19 = box17 ×ˢ Finset.range 3`.
3. The **Monotonic Prime-Extension Capacity Ratio** (`euler_product_step_ratio`), establishing
   the exact multiplicative step ratios `p / (p - 1)` and strict capacity monotonicity across the
   7-smooth through 19-smooth covering hierarchies.
-/

namespace Research.CoveringSeventeen

open Research.CoveringTail Research.CoveringEleven

/-- Seven-prime exponent tuples `((((a, b), (c, d), e), f), g)` for `{2, 3, 5, 7, 11, 13, 17}`. -/
abbrev Exponents17 := Exponents13 × ℕ

/-- Reciprocal modulus weight `1 / (2^(a+1) * 3^b * 5^c * 7^d * 11^e * 13^f * 17^g)`. -/
noncomputable def weight17 (w : Exponents17) : ℝ :=
  weight13 w.1 * (1 / 17 : ℝ) ^ w.2

theorem weight17_nonneg (w : Exponents17) : 0 ≤ weight17 w := by
  unfold weight17
  have hw := weight13_nonneg w.1
  positivity

/-- The 7-prime (17-smooth) Euler product `(1001 / 384) * (17 / 16) = 17017 / 6144`. -/
theorem euler_product_17 : HasSum weight17 (17017 / 6144) := by
  have h17 : HasSum (fun g : ℕ => (1 / 17 : ℝ) ^ g) (17 / 16) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 17 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have h := weight13_hasSum.mul h17 (weight13_hasSum.summable.mul_of_nonneg h17.summable
    (fun _ => weight13_nonneg _) (fun _ => by positivity))
  norm_num at h
  exact h

/-- Alias for `euler_product_17` matching the `weight*_hasSum` convention. -/
theorem weight17_hasSum : HasSum weight17 (17017 / 6144) :=
  euler_product_17

/-- The `10 × 7 × 5 × 4 × 5 × 4 × 3` finite exponent box for `{2, 3, 5, 7, 11, 13, 17}`. -/
def box17 : Finset Exponents17 :=
  box13 ×ˢ Finset.range 3

theorem box17_mass : ∑ w ∈ box17, weight17 w =
    (1023 / 1024 : ℝ) * (1093 / 729) * (781 / 625) * (400 / 343) *
      (16105 / 14641) * (2380 / 2197) * (307 / 289) := by
  simp only [box17, weight17, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [box13_mass]
  norm_num [Finset.sum_range_succ]

/-- Exact unconditional tail bound outside `box17`:
`(17017 / 6144) - box17_mass = 736489091029 / 110203821471744` (`≈ 6.6830 × 10⁻³`). -/
theorem finite_tail_bound_17 (s : Finset Exponents17) (h : Disjoint s box17) :
    ∑ w ∈ s, weight17 w ≤ 736489091029 / 110203821471744 := by
  have hu : ∑ w ∈ s ∪ box17, weight17 w ≤ 17017 / 6144 := by
    rw [← euler_product_17.tsum_eq]
    exact Summable.sum_le_tsum (s ∪ box17) (fun _ _ => weight17_nonneg _) euler_product_17.summable
  rw [Finset.sum_union h, box17_mass] at hu
  norm_num at hu
  linarith

/-- Eight-prime exponent tuples `(((((a, b), (c, d), e), f), g), k)` for `{2, 3, 5, 7, 11, 13, 17, 19}`. -/
abbrev Exponents19 := Exponents17 × ℕ

/-- Reciprocal modulus weight `1 / (2^(a+1) * 3^b * 5^c * 7^d * 11^e * 13^f * 17^g * 19^k)`. -/
noncomputable def weight19 (u : Exponents19) : ℝ :=
  weight17 u.1 * (1 / 19 : ℝ) ^ u.2

theorem weight19_nonneg (u : Exponents19) : 0 ≤ weight19 u := by
  unfold weight19
  have hw := weight17_nonneg u.1
  positivity

/-- The 8-prime (19-smooth) Euler product `(17017 / 6144) * (19 / 18) = 323323 / 110592`. -/
theorem euler_product_19 : HasSum weight19 (323323 / 110592) := by
  have h19 : HasSum (fun k : ℕ => (1 / 19 : ℝ) ^ k) (19 / 18) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 19 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have h := euler_product_17.mul h19 (euler_product_17.summable.mul_of_nonneg h19.summable
    (fun _ => weight17_nonneg _) (fun _ => by positivity))
  norm_num at h
  exact h

/-- Alias for `euler_product_19` matching the `weight*_hasSum` convention. -/
theorem weight19_hasSum : HasSum weight19 (323323 / 110592) :=
  euler_product_19

/-- The `10 × 7 × 5 × 4 × 5 × 4 × 3 × 3` finite exponent box for `{2, 3, 5, 7, 11, 13, 17, 19}`. -/
def box19 : Finset Exponents19 :=
  box17 ×ˢ Finset.range 3

theorem box19_mass : ∑ u ∈ box19, weight19 u =
    (1023 / 1024 : ℝ) * (1093 / 729) * (781 / 625) * (400 / 343) *
      (16105 / 14641) * (2380 / 2197) * (307 / 289) * (381 / 361) := by
  simp only [box19, weight19, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [box17_mass]
  norm_num [Finset.sum_range_succ]

/-- Exact unconditional tail bound outside `box19`:
`(323323 / 110592) - box19_mass = 198373075945637 / 26522386367533056` (`≈ 7.4795 × 10⁻³`). -/
theorem finite_tail_bound_19 (s : Finset Exponents19) (h : Disjoint s box19) :
    ∑ u ∈ s, weight19 u ≤ 198373075945637 / 26522386367533056 := by
  have hu : ∑ u ∈ s.disjUnion box19 h, weight19 u ≤ 323323 / 110592 := by
    rw [← euler_product_19.tsum_eq]
    exact Summable.sum_le_tsum (s.disjUnion box19 h) (fun _ _ => weight19_nonneg _)
      euler_product_19.summable
  rw [Finset.sum_disjUnion h, box19_mass] at hu
  norm_num at hu
  linarith

/-- Monotonic Prime-Extension Capacity Ratio:
Extending the smooth prime pool from 7-smooth (`35/16`) through 11-smooth (`77/32`),
13-smooth (`1001/384`), 17-smooth (`17017/6144`), and 19-smooth (`323323/110592`)
multiplies the unconditioned Euler capacity ceiling by `p / (p - 1) > 1` at each step,
producing a strictly increasing rational tower bounded below `3`. -/
theorem euler_product_step_ratio :
    ((77 / 32 : ℝ) = (35 / 16) * (11 / 10)) ∧
    ((1001 / 384 : ℝ) = (77 / 32) * (13 / 12)) ∧
    ((17017 / 6144 : ℝ) = (1001 / 384) * (17 / 16)) ∧
    ((323323 / 110592 : ℝ) = (17017 / 6144) * (19 / 18)) ∧
    ((35 / 16 : ℝ) < 77 / 32) ∧
    ((77 / 32 : ℝ) < 1001 / 384) ∧
    ((1001 / 384 : ℝ) < 17017 / 6144) ∧
    ((17017 / 6144 : ℝ) < 323323 / 110592) ∧
    ((323323 / 110592 : ℝ) < 3) := by
  norm_num

/-- General prime-extension step ratio lemma: for any real modulus base `p > 1` and
positive base capacity `S > 0`, multiplying by the geometric series sum `(p / (p - 1))`
strictly increases the capacity ceiling. -/
theorem prime_extension_capacity_strict_mono {S p : ℝ} (hS : 0 < S) (hp : 1 < p) :
    S < S * (p / (p - 1)) := by
  have hp1 : 0 < p - 1 := by linarith
  have h_gt_one : 1 < p / (p - 1) := ( one_lt_div hp1 ).mpr (by linarith)
  nlinarith

#print axioms euler_product_17
#print axioms box17_mass
#print axioms finite_tail_bound_17
#print axioms euler_product_19
#print axioms box19_mass
#print axioms finite_tail_bound_19
#print axioms euler_product_step_ratio
#print axioms prime_extension_capacity_strict_mono

end Research.CoveringSeventeen
