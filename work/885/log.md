# Log: Erdős Problem 885

- 2026-10-19 `ctrl new 885`: drafted challenge from FC `Erdos885.erdos_885.variants.k_eq_3`
- 2026-10-19 fetched Spark job `20261019-121530-885-solve-1e67` (73-smooth `N ≤ 10^12`, `d ≤ 250000`: 30,654,888 rows, 727,083,350 incidences, 12 `K_{3,6}` hits, 1 `K_{2,13}` hit, 0 `K_{4,5}`/`K_{5,5}` hits) and proved `lean/ErdosLab/Erdos885.lean` (`erdos_885.variants.k_eq_3`; 0 `sorry`, standard axioms).
- 2026-10-24 `lean/Research/Erdos885C5Chabauty.lean` (branch `research/erdos885-coleman`): conditional
  proof that `C₅ : w² = x⁵ + 89x⁴ + 2796x³ + 35704x² + 123200x` has `C₅(ℚ) = {∞, (0,0)}`
  (`c5_rational_points_of_rank_one`), using a single-prime Mordell–Weil sieve at p = 17 plus
  Coleman disk certificates. All finite data is checked by `decide +kernel`. The open hypotheses are
  rank J(ℚ) ≤ 1, 2- and 5-saturation of ⟨D, T⟩, standard genus-2 divisor facts mod 17, and the
  Coleman expansions. Numerics (scripts in `work/885/c5/`, exact integers):
  - Rational point search, |a| ≤ 2·10⁵ and c < 200 (x = a/c²): only ∞ and (0,0).
  - Degree-2 divisor search, integer a-coefficients up to 400: only D = (x²+8x+32, 136x+272), up to sign.
  - #J(F_p) for good p ≤ 109. gcd = 2, so J(ℚ)_tors = ⟨T⟩ with T = [(0,0) − ∞]. D has order 74 mod 13,
    so rank ≥ 1.
  - Saturation: J(F₁₇) has order 400 with J(F₁₇)[2] ≅ (ℤ/2)⁴ and D₁₇ ∉ {0, T}, so ⟨D, T⟩ is 2-saturated.
    J(F₄₁) has order 2000 and D₄₁ has order 250, so it is 5-saturated.
  - Coleman integrals at 17, from tiny integrals on 2D, 4D, 6D in the disk of (0,0) (linear to 17⁶):
    ∫_{2D} dx/y = 17·u₀ and ∫_{2D} x dx/y = 17²·u₁, with u₀ ≡ 10 and u₁ ≡ 16 (mod 17). The disk
    leading coefficients are 3 (∞) and 15 ((0,0)), both units.
  - **Provenance:** q₅ = f/x is irreducible over ℚ, so C₅ is not one of the fully split quotients
    of the Class 1 tower. Its link to k = 5 is unverified.
  - Rank ≤ 1 is not verified. A 2-descent needs Magma or Sage, and neither is installed.
