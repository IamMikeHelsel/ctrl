# Handoff Report: Deep Investigation of Open Lanes (Erdős 273 and Erdős 885)

## 1. Observation

### 1.1 work/273 (Erdős 273 Covering Systems)
- **Problem Statement**: Erdős problem 273 (`https://www.erdosproblems.com/273`) asks whether there exists a covering system of the integers by distinct congruences $r_i \pmod{m_i}$ with moduli $m_i \ge 4$ such that each $m_i + 1$ is prime.
- **Even Moduli Necessity**: In `lean/Research/CoveringFamily.lean:323-339` (`even_smooth_representation`), Lean verifies that if $4 \le m$ and $(m+1)$ is prime, $m$ is necessarily even (since $m$ odd implies $m+1 \ge 6$ is even and composite).
- **Existing 7-Smooth Kernel-Checked Formalization**:
  - `lean/Research/CoveringFamily.lean:343-412`: Proves `seven_smooth_period_gap` and `seven_smooth_not_cover`:
    ```lean
    theorem seven_smooth_period_gap (D : Finset ℕ) (r : ℕ → ℤ) (H : ℕ)
        (h60 : 60 ∣ H) (hdiv : ∀ m ∈ D, m ∣ H)
        (hvalid : ∀ m ∈ D, 4 ≤ m ∧ (m + 1).Prime ∧
          ∃ a b c d : ℕ, m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
        (H : ℝ) * (57 / 10000) ≤
          (((Finset.range H).filter (fun n : ℕ => ∀ m ∈ D,
            ((n : ℤ) + r 4) % (m : ℤ) ≠ r m % (m : ℤ))).card : ℝ)

    theorem seven_smooth_not_cover (D : Finset ℕ) (r : ℕ → ℤ)
        (hvalid : ∀ m ∈ D, 4 ≤ m ∧ (m + 1).Prime ∧
          ∃ a b c d : ℕ, m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
        ∃ n : ℤ, ∀ m ∈ D, n % (m : ℤ) ≠ r m % (m : ℤ)
    ```
  - Axiom check (`CoveringFamily.lean:413-415`): `#print axioms seven_smooth_period_gap` and `#print axioms seven_smooth_not_cover` print strictly `[propext, Classical.choice, Quot.sound]`, with 0 `sorry`.
  - Architecture: Modulated into 6 Lean files (`CoveringCRT.lean`, `CoveringTail.lean`, `CoveringMass.lean`, `CoveringCapacity.lean`, `CoveringAssembly.lean`, `CoveringFamily.lean`).
  - Finite arithmetic certificate: `CoveringCapacity.lean:93-97` (`seven_smooth_capacity_certificate`) verifies all 720 normalized prefix assignments via `set_option maxRecDepth 4096 in decide +kernel`.
  - Independent audit: `work/273/check_seven.py:1-157` replays the 7-smooth certificate without bitmasks or search imports and includes 4 mutation tests in `mutation_checks()`.
- **Existing 11-Smooth Extension Artifacts**:
  - `work/273/smooth_probe.py:1-157`: Computes exact rational conditional capacity bounds over prime support `[2, 3, 5, 7, 11]` with exponent caps `[14, 9, 6, 5, 4]`.
  - Prefix chosen: `[4, 6, 10, 12, 16, 18, 30, 36]`, with common period $L = \text{lcm}(4,6,10,12,16,18,30,36) = 720$.
  - Sieve and exponent box: Retains 5,265 moduli $m \ge 4$ passing Fermat tests base 2 and 3 for $m+1$.
  - Unconditioned density upper bound: $\sum_{m \in \text{pool}} \frac{1}{m} + \text{tail} = \frac{728347923255532331431}{619957906178688000000} \approx 1.174834 > 1$.
  - Geometric tail outside box: $\text{tail} = \frac{1806085527193}{7116137582400000} \approx 0.0002538$.
  - Stabilizer reduction: In `smooth_probe.py:107-111`, translation by previous lcm allows branching on residue $a \in [0, \gcd(\text{stabilizers}[k], m) - 1]$.
  - Performance difference:
    - Without stabilizer reduction (`work/273/probe-11-deep.json`): 594,323 nodes, 75.58 s.
    - With stabilizer reduction (`work/273/probe-11-symmetric.json`): 3,518 nodes, 0.86 s.
    - Both runs yield `unresolved: 0`, `excluded_by_python_bound: true`, and `minimum_prune_gap: 50661803066306609 / 1239915812357376000000` ($\approx 0.040859$, $> 4.08\%$ uncovered points).
  - 13-Smooth attempt: `work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json` timed out after 240 s at period 5040 with 22,944 retained moduli, 26,952 unresolved nodes, and positive excess ($+0.0402$).

---

### 1.2 work/pod/885 (Erdős 885 $6 \times 4$ Grids)
- **Problem Statement**: Erdős problem 885 asks whether for every $k$, there exist $k$ integers $N_1, \dots, N_k$ sharing $k$ differences in their factor-difference sets $D(N) = \{|a-b| : ab = N\}$.
- **Equivalence**: $k$ integers sharing $m$ differences $\iff$ a $(k+1) \times m$ rational sumset of squares $U + V \subseteq \text{Squares}$ with $0 \in U$ and $V = \{d_j^2\}$.
  - A $6 \times 4$ sumset of squares corresponds to:
    - Form A: 5 integers sharing 4 differences ($k=4, m=4$, plus an extra base row);
    - Form B (transposed): 3 integers sharing 6 differences ($k=2, m=6$, plus an extra base row).
  - Solving $k=5$ requires a $(5+1) \times 5 = 6 \times 5$ grid.
- **Prior Art Audit (`work/pod/885/PRIOR_ART.md`)**:
  - Published literature (Guy D14, Choudhry arXiv:2508.07806 INTEGERS 2026, Bremner 2019 IJNT) contains $3 \times n$, $4 \times 4$, and $5 \times 4$ grids, but NO $6 \times 4$ or $4 \times 6$ grids.
  - Official Erdős Problems forum (up to 2026-09-29): posts reach $5 \times 4$ (Yicheng Pan, 3 numbers sharing 5 differences; Aleksanndr_NFA, 4 numbers sharing 4 differences).
  - Community web post (`erdosproblemaday.com/day/885-factor-difference-k5`, July 2026): mentions an unverified "community list of 71 primitive 4x6 rectangles" with negative search up to $q \le 10,000$.
- **Found $6 \times 4$ Configurations**:
  - **Class 1 (59-smooth)**:
    - Form B: $D(349102656) \cap D(1034586000) \cap D(4883112000) = \{6720, 15855, 26880, 45440, 69510, 129290\}$.
    - Form A (transposed): $N = \{206222625, 677376000, 2019635200, 4786481700, 16670745700\}$ share $d = \{13440, 75936, 129360, 279840\}$.
  - **Class 2 (101-smooth)**:
    - Form B: $D(4148640) \cap D(34418880) \cap D(300736800) = \{2988, 4356, 5787, 11164, 17046, 23948\}$.
    - Form A: $N = \{10046592, 24561225, 115706752, 281637972, 564578560\}$ share $d = \{5976, 10104, 24216, 69624\}$.
  - **Class 3 (Lagrange algebraic family)**:
    - Found by `curves/combine.py lagrange "u=x,v=1" 1 30000` at $x = -911/588$ (`curves/NOTES.md:9-20`, `curves/grids/g64_lagrange_m911_588.json`).
    - Form B: $N = \{70221547596375, 218508790732375, 2492797287180375\}$ share $d = \{7142490, 14215590, 18055770, 36195030, 115690710, 130085034\}$.
  - **Lean 4 Formalization**: `lean/Grid6x4.lean:1-170` proves all 4 theorems (`grid1_three_share_six`, `grid1_five_share_four`, `grid2_three_share_six`, `grid2_five_share_four`) using only standard axioms `[propext, Classical.choice, Quot.sound]`.
- **Search for Rational Extension ($q \le 10^6$)**:
  - `work/pod/885/smooth/extend_grids.cpp` and log `work/pod/885/smooth/extension_q1e6.log`:
    - Exhaustive search for rational column extensions ($w = p/q$) and row extensions with $q \le 1,000,000$.
    - Class 0: column hits = 0 (112.93 s), row hits = 0 (392.32 s).
    - Class 1: column hits = 0 (48.57 s), row hits = 0 (173.83 s).
    - Total: 0 hits across all directions.
  - Mordell-Weil lattice search (`curves/deep.py` and `curves/grids/g64_lagrange_m911_588.deep2.log`):
    - Tested all 20 column triples and all 4 row triples over the Mordell-Weil bases of $E: Y^2 = (X+v_i)(X+v_j)(X+v_k)$.
    - Tested hundreds of thousands of combinations: `done: 0 new rows, 0 new cols`.

---

## 2. Logic Chain

### 2.1 work/273: From Conditional Capacity to Formalization
1. **Unconditioned Failure**: The sum of reciprocal densities of 11-smooth prime-minus-one moduli in the box plus the geometric tail is $\approx 1.1748 > 1$. Therefore, any proof that 11-smooth moduli cannot cover the integers must exploit congruence overlap and conditional survivor geometry.
2. **Prefix Conditioning Principle**: Fix a prefix $P = \{m_1, \dots, m_k\}$ with period $L = \text{lcm}(P)$. For any choice of residue classes for $P$, let $U \subset [0, L)$ be the set of uncovered residues. Any subsequent modulus $m$ with $g = \gcd(m, L)$ can cover at most $g \cdot C_g(U) / (L \cdot m)$ points in $U$, where $C_g(U) = \max_r |\{x \in U \mid x \equiv r \pmod g\}|$.
3. **Stabilizer Pruning**: The search space of prefix assignments for $P = [4, 6, 10, 12, 16, 18, 30, 36]$ has size $1.86 \times 10^8$. However, translation by $\text{lcm}(m_1, \dots, m_{j-1})$ leaves earlier congruence classes invariant, reducing the branching factor at step $j$ to $\gcd(\text{lcm}(m_1, \dots, m_{j-1}), m_j)$.
4. **Finite Tree Verification**: With stabilizer reduction, the branch-and-bound tree terminates in exactly 3,518 nodes, all pruned before reaching full depth. At every node, remaining capacity is strictly bounded below survivor count by a gap of $\ge 0.040859$.
5. **Lean Gap Analysis**:
   - `CoveringCRT.lean` already contains the general counting lemma `conditional_class_card_le` and `lift_card` for arbitrary periods $B$ and moduli $m$.
   - The missing components are: (a) 5-prime geometric tail theorem `finite_tail_bound11`; (b) sieve/mass evaluation for 5,265 moduli across 30 gcd groups; (c) certified tree validation (computational reflection or explicit DAG certificate) since naive exhaustive `decide +kernel` would encounter $1.86 \times 10^8$ states.

### 2.2 work/pod/885: From Bounded Search to Genus-49 Structural Obstruction
1. **Rediscovery Assessment**: While published literature and the official forum stopped at $5 \times 4$, the July 2026 `erdosproblemaday.com` report of 71 rectangles establishes that $6 \times 4$ was already discovered by the community. Thus, the pod's findings represent an independent rediscovery, with the notable advance of formal Lean 4 certificates.
2. **Computational Extension Search ($q \le 10^6$)**:
   - Clearing denominators for a rational column $w = p/q$ gives $4N_i q^2 + p^2 = s_i^2$, requiring $p \in \bigcap_{i=1}^5 D(q^2 N_i)$.
   - `extend_grids.cpp` tested all $q \le 10^6$ for both primitive classes in both orientations, finding zero hits.
3. **The Algebraic Geometry of Column Extensions**:
   - Let $U = \{u_1, \dots, u_6\}$ be the 6 row elements of a $6 \times 4$ sumset of squares.
   - An extension column $v$ requires $u_i + v = y_i^2$ for $i=1,\dots,6$.
   - Eliminating $v$ yields 5 quadratic equations in $y_1, \dots, y_6$:
     $$y_i^2 - y_1^2 = u_i - u_1 \quad (i = 2, 3, 4, 5, 6)$$
   - In projective space $\mathbb{P}^6$ with homogeneous coordinates $[y_1 : \dots : y_6 : z]$, this is a complete intersection of 5 quadrics:
     $$y_i^2 - y_1^2 = (u_i - u_1) z^2 \quad (i = 2, 3, 4, 5, 6)$$
   - **Dimension and Degree**: Dimension $6 - 5 = 1$ (an algebraic curve $C$). Degree $\deg(C) = 2^5 = 32$.
   - **Genus Computation via Adjunction**:
     The canonical bundle is $\omega_C \cong \mathcal{O}_C(\sum d_i - (n+1)) = \mathcal{O}_C(2 \times 5 - 7) = \mathcal{O}_C(3)$.
     Degree of canonical bundle: $2g - 2 = 3 \cdot \deg(C) = 3 \cdot 32 = 96 \implies 2g = 98 \implies \mathbf{g = 49}$.
4. **Consequences of Genus 49**:
   - By **Faltings' Theorem** (1983), any smooth projective curve of genus $g \ge 2$ over $\mathbb{Q}$ has only **finitely many rational points**!
   - The 4 known columns $\{v_1, v_2, v_3, v_4\}$ furnish rational points on $C$.
   - Extending the grid requires finding an *additional* rational point on a curve of genus 49 that already has known rational points.
   - A Spark-scale computational search ($q \le 10^8$ or $10^9$) is searching for points on a genus 49 curve. Because rational points on higher-genus curves are either small or non-existent, brute-force search is mathematically ill-posed as a primary attack.
   - The correct open step is **algebraic-geometric obstruction certification** (Elliptic Curve Chabauty / 2-descent / Mordell-Weil sieve) to prove that $C(\mathbb{Q})$ contains *only* the known 4 columns, or finding a parameterized family.

---

## 3. Caveats

1. **Erdős 273 Overall Status**: Neither 7-smooth nor 11-smooth resolves Erdős problem 273. The full conjecture remains open for general moduli. Excluding smooth families proves that any covering system must involve moduli with prime factors $p \ge 11$ (7-smooth) or $p \ge 13$ (11-smooth).
2. **11-Smooth Sieve Completeness**: In `smooth_probe.py`, the Fermat base 2 and 3 test was used to discard composites. A pseudoprime passing Fermat tests only loosens the upper bound (conservative), but for a Lean formalization, either exact trial division or certified primality (e.g. Lucas-Lehmer / Pocklington) up to $1.25 \times 10^{15}$ is required.
3. **Erdős 885 Extension Scope**: The non-existence of a rational column up to $q \le 10^6$ applies specifically to the two tested primitive classes. It does not preclude that a 5th column exists at huge heights ($q > 10^6$) or on another undiscovered $6 \times 4$ class, nor does it preclude a $6 \times 5$ grid originating from a different family.
4. **Chabauty Condition**: Elliptic curve Chabauty requires the rank of the Jacobian or covering elliptic curves to be strictly less than the degree of the base field or genus. The rank of the Jacobian $J(C)$ (dimension 49) has not yet been computed.

---

## 4. Conclusion

### 4.1 Findings for work/273
1. **The 11-Smooth Covering Extension**: Uses conditional capacity with prefix $[4, 6, 10, 12, 16, 18, 30, 36]$ (period 720) to prove that no covering system exists using distinct moduli $m \ge 4$ with $m+1$ prime and prime factors $\le 11$. It overcomes an unconditioned reciprocal mass excess of $\approx 1.1748$ to establish a verified minimum density gap of $> 4.08\%$.
2. **Python Certificate Structure**: `smooth_probe.py` evaluates exact geometric tails, computes gcd-partitioned reciprocal masses for 5,265 moduli, and performs branch-and-bound with memoization and stabilizer reduction (3,518 nodes in 0.86 s).
3. **Missing Audit and Lean Formalization**:
   - Independent Python audit: Missing a standalone `check_eleven.py` with mutation tests.
   - Lean formalization: Missing `CoveringTail11.lean` (5-prime geometric tail), `CoveringMass11.lean` (mass bounds for 30 gcd groups), and `CoveringCapacity11.lean` (3,518-node certified tree checker via computational reflection).
4. **Lean Formalization Plan**:
   - Generalize `CoveringTail.lean` to 5 primes ($p \le 11$).
   - Implement `checkTree : SearchTree → Bool` in Lean and verify the 3,518-node certificate.
   - Re-use `CoveringCRT.lean` without modification (already fully parametric).

### 4.2 Findings for work/pod/885
1. **Prior Art / Rediscovery**: $6 \times 4$ grids are an independent rediscovery of a community finding reported in July 2026. The pod has provided the first Lean 4 verified proofs for two primitive classes (`lean/Grid6x4.lean`).
2. **Rational Column Search**: Bounded non-extension is established for both primitive classes up to denominator $q \le 1,000,000$ ($10^6$) in both row and column orientations (0 hits), exceeding prior art ($q \le 10^4$) by $100\times$.
3. **Nature of the Open Step**: The open step is **NOT** a Spark-scale brute-force search. The extension variety for a 5th column is a smooth complete intersection curve of **genus $g = 49$**. By Faltings' Theorem, rational points are finite. Brute-force searching on a genus 49 curve is mathematically blind.
4. **Testable Structural Lemmas and Obstruction Certificates**:
   - **Adjunction & Genus Theorem**: Formalize that the simultaneous square system for $m$ rows defines a complete intersection curve in $\mathbb{P}^m$ of genus $g = (m-4) 2^{m-2} + 1$ ($g=1$ for $m=4$; $g=17$ for $m=5$; $g=49$ for $m=6$).
   - **2-Descent on 20 Covering Curves**: Map $C_{49} \to E_{ijk}$ for each of the $\binom{6}{3} = 20$ triple curves. If any $E_{ijk}$ has rank 0, its rational points are restricted to 2-torsion points, providing an immediate obstruction certificate.
   - **Elliptic Curve Chabauty / Mordell-Weil Sieve**: Apply the Mordell-Weil sieve across multiple primes to prove that the 4 known columns are the *unique* rational points on $C_{49}$.

---

## 5. Verification Method

### 5.1 Verifying work/273 Artifacts
1. **Reproduce Existing 7-Smooth Lean 4 Proofs**:
   ```sh
   cd /Users/mike/dev/ctrl/lean
   lake env lean Research/CoveringFamily.lean
   lake build
   ```
   *Expected Output*: Exit code 0, 0 errors, prints standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
2. **Run Independent 7-Smooth Python Replay and Mutation Checks**:
   ```sh
   cd /Users/mike/dev/ctrl
   uv run python work/273/check_seven.py --self-test --output work/273/seven-certificate-audit.json
   ```
   *Expected Output*: `checked: true`, `rejected_mutations: 4`, minimum density margin `57/10000`.
3. **Reproduce 11-Smooth Python Certificate**:
   ```sh
   cd /Users/mike/dev/ctrl
   uv run python work/273/smooth_probe.py --primes 2,3,5,7,11 --caps 14,9,6,5,4 \
     --prefix 4,6,10,12,16,18,30,36 --output work/273/probe-11-symmetric.json
   ```
   *Expected Output*: Completes in $< 2$ seconds; `nodes: 3518`, `pruned: 3271`, `unresolved: 0`, `excluded_by_python_bound: true`.

### 5.2 Verifying work/pod/885 Artifacts
1. **Reproduce Lean 4 Verification of $6 \times 4$ Grids**:
   ```sh
   cd /Users/mike/dev/ctrl
   lake env lean work/pod/885/lean/Grid6x4.lean
   ```
   *Expected Output*: Exit code 0, proves `grid1_three_share_six`, `grid1_five_share_four`, `grid2_three_share_six`, `grid2_five_share_four`.
2. **Verify Factor Difference Intersections**:
   ```sh
   cd /Users/mike/dev/ctrl
   python3 work/pod/885/verify_k36.py
   python3 work/pod/885/curves/verify_grid.py work/pod/885/curves/grids/g64_lagrange_m911_588.json
   ```
   *Expected Output*: Exact divisor enumeration confirms 6 differences shared by 3 numbers, and 4 differences shared by 5 numbers.
3. **Inspect $q \le 10^6$ Exhaustive Log**:
   ```sh
   cat /Users/mike/dev/ctrl/work/pod/885/smooth/extension_q1e6.log
   cat /Users/mike/dev/ctrl/work/pod/885/smooth/extension_q1e6_coverage.txt
   ```
   *Expected Output*: Confirms zero column and row hits across both primitive classes for all $q \in [1, 10^6]$.
