# Handoff Report: Survey and Triage of Open Mathematical Problems

**Agent**: `explorer_survey_math_1`  
**Date**: 2026-10-19  
**Recipient**: `0b6a5e14-8c10-4497-8beb-fd637698bacb`  
**Working Directory**: `/Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_math_1`  

---

## 1. Observation

### 1.1 Upstream Prior-Art Gate and Erdős 834 Pilot Role
1. **Prior-Art Gate Verification (`./ctrl triage`)**:
   - In `/Users/mike/dev/ctrl-erdos-rename/tools/ctrl_cli/triage.py` (lines 153–159):
     ```python
     erdos_ids = jsp_to_erdos.get(jid, set())
     erdos_in_plby = erdos_ids.intersection(plby_erdos)
     if erdos_in_plby:
         reasons.append(
             f"in plby/lean-proofs (Erdős {', '.join(str(e) for e in sorted(erdos_in_plby))})"
         )
     ```
   - In `/Users/mike/dev/ctrl-erdos-rename/tools/data/plby_erdos.json` (line 426):
     ```json
     834,
     ```
   - Problem 834 is indexed as an already-solved problem in the upstream repository `plby/lean-proofs`.
   - In `/Users/mike/dev/ctrl/work/834/status.json` (lines 4–19):
     ```json
     "fc_theorem": "Erdos834.erdos_834.parts.ii",
     "fc_pin": "d9ce556",
     "axiom_tier": "default",
     "last_check": {
       "ok": false,
       "build": true,
       "tokens": true,
       "axioms": true,
       "binding": true,
       "hash": false,
       "failed": ["NOT_APPROVED"]
     }
     ```
   - In `/Users/mike/dev/ctrl/docs/crossover-program-report-2026-10-18.md` (lines 48–50, 124–159):
     The existing Erdős 834 part ii solution formalizes Li's 9-vertex, 22-edge 3-uniform hypergraph. The crossover work compressed the non-2-colorability exhaustion from 512 assignments to a 3-branch, 4-leaf NAE propagation tree. A weighted-clique LP relaxation yielded bound 44 (too weak vs optimal 42), and a numerical SDP gave 44.5189.
   - **Conclusion on 834**: Erdős 834 is a benchmark reference for certificate structuring (SAT/NAE tree compression, exact energy bounds), but is strictly disqualified from being a novelty target.

### 1.2 Inventory of Math Problems Across Repositories
1. **Catalog Scan (`/Users/mike/dev/ctrl/data/erdos/open.csv`)**:
   - 642 open problems tracked.
   - 55 problems carry approximate cash prizes ($10 to $10,000).
   - Filtered for combinations of:
     - Finite computation / construction / counterexample search route.
     - Formal Conjectures statement present (`has_fc = yes`).
     - Amenability to cross-discipline techniques: SAT/SDP, flag algebras, Lyapunov/potential functions, algebraic geometry.
2. **Sibling Repositories**:
   - `/Users/mike/dev/ctrl-erdos-lab`: Formalized proofs for already-solved problems (#261 [telescoping sequence], #291 [Steinerberger base-3 lcm], #382 [Bertrand postulate for product of intervals], #834 [Li hypergraph NAE tree], #931 [consecutive integer prime factor equality]).
   - `/Users/mike/dev/ctrl-erdos-rename`: Established triage filtering scripts and historical notes.
   - `/Users/mike/Dev/formal-conjectures`: Reference definitions in Lean 4 (checked at commit `d9ce556`).
3. **Recent Mathematical Literature Discoveries**:
   - **Erdős 500** ($\pi(K_4^{(3)})$ Turán density): Just received a significant breakthrough preprint in September 2026 by G. Jeong et al. (arXiv:2609.27495v2), proving $\pi(K_4^{(3)}) < 0.557789$ with a complete Lean 4 formal verification of the 7-vertex flag-algebra certificate. This moves the state-of-the-art beyond Baber's 2012 bound of 0.5615.
   - **Erdős 488** (density of multiples): An author package by D. Gessel (September 2026) claims a full refutation of the unrestricted conjecture with Lean source.
   - **Erdős 647** (divisor count): August 2026 preprint by Mian & Siddique (arXiv:2608.17880) established kernel-checked exclusion through $10^9$.

---

## 2. Logic Chain: Triage and Selection of Top 3 Candidates

To identify genuine novelty targets where computational, symbolic, and cross-discipline methods can produce a checkable result or certificate, we apply four filtering criteria:
1. **Novelty & Uncontested Status**: Must NOT be solved upstream (not in `plby/lean-proofs`), have no pending unmerged PRs in `TheJustinSunPrize/awards`, and not be duplicative of existing active pod work (e.g. #885, #939).
2. **Cross-Discipline Transferability**: Must bridge directly to one of the specified crossovers:
   - Real Algebraic Geometry / Computer Vision Minimal Solvers (polynomial homotopy, Cayley-Menger varieties, SOS).
   - Semidefinite Programming / Flag Algebras (analogous to Lyapunov / SOS energy certificates in control).
   - Discrete Dynamical Potential Functions (Local Cut Lemma / entropy bounds) + SAT/CP-SAT branch-and-bound.
3. **Finite Certificate Feasibility**: Must admit an exact, kernel-checkable artifact (rational SOS decomposition, LRAT proof, explicit rational coordinate witness checked by `decide` or `norm_num`).
4. **Concrete Falsifiability**: Must have an explicit small instance or search domain where a negative or positive result can be definitively established.

Applying these criteria isolates three standout problems spanning discrete geometry, extremal hypercube combinatorics, and additive number theory.

---

### Candidate 1: Erdős Problem 97 — Convex Polygons and Equidistant Vertices

#### 1. Statement and Current Known Bounds/Status
- **Formal Statement** (`FormalConjectures/ErdosProblems/97.lean:79–81`):
  ```lean
  theorem erdos_97 :
      ∀ A : Finset ℝ², A.Nonempty → ConvexIndep A → ¬HasNEquidistantProperty 4 A
  ```
  *Question*: Does every convex polygon in $\mathbb{R}^2$ have a vertex with no four other vertices equidistant from it? (Prize: $100).
- **Current Status**: Open for $k = 4$.
- **Known Bounds**:
  - $k = 3$: Originally conjectured by Erdős in 1946 (Amer. Math. Monthly). Disproved by Ludwig Danzer (1986), who constructed a convex 9-gon with 3-fold cyclic symmetry ($C_3$) where every vertex has at least 3 other vertices equidistant from it (`erdos_97.variants.three_equidistant`).
  - Unit distance variant: Fishburn and Reeds (1992, Comput. Geom.) constructed a convex 20-gon where every vertex has 3 *unit-distance* vertices, and proved 20 is the minimal cut partition size.
  - $k = 4$: No convex polygon is known where every vertex has 4 equidistant vertices; no proof of non-existence is known for any $n$.

#### 2. Prior-Art Checks
- **erdosproblems.com/97**: Classified as Open ($100 prize for counterexample, $50 for proof).
- **Formal Conjectures**: Full Lean 4 definitions present in `97.lean` (`HasNEquidistantProperty`, `ConvexIndep`).
- **arXiv & Google Scholar**: Brass, Pach, and Swanepoel (*Research Problems in Discrete Geometry*, 2005, Chapter 5); Nivasch et al. (*The number of distinct distances from a vertex of a convex polygon*); no counterexample for $k=4$ has ever been published or reported.

#### 3. Cross-Discipline Transfers
- **Transfer from Computer Vision Minimal Problems & Real Algebraic Geometry**:
  - In computer vision, multi-view geometry problems (e.g. 5-point relative pose, 8-point algorithm, planar homography, calibrated resectioning) solve polynomial systems subject to rank and rotation constraints via **polynomial homotopy continuation** and **resultant/Gröbner basis solvers**.
  - A polygon of $n$ points $p_i = (x_i, y_i) \in \mathbb{R}^2$ having 4 equidistant vertices per vertex defines a **real algebraic variety**:
    $$\|p_i - p_{j_{i,1}}\|^2 = \|p_i - p_{j_{i,2}}\|^2 = \|p_i - p_{j_{i,3}}\|^2 = \|p_i - p_{j_{i,4}}\|^2 = r_i^2 \quad \forall i \in \{1, \dots, n\}$$
    subject to orientation determinants enforcing strict convexity:
    $$\det \begin{pmatrix} 1 & x_i & y_i \\ 1 & x_j & y_j \\ 1 & x_k & y_k \end{pmatrix} > 0 \quad \text{for all cyclically ordered triples } (i, j, k).$$
  - Dihedral ($D_m$) or cyclic ($C_m$) symmetry groups dramatically collapse the dimension of the variety (from $2n$ variables to $\lfloor n/m \rfloor$ variables), making polynomial homotopy solvers (such as Bertini, HomotopyContinuation.jl, or Macaulay2) applicable.

#### 4. Concrete Falsification Test
- **Counterexample Search with Rational Certificate Verification**:
  1. Fix symmetry group $C_4$ or $D_4$ on $n = 16$ vertices, or $C_6$ on $n = 18$ vertices, with equidistant 4-tuples chosen symmetrically.
  2. Formulate the zero-dimensional polynomial system for the generator vertices.
  3. Solve numerically to high precision ($10^{-50}$) using homotopy continuation.
  4. If a candidate real root satisfies the strict determinant convexity conditions, apply the **Newton-Krawczyk interval operator** to prove quadratic convergence to an exact isolated real zero, and find a nearby rational coordinate representation $q_i \in \mathbb{Q}^2$.
  5. The resulting rational coordinates $(q_1, \dots, q_n)$ form an exact, kernel-checkable witness in Lean, verified via `decide` and `norm_num`.
  6. *Falsification criteria*: If interval bounding proves that the semi-algebraic variety defined by distance equalities and positive orientation determinants is empty for all symmetric configurations with $n \le 20$, the symmetric counterexample hypothesis for small $n$ is certified false.

---

### Candidate 2: Erdős Problem 86 — 4-Cycle-Free Subgraphs of the Hypercube

#### 1. Statement and Current Known Bounds/Status
- **Formal Statement** (`FormalConjectures/ErdosProblems/86.lean:45–50`):
  ```lean
  theorem erdos_86 :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool),
        H ≤ hypercube n →
          (1 / 2 + ε) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) →
            cycleGraph 4 ⊑ H
  ```
  *Question*: What is the maximum edge density $\pi_Q(C_4) = \lim_{n \to \infty} \frac{\mathrm{ex}(Q_n, C_4)}{e(Q_n)}$ of a $C_4$-free subgraph of the hypercube? Erdős conjectured that $\pi_Q(C_4) = 1/2$. (Prize: $100).
- **Current Status**: Open.
- **Known Bounds**:
  - Lower bound: $\pi_Q(C_4) \ge 1/2$. Achieved by taking all edges between layers $2k$ and $2k+1$ (an induced bipartite subgraph with no 4-cycles spanning alternate levels).
  - Upper bound:
    - Brass, Harborth, Nienborg (1995, J. Graph Theory): $\pi_Q(C_4) \le \frac{\sqrt{5}-1}{2} \approx 0.61803$.
    - Balogh, Hu, Lidický, Liu (2014, Eur. J. Combin.): $\pi_Q(C_4) \le 0.6068$ via flag algebras on the 3-cube.
    - Baber (2012, arXiv:1201.3587): $\pi_Q(C_4) \le 0.60318$ via semidefinite programming with flags up to 4-cube subgraphs.
  - The gap $[0.50000, 0.60318]$ has stood unresolved for over a decade.

#### 2. Prior-Art Checks
- **erdosproblems.com/86**: Classified as Open ($100 prize).
- **Formal Conjectures**: Formal statement in `86.lean`.
- **arXiv & Google Scholar**:
  - Baber (2012, arXiv:1201.3587), "Turán densities of hypercubes".
  - Balogh et al. (2014).
  - No paper has beaten Baber's $0.60318$ upper bound to date.

#### 3. Cross-Discipline Transfers
- **Transfer from Control Theory Lyapunov / SOS Certificates & Semidefinite Programming**:
  - The flag algebra method for host graphs (like the hypercube $Q_n$) expresses asymptotic edge density as a linear objective over flag densities, subject to linear inequalities arising from Cauchy-Schwarz bounds:
    $$\sum_{\sigma} \langle \mathbf{f}_{\sigma}, Q_{\sigma} \mathbf{f}_{\sigma} \rangle \ge 0 \quad \text{for all } Q_{\sigma} \succeq 0.$$
  - This is mathematically identical to finding a **Sum-of-Squares (SOS) polynomial certificate** or **Control Contraction / Lyapunov matrix** $Q \succeq 0$ certifying positive energy dissipation.
  - The DGX Spark contains the exact toolchain required: `~/venvs/solve` includes `cvxpy`, `clarabel`, `scs`, and `highs`.
  - Crucially, an SDP solution matrix $Q^* \succeq 0$ found by Clarabel can be projected to a rational matrix $Q_{\mathbb{Q}} \in \mathbb{Q}^{m \times m}$ with an explicit rational Cholesky/LDL decomposition $L D L^T$, giving an exact, kernel-checkable bound in Lean verified via `norm_num`.

#### 4. Concrete Falsification Test
- **Certifiable Flag Algebra SDP Search**:
  1. Generate the algebra of $C_4$-free subgraphs of $Q_4$ (4-cube) with allowed symmetries.
  2. Formulate the dual SDP minimizing the upper bound $\alpha$ subject to $Q_{\sigma} \succeq 0$ and flag density identities.
  3. Solve on the Spark via `ctrl spark solve 86 sdp_c4.py`.
  4. *Falsification test*:
     - If the optimal objective value $\alpha^* \ge 0.60318$, the hypothesis that 4-cube flags with standard symmetry types can improve Baber's bound is definitively refuted.
     - If $\alpha^* \le 0.59$, synthesize the rational Cholesky certificate $L D L^T \in \mathbb{Q}$, export to `work/86/certs/flag_sos.json`, and verify via rational matrix arithmetic in Python and Lean.

---

### Candidate 3: Erdős Problem 273 — Restricted Covering Systems with Moduli $p-1$ ($p \ge 5$)

#### 1. Statement and Current Known Bounds/Status
- **Formal Statement** (`FormalConjectures/ErdosProblems/273.lean:32–35`):
  ```lean
  theorem erdos_273 : ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ (p : ℕ), p.Prime ∧ 5 ≤ p ∧
      c.moduli i = Ideal.span {↑(p - 1)}
  ```
  *Question*: Is there a covering system of the integers whose moduli are all distinct and of the form $p-1$ for some prime $p \ge 5$?
- **Current Status**: Open.
- **Known Bounds**:
  - $p \ge 3$: Solved affirmatively (`erdos_273.variants.three`), since $3 - 1 = 2$, and modulus 2 allows simple coverings (e.g. $\{0 \pmod 2, 1 \pmod 4, 3 \pmod 6, \dots\}$).
  - $p \ge 5$: Moduli must be distinct even integers $\ge 4$: $\{4, 6, 10, 12, 16, 18, 22, 28, 30, \dots\}$. The absence of modulus 2 forces the total reciprocal sum to accumulate much more slowly.
  - Hough (2015, Annals of Math.) disproved the general minimum modulus conjecture, proving every covering system has a modulus $\le 10^{16}$.
  - The independent repository `idealombrer/erdos-273-covering-pm1` reported computational exclusions for common periods $\mathrm{lcm}(m_1, \dots, m_k) < 8 \times 10^6$ and prime cutoffs up to $p < 877$.

#### 2. Prior-Art Checks
- **erdosproblems.com/273**: Classified as Open.
- **Formal Conjectures**: Lean 4 formalization complete in `273.lean` (`StrictCoveringSystem`).
- **arXiv & Google Scholar**:
  - Hough (2015), "Solution of the minimum modulus problem for covering systems".
  - Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022, Invent. Math.), "Flat coverings and the minimum modulus problem".
  - No paper has settled the existence or non-existence of $p-1$ coverings for $p \ge 5$.

#### 3. Cross-Discipline Transfers
- **Transfer from Dynamical Potential Functions & SAT/CP-SAT Solving**:
  - **Lyapunov / Potential Function Method**: Hough's and Balister et al.'s breakthroughs introduced the **Local Cut Lemma**, which defines an energy/distortion potential function along prime fibers $q \mid L$. The potential function measures the conditional probability distribution of uncovered residues. If the potential function increases along the sieve filtration, coverage is proven impossible.
  - **SAT / Max-Coverage Encoding**: Finding a covering system for a candidate set of moduli $\mathcal{M} = \{m_1, \dots, m_k\}$ with common period $L = \mathrm{lcm}(m_1, \dots, m_k)$ is an exact propositional satisfiability (SAT) instance:
    - Boolean variables $x_{i, a}$ indicating whether residue $a \in \{0, \dots, m_i - 1\}$ is selected for modulus $m_i$ (with $\sum_a x_{i,a} = 1$).
    - Covering clauses: for every $y \in \{0, \dots, L - 1\}$, $\bigvee_{i=1}^k x_{i, y \bmod m_i} = \text{True}$.
  - The Spark has `Kissat 4.0.4` and `CaDiCaL 3.0.1` (with LRAT proof generation), allowing either rapid discovery of a satisfying covering assignment or certified proof of unsatisfiability for specific modulus candidate combinations.

#### 4. Concrete Falsification Test
- **Candidate Filter & Kissat Search**:
  1. Select a candidate modulus set $\mathcal{M} \subset \{p-1 : 5 \le p \le P\}$ satisfying the necessary density condition $\sum_{m \in \mathcal{M}} \frac{1}{m} > 1$ and having an admissible common period $L \in [10^7, 10^9]$ (e.g. smooth periods like $2^a \cdot 3^b \cdot 5^c \cdot 7^d$).
  2. Generate the CNF encoding over universe $\mathbb{Z}/L\mathbb{Z}$ with symmetry-breaking constraints ($x_{1,0} = 1$).
  3. Execute Kissat on the Spark (`ctrl spark solve`).
  4. *Falsification test*:
     - If SAT: Kissat returns a satisfying assignment $(a_m)_{m \in \mathcal{M}}$. This is an exact, finite mathematical witness: a Python script checks that every integer in $\{0, \dots, L-1\}$ is covered, and Lean verifies the finite covering by `decide` in seconds. This would completely resolve Erdős 273.
     - If UNSAT: CaDiCaL generates an LRAT refutation certificate, proving that no covering exists within that specific modulus family, establishing an exact mathematical exclusion boundary.

---

### Comparative Evaluation Matrix

| Candidate | Domain | Route / Technique | Cross-Discipline Transfer | Checkable Certificate Format | Primary Risk / Invalidation Mode |
|---|---|---|---|---|---|
| **Erdős 97** ($100) | Discrete Geometry in $\mathbb{R}^2$ | Real Algebraic Geometry & Homotopy Continuation | Computer Vision minimal solvers (5-point/8-point), Cayley-Menger varieties, interval Newton | Exact rational coordinates $(q_i \in \mathbb{Q}^2)$ checked by `decide` + `norm_num` in Lean | Non-existence of small ($n \le 24$) symmetric counterexample |
| **Erdős 86** ($100) | Extremal Graph Theory ($Q_n$) | Flag Algebras & Semidefinite Programming | Control theory SOS / Lyapunov matrices ($Q \succeq 0$), semidefinite duality | Rational Cholesky decomposition $L D L^T$ checked by `norm_num` in Lean | Flag size 4 SDP bound fails to strictly improve $0.60318$ |
| **Erdős 273** | Additive Number Theory | Potential Functions & SAT Solving | Discrete dynamical potential functions (Local Cut Lemma) + SAT solver (Kissat/CaDiCaL) | Explicit residue assignments $(a_m)_{m \in \mathcal{M}}$ checked by `decide`, or LRAT UNSAT proof | Minimum period $L$ exceeds memory/SAT scaling capacity |
| *Erdős 834* *(Pilot)* | Hypergraphs | NAE propagation trees | MaxCut / Ising discrete energy representation | 4-leaf contradiction tree in Lean (`decide`) | *Claimed upstream* (disqualified from novelty) |
| *Erdős 500* *(Reference)* | 3-Hypergraphs | Flag algebras on $K_4^{(3)}$ | Degree-stationarity differential flag SDP | Lean 4 checked SOS certificate | *Recent Sept 2026 breakthrough* (Jeong et al., arXiv:2609.27495) |

---

## 3. Caveats

1. **Erdős 834 Prior-Art Boundary**:
   - Erdős 834 part ii was claimed and proven in `plby/lean-proofs` (line 426) and was previously evaluated in `work/834/`. While its proof structure was golfed to a 4-leaf NAE tree, it cannot be submitted as a novel mathematical breakthrough.
2. **Computational Scale Limits**:
   - For Erdős 97, if the minimal counterexample requires $n > 30$ vertices or lacks cyclic/dihedral symmetry, algebraic polynomial solvers will face exponential variable scaling unless guided by geometric heuristic pruning.
   - For Erdős 86, semidefinite programs over flag algebras grow rapidly with flag size; 4-cube flag formulations require careful block-diagonalization using the hypercube automorphism group ($\mathrm{Aut}(Q_4) \cong S_4 \ltimes \mathbb{Z}_2^4$ of order 384).
   - For Erdős 273, common periods $L = \mathrm{lcm}(m_i)$ with large distinct prime factors rapidly exceed propositional SAT instance limits (clauses $\propto L$); search must focus on smooth periods or tree-based sifting.
3. **Formal Conjectures Dependency**:
   - All proposed Lean challenge bindings rely on `google-deepmind/formal-conjectures` pinned at commit `d9ce556`. Challenge statements must not be altered, per repo integrity rules (`AGENTS.md`).

---

## 4. Conclusion

1. **Prior-Art Gate Confirmation**:
   - Erdős 834 is confirmed as an upstream-claimed problem (`plby/lean-proofs:426`). It serves as an exemplary pilot for finite certificate design (SAT NAE trees and exact discrete energy bounds), but must not be treated as a novelty target.
2. **Ranked Candidate Selection**:
   - **Rank 1: Erdős Problem 86 ($100 prize)**: Optimal candidate for the DGX Spark solver environment (`cvxpy`, `clarabel`). Directly transfers control-theoretic SOS / Lyapunov certificate techniques to compute a certified rational flag algebra upper bound improving the 14-year-old $0.60318$ bound on $\pi_Q(C_4)$.
   - **Rank 2: Erdős Problem 97 ($100 prize)**: Optimal candidate for cross-discipline transfer from computer vision minimal problem solvers. Applies polynomial homotopy continuation and real algebraic geometry to search for symmetric convex polygons with 4 equidistant vertices, verifiable via rational coordinates in Lean.
   - **Rank 3: Erdős Problem 273**: Optimal candidate for discrete dynamical potential functions (Local Cut Lemma) coupled with high-performance SAT search (Kissat on Spark) to discover an exact covering system or establish a certified exclusion boundary for candidate moduli $p-1$ ($p \ge 5$).

---

## 5. Verification Method

To independently verify the observations, prior-art status, and technical findings:

1. **Verify Erdős 834 Prior-Art Gate**:
   ```sh
   grep -n "834" /Users/mike/dev/ctrl-erdos-rename/tools/data/plby_erdos.json
   # Output confirms line 426: "834,"
   ```
2. **Verify Formal Conjectures Statements**:
   ```sh
   # View frozen Lean 4 statements
   cat /Users/mike/Dev/formal-conjectures/FormalConjectures/ErdosProblems/97.lean
   cat /Users/mike/Dev/formal-conjectures/FormalConjectures/ErdosProblems/86.lean
   cat /Users/mike/Dev/formal-conjectures/FormalConjectures/ErdosProblems/273.lean
   ```
3. **Verify Catalog Triage Ranking**:
   ```sh
   cd /Users/mike/dev/ctrl
   uv run ctrl targets --tab open --top 25
   ```
4. **Verify Spark Toolchain Availability**:
   ```sh
   cd /Users/mike/dev/ctrl
   uv run ctrl doctor
   ```
   Inspect `docs/architecture.md` lines 5–15 and `docs/machines.md` lines 20–22 confirming `cvxpy`, `clarabel`, `scs`, `kissat`, and `cadical` on the Spark.
5. **Verify Recent Literature Breakthrough on Erdős 500**:
   - Inspect arXiv preprint `arXiv:2609.27495` (Jeong et al., September 2026, "A New Upper Bound for the Turán Density of the Tetrahedron"), proving $\pi(K_4^{(3)}) < 0.557789$ with Lean 4 formal certificates.
