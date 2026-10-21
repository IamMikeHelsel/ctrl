# mf13/bilevel — bilevel (K,Y)-search for the n=6 Byers–Nash question

Pod role: "bilevel search". Everything here is reproducible with
`./run.sh script.py args` (= `uv run --with numpy --with scipy --with cma --with mpmath --with clarabel python ...`).
Max 6 processes were used at any time. Date of work: 2026-10-18.

## 0. Bottom line

* **n=6: no counterexample found.  min f(K,Y) = 1 (to ~1e-14) in every run, always approached from above, never below.**
  Best values: f−1 = +3.3e-15, +3.8e-15, +6e-15, +2.8e-14, +3.4e-14 (Track A, 5 independent CMA runs, ε-barriers 0.01…0.1),
  +4e-16, +1e-15, −1.1e-15 (round-off) (Track B), ≥ +1e-15 (36-dim CMA over A with pair-extraction).
  ~1.1e5 outer evaluations in CMA runs + ~7e3 random-pair / structured-A samples, 0 samples with f<1.
* The minimum f=1 is attained on a **large full-rank "equality ridge"** (σ_min(K) up to 0.4, K,Y far from each other; the Hessian at one ridge point has 3 positive
  transverse eigenvalues and is quartic-flat in the other 14 raw directions; the ridge lies inside the 8-dim "common-T" locus below, so its dimension is ≤8 in the 11-dim pair space).
  It is **not** the rank-4 boundary and **not** only K=±Y.
* **Why f ≥ 1 on the ridge — exact (rigorous) mechanism, verified at every minimiser:**
  K and Y have a **common anticommuting orthogonal involution T** (T=Tᵀ, T²=I, TK=−KT, TY=−YT, spectrum (+1)³(−1)³).
  Then X_v=KT and X_u=YT are symmetric, ‖X_v‖=‖K‖, ‖X_u‖=‖Y‖ and **⟨X_u, L_A(X_v)⟩ = ‖Y‖²** (Lemma below), so ‖L_A|S‖ ≥ ‖L_A K‖/‖K‖
  for every A (only the first pair equation is used).
  So "same-square comparator" (the rank-4 mechanism: X_v²=−K²) is extended by *pairing it with the matching comparator for Y*.
* **n=7 positive control works** (details §3): paper matrix reproduced exactly; its pair's inner optimum has ratio 0.999588;
  and the *same* bilevel code (generic-n Track A, random start, CMA) reached f<1 in n=7 (1−1.2e-6 and still decreasing),
  while in n=6 the same code/settings stalls at 1+1e-15. The n=7 sub-1 point is a small perturbation of an n=6-type ridge point
  (K,Y kernels nearly aligned, cos=0.9988) — the negative direction uses the extra (kernel) dimension.

## 1. Verified definition (arXiv 2608.20875, fetched)

L_A(X)=AX+XAᵀ, S_n/K_n sym/skew (both L_A-invariant), ‖L_A‖=max(‖L_A|S‖,‖L_A|K‖).
Conjecture 1: **‖L_A|K‖ ≤ ‖L_A|S‖** for all A. **Counterexample = skew-restricted norm strictly larger than symmetric-restricted norm.**
n=7 example (their (4)): ‖L_A|S‖² < 1196 < ‖L_A|K‖²; floats 1195.593985 / 1196.025224. My code reproduces 1195.593985 / 1196.025224
three ways (orthonormal-basis SVD, 49×49 Kronecker restricted to sym/skew, mpmath 40 digits) — see `test_n7_control.py`, `verify_candidate.py`.
So *f<1 ⇒ counterexample* with f := sym norm of an A whose skew singular value is exactly 1 (then ‖L_A|K‖≥1>f).

## 2. Check of the theorist's reduction (all numerically verified, `test_reduction.py`)

* Compatibility: for K=diag(aJ,bJ,cJ), a random Y is incompatible (LS residual 0.3–0.6); after Gauss–Newton on the 3 moments
  (m0,m1,m2) it is compatible (residual 1e-15) with M of rank 27 (30×36 system) ⇒ affine A-family of dimension **9** — ✔.
* Cokernel of Φ(H)=(KY)H−H(YK): rank 12, cokernel spanned by K⁻¹, Y, YKY (residual 1e-15) — ✔. eig(YK) always even multiplicity (can be complex pairs) — ✔.
* (K,Y) is a singular pair: A(z)K+KA(z)ᵀ=Y, A(z)ᵀY+YA(z)=K to 1e-15, B_K v=u, B_Kᵀu=v — ✔.
* **Imprecise claim:** "1 is the top skew singular value of A(z*)". Not true in general: for random compatible pairs the top skew s.v. of A(z) is ≈2.4 (min 1.11
  in 160 samples); at the inner optimum A(z*) the skew norm k(A*) is typically 5–10 % *below* f. This does not matter: f<1 ⇒ s(A*)<1≤k(A*) is a
  counterexample, and a counterexample's top skew pair is a compatible pair with f<1. (So "f<1 ⇔ counterexample exists" is right; the top-ness check is unnecessary.)
  At the ridge minimisers 1 IS the top skew s.v. (k=s=1).
* Rank-4 boundary: f→1 from above as σ_min(K)→0 (fromA sampler: f−1 ≈ 2.6e-5…6e-6 at σ_min≈1e-3).
* The direct 30×36 null-space construction (`bl.affine_family`) is used instead of the H-parametrization (identical, handles degenerate pairs where the
  nullity jumps 9→10→19; those strata were sampled, see §4.3).

## 3. n=7 positive control

1. `test_n7_control.py`: paper A, top skew pair (K,Y) (σ=34.5836): K s.v. 0.59895,0.36582,0.08623 (×2) + 0 (matches theorist's numbers), Y s.v. 0.61437,0.32538,0.12914.
   Affine family nullity 10 (rank 39, clean gap 6e-2 vs 1e-16). Sym/skew ratio of the paper's own A: 0.99981970 (=√(1195.593985/1196.025224)).
2. Inner convex problem for the paper's pair: **f = 0.9995881048** (gap 4.12e-4, 2.3× larger than the paper's A). Saved `candidates/n7_inner_optimum_A.json`,
   mpmath-50-digit verified: ‖S‖=0.99958810477103, ‖K‖=1.0000000000000012.
3. Local outer search (generic-n Track A, CMA from the canonicalised paper pair, `n7_local.py`): 0.99959 → **0.999367** in 30 gens; start perturbed by 10 %: 0.999403; perturbed 30 %: slides to the ridge (1.00003) ⇒ the n=7 basin is narrow.
4. **From random starts**: Adam-on-gap (the paper's method, `adam_gap.py`): 0/12 successes in n=7 (as the paper itself says it only found n=9 directly).
   36-/49-dim CMA over A with pair-extraction (`track_fromA.py`): reached 1+1e-8 only (stopped early).
   **Generic-n Track A (`track_a_gen.py 7 …`, pop 24, σ0=0.5, ε=0.02), seed 1: after ≈290 generations (≈25 min) it crossed 1:
   f = 0.9999999860 → 0.99999978 (verified, candidates/n7_bilevel_found_A.json: ‖S‖=0.99999977755, ‖K‖=1.0000000000000016, mpmath-50-digit) → 0.9999988 and still decreasing**
   (seed 2 reached 1+6e-10 at gen 300, not crossed yet). Barrier solver at that point: pair residual 3e-15, rank gap clean (1.2e-1 vs 7e-16).
   Structure of this n=7 solution: top sym s.v. double (1,1), first singular vectors exactly same-square (|Xv²+K²|=0, XK+KX=0) i.e. it sits next to an n=6-type ridge point,
   K,Y kernels nearly parallel (cos 0.9988) — the sub-1 direction is the kernel/extra-dimension coupling.
   ⇒ The pipeline *can* cross the ridge when a negative direction exists; in n=6 it never did (stalls at 1+1e-15 in 7+ independent runs, 400–800 generations each).

## 4. n=6 results

### 4.1 Implementation (files)
* `bl.py` generic-n: bases, operator tensors, `affine_family` (nullspace of the 2·C(n,2)×n² pair system), norms, full-Kronecker cross-check, `skew_top_pair`.
* `barrier.py` custom log-barrier solver for min_z σ_max(B0+ΣzB_r), barrier −logdet(t²I−BᵀB) (2m-self-concordant); 30–40 ms for n=6 (vs 80–400 ms cvxpy/clarabel), agrees with Clarabel/cvxpy to 1e-9
  (`prof2.py`, `test_inner_speed.py`). nit≈100–140 at the ridge points (cap raised to 3000 after n=7 runs hit the old 400 cap; n=6 results unaffected, checked by `chk_nit.py`).
* `n6.py` canonical K, analytic moment Jacobian, Gauss–Newton projection of Y onto m0=m1=m2=0 (5–6 its to 1e-16).
* `track_a.py` Track A: 17 outer vars (u,v → a:b:c with a²+b²+c²=½; 15 raw Y coords → normalise → project), objective f + 50·(max(0,ε−σ_min(K))+max(0,ε−σ_min(Y))); CMA-ES.
* `track_b.py` Track B: Y=QKQᵀ, Q=U diag(±1…)Uᵀ (k=1,2,3) or Q skew-orthogonal ("J"), U=expm(skew(15)).
  Checked: Y=±QKQᵀ with Q²=±I gives zero moment defect identically (resid 0, nullity 9) — ✔; general orthogonal Q does not (moment defect 0.02–0.03).
* `track_fromA.py` CMA over A (36 vars, optional block structure) with f(top skew pair of A); `track_a_gen.py` generic-n Track A (compatibility by Gauss–Newton on LS-unsolvable residual).
* `landscape.py`, `strata.py` (structured A: blocks 3+3,2+4,4+2,2+2+2,5+1,diag,commuting-with-J6,sym,skew,normal,tri,low-rank,nilpotent,…), `track_fixedK.py` (fixed K shape, many Y restarts).
* `verify_candidate.py` (mpmath, independent of search code), `make_*_candidate*.py`, `summarize.py`, `analyze_*.py`, `hessian.py`, `linescan.py`, `fss.py`, `gcert.py`.

### 4.2 Minima (CMA, `runs/*.best.json`; `summarize.py`)
| run | f−1 | σ(K) (a,b,c) | σ(Y) | eig(YK) (distinct, each ×2) | s(A*)−1 / k(A*)−1 |
|---|---|---|---|---|---|
| A ε=0.02 s1 | +3.3e-15 | .518 .480 .029 | .545 .450 .030 | −.238, .0009, .249 | 3e-15 / −6e-16 |
| A ε=0.01 s21 | +3.8e-15 | .651 .201 .189 | .651 .201 .189 | −.423, −.039, .037 | 4e-15 / −1e-16 |
| A ε=0.05 s2 | +6.0e-15 | .511 .380 .307 | .480 .444 .269 | −.122, .036∓.164i (cplx) | 6e-15 / −1e-16 |
| A ε=0.01 s31 | +3.4e-14 | .457 .445 .305 | .503 .373 .328 | −.174, .007∓.148i | 1e-12 / 7e-16 |
| A ε=0.1 s3 | +2.8e-14 | .581 .384 .120 | .584 .380 .121 | −.200, −.024, .148 | 3e-14 / −6e-16 |
| B (k=1) | +1.3e-15 | .413 .409 .403 | = | −.170, −.162, .167 | |
| B (k=2) | −1.1e-15 (round-off) | .481 .416 .309 | = | −.173, .096, .230 | |
| B (k=3) | +4.4e-16 | .408 .408 .408 | = | −.076∓.149i, .167 | |
All have K,Y full rank (σ_min(K)=0.029–0.41, 3 distinct σ except B), nullity 9, YK diagonalisable with 3 distinct eigenvalue pairs (real or one complex pair).
⟨K,Y⟩ ranges −0.04…0.33, ‖Y∓K‖≈1.3–1.6, i.e. these are NOT the trivial K=±Y calibration points.
At all of them s(A*)=k(A*)=1 (to 1e-12): they are points of the **s=k equality ridge** the KV paper mentions, but with full-rank K,Y.

### 4.3 Landscape
* Random compatible pairs (K random a:b:c, Y Gaussian projected; N=2000): f quantiles (0,1,5,10,25,50,75,90,100 %) =
  1.016, 1.124, 1.244, 1.337, 1.610, 2.203, 3.360, 5.886, 41.5. Never <1.0158. (Large f: random pairs are far from top pairs.)
* "Natural" sampler (random A → top skew pair → canonical K; N=2000): quantiles 1.00001, 1.0001, 1.00046, 1.0011, 1.0045, 1.0203, 1.079, 1.147, 1.354; min 1+6.3e-6;
  f−1 correlates with σ_min(K) (rank-4 boundary, median f−1 = 5.9e-3 for σ_min<1e-3 … 9.8e-2 for σ_min∈[0.1,0.5)). 0/4000 below 1.
* Structured A (`strata.py`, 18 classes × 150, including degenerate strata with nullity 10 and 19: block-diagonal, normal, symmetric, skew, …): 0 below 1, min = 1.00000000.
  Nullity 19 occurs for diag/sym/normal A (K,Y with repeated singular values), f=1 there too.
* Local structure at a ridge minimiser (`hessian.py`, `linescan.py`, run A ε=0.05 s2, 17 raw coords): 3 eigenvalues 0.069, 0.082, 0.163 (transverse), rest |λ|<1e-4 (FD-noise level
  of a quartic-flat valley); along all 14 other eigendirections f−1 ≥ +5e-15 for steps 1e-3…1e-1, growing like t^4 (1e-13 @1e-3, 2e-11 @1e-2, 1e-7 @1e-1) — i.e. straight lines leave a curved 8-dim ridge quadratically.
  ⇒ transversally (3 directions) a strict quadratic minimum; in the other directions f−1 grows ~t⁴ (so the Hessian alone does not give the dimension of {f=1}); no negative direction seen (CMA at σ≈1e-3 around it also found none).
* Fixed-K searches (`track_fixedK.py`): K shape of the n=7 solution (a:b:c = .599:.366:.086), 12 random Y restarts × 60 gens: min f = 1.0000031.

### 4.4 Why f=1 at the ridge (proof content)

**Lemma (common-involution certificate; rigorous, verified numerically in `test_lemma.py`).** Let A be arbitrary, K skew, Y:=AK+KAᵀ (skew). Suppose T=Tᵀ, T²=I, TK=−KT, TY=−YT.
Then KT, YT are symmetric, ‖KT‖_F=‖K‖_F, ‖YT‖_F=‖Y‖_F and
⟨YT, L_A(KT)⟩ = −tr(YAK)−tr(YKAᵀ) = −tr(Y²) = ‖Y‖²  (use TYKT=YK twice).
Hence ‖L_A|S‖ ≥ ‖Y‖/‖K‖ = ‖L_A(K)‖/‖K‖. In particular if K is a skew maximiser and Y=L_A(K) has a common T with K, a symmetric maximiser exists.
For a compatible pair this gives f(K,Y)≥1 exactly (equality attained: equality ⇔ L_A(KT)=YT).

*Where T comes from:* T = P_V − P_{V⊥} with V a 3-dim subspace with KV=V⊥ (for distinct a,b,c: V = span of one real vector from each 2-plane of K → a 3-torus T³_K of such T);
likewise a 3-torus T³_Y for Y. A common T is an intersection of two 3-dim families in the 9-dim Grassmannian Gr(3,6) ⇒ expected codim 3 in the 11-dim pair space, i.e. an 8-dim "common-T locus".
Explicit parametrisation (`commonT_family.py`): in the eigenbasis of T, K=[[0,−Cᵀ],[C,0]], Y=[[0,−Dᵀ],[D,0]] (C,D 3×3): 18 params −(|K|=|Y|=1: 2) −(m1,m2: 2) −(O(3)×O(3) gauge: 6) = 8 ✓.
**Important correction found there:** on the common-T locus f≥1 (Lemma) but f is *not* identically 1: in 25 Gauss–Newton-sampled common-T pairs f−1 ranged 3e-14 … 5.6e3
(5/25 had f=1 to <2e-10, e.g. pairs with σ(K)=σ(Y) or with matching c and a²+b²; the others f−1 = 1e-2…10). So the minimisers (f=1) are the part of the common-T locus where, in addition, the inner optimum A* satisfies L_A(KT)=YT with
[T,A*]-compatible structure (equality in Cauchy–Schwarz); I have not derived the exact extra condition.
Numerically (`common_T.py`): at the minimisers of Track A (all 5) and Track B (k=2,3) the top symmetric singular vectors are exactly X_v=KT, X_u=YT with the *same* T
(|T_v−T_u|=5e-7…4e-5, T symmetric, orthogonal, anticommutes with K and Y to 1e-6, spectrum (−1)³(+1)³), the top sym s.v. is simple (=1) and the dual certificate is the single term X_u X_vᵀ.
Dual formulation of f (derived, checked): with M:=pair map, Range(Mᵀ)={Z₁K+YZ₂ : Z₁,Z₂ skew}; f = max{ −⟨Z₁,Y⟩−⟨Z₂,K⟩ : N(Z₁K+YZ₂) ≤ 1 },
N(P)=min‖W‖_* s.t. Σ W_ij S_iS_j = P (S_i orthonormal sym basis). The Lemma is the choice Z₁=−Y, Z₂=0: P = X_uX_v = YTKT = −YK = Z₁K, with value ⟨Y,Y⟩=1 and N(P)≤‖X_u‖‖X_v‖=1.
Related exact identity (verified `test_identity.py`): for any A, skew K, T anticommuting with K, Y=L_A K, Y_c=½(Y+TYT):
‖L_A(KT)‖² = ‖Y‖² + 4 tr(Y_c K Aᵀ) + ‖K[T,Aᵀ]‖²  (so the rank-4/same-square lemma is the case where the cross term is made ≥0 by choice of T).

**What is NOT proved:** f≥1 for pairs *without* a common T (generic compatible pairs, f∈(1,∞) there). The single-term / R-type same-square dual class is not enough for them
(`fss.py`: restricted dual value 0.74–0.95 <1 for random pairs while f≈1.4–6), and the Rayleigh class (X_u=X_v, `gcert.py`) gives 0.5–2.2. Generic optimal duals are multi-term with non-same-square X.
So there is no proof of n=6 from this; the evidence is numerical: inf f=1 attained exactly on the "common-T" ridge, quadratic growth off it.
A cheap averaging argument over the T³_K torus gives E‖L_A(KT)‖² = ‖Y‖² − ‖Y_off‖² + E‖K[T,Aᵀ]‖² and falls short by a factor 2 — consistent with n=7 failing.

## 5. Caveats
* CMA = local/stochastic; the n=7 negative region needed ≈300 generations to reach from random starts although it sits right next to the ridge, so absence of f<1 in n=6 after 400–800 generations ×7 runs
  (+ structured/degenerate sampling) is strong but not exhaustive evidence. A rigorous n=6 statement needs a proof (e.g. certificate for non-common-T pairs).
* Exactly degenerate pairs (nullity 10/19) are measure-zero; sampled via structured A (§4.3) but not optimised over.
* Inner solver returns an *upper bound* σ_max(B(z)) ≥ f; n=6 results use tol 1e-9…1e-13 and nit≪cap, so f<1 cannot be masked at the 1e-8 level at the reported points.
  (n=7 runs used the old 400-iteration cap: their reported f is slightly pessimistic; re-solved candidate values are lower — e.g. 0.99999978 vs logged 0.99999993.)

## 6. Candidates
No n=6 candidate (f<1) exists, so `candidates/` has: `n7_paper_integer_A.json`, `n7_inner_optimum_A.json`, `n7_bilevel_found_A.json` (positive controls, verified with
`./run.sh verify_candidate.py FILE 50`) and `n6_ridge_reference_A.json` (s=k=1 within 6e-15, verifier says NOT a counterexample: gap −5.7e-15).

## FINAL RESULTS OF THE LONG RUNS (same code `track_a_gen.py`, same settings, ε=0.02, 600–700 gens)

| run | n | final f (=sym norm; skew = 1) |
|---|---|---|
| AG_n7_s1 | 7 | **0.9955476400** (gap 4.45e-3; mpmath-verified, `candidates/n7_bilevel_found_s1_A.json`) |
| AG_n7_s2 | 7 | 0.9970671799 |
| AG_n6_s1 | 6 | 1.0000000000000007 (sym 1.0000000000000009, skew 0.9999999999999998) |
| AG_n6_s2 | 6 | 1.000000000000006 |
| track_a.py 41 (ε=0.3) | 6 | 1.0000000000030 |
| track_fixedK (n=7 K-shape, 12 Y-restarts × 60 gens, n=6) | 6 | min 1.00000075 |

* n=7 (positive control, random start, no knowledge of the paper) keeps descending as gens grow (from 0.9999 → 0.9955), so the bilevel search finds strict
  counterexamples at n=7 easily; with identical code/budget n=6 stays at exactly 1 (to 1e-15) in every run. No f<1 candidate at n=6 → `candidates/` has no n=6 counterexample.
* Correction to the Hessian bullet above: transversal curvature is positive in 3 directions; the ridge dimension ({f=1}) is ≤ 8 (inside common-T locus), exact dimension not determined.
