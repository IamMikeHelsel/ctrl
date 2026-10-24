# BN6 — Byers–Nash symmetric-maximizer conjecture at n = 6 (lane BN6, wave 2)

Code and data: `docs/research/2026-10-wave2/bn6/`
(numpy, scipy, cvxpy/Clarabel, sympy, Fraction). Each script stands alone and writes its JSON next to itself.

## 0. Bottom line

* **No n = 6 violation found.** 144 monotone SDP-dual ascents at n = 6 (independent re-implementation)
  never exceeded k/s = 1 − 1e-12. The same code reaches k/s = 1.0077887 at n = 7 from a random start.
  This is numerical evidence, not proof.
* **The "single remaining cross-term inequality" is false, not merely tight, in every comparator
  form I could formulate.** The STATUS doc names it as the last step to close n = 6 in Lean. Three failures:
  1. The 8 Lean comparators K·T_r, K·G_r fail by up to 22%. Worst found: ratio 0.78 to 0.80.
  2. The full 27-component same-square class fails by about 8% (0.917). This is the pod's own exact
     certificate, which I reproduced.
  3. **New: even the best linear combination of all symmetric matrices that are block-diagonal in the
     Darboux frame of the top skew singular vector fails.** I found ratio 0.970 with a near-degenerate
     top skew value, and 0.9952 when a 3% spectral gap is enforced. A third failure sits near the
     rank-4 atoms: 1 − 3.6e-6 at a 13% gap. All three are backed by exact certificates for a rounded
     K̃ (§5.4, §5.5).

  Every comparator the Lean modules build (T_r, G_r, the canonical U_r pairings, the same-square class)
  lies in that block-diagonal span. No version of the planned inequality can close n = 6.
* **Adding rank-one comparators does not rescue it either (numerical).** Add the rank-one comparators
  S = vvᵀ to the block-diagonal span. This fixes the large failures. Adversarial search still finds
  failures of about 6e-3 for full-rank K with a 2% top-skew gap, and 1e-4 to 4e-6 near the rank-4
  atoms (§5.5).
  Near the rank-4 atoms, where Lean already proves BN, the block-diagonal comparators lose only at
  second order. So a local lemma around the atoms must use symmetric directions outside this span.
* **Two corrections to ctrl's docs.**
  - `STATUS_AND_ROADMAP.md` states s, k as **minima** (sep). The Lean code and the literature use
    **operator norms** (maxima). The min version is not the open problem: it fails at n = 3 (§1).
  - The STATUS doc misquotes the 8-involution identity. The Lean statement is correct (§2).

## 1. Definitions used, and reconciling the two formulations

* ctrl Lean (`Research.ByersNashDuality.lyap`): L_A(X) = AX + XAᵀ.
  The user's form AᵀX + XA is L_{Aᵀ}. Since L_{Aᵀ} = L_A* and Sym and Skew are invariant, the restricted
  norms agree. Everything below uses AX + XAᵀ.
* s(A) = ‖L_A|_{Sym_n}‖ and k(A) = ‖L_A|_{Skew_n}‖ (Frobenius operator norms, i.e. maxima).
  **BN(n): k(A) ≤ s(A) for all A.** By orthogonal decoupling, BN(n) says ‖L_A‖ is attained on a
  symmetric matrix: the "symmetric-maximizer conjecture".
* This is the formulation of:
  - the ctrl Lean modules and pod `PROOF_SKETCH.md`;
  - Kressner–Vandereycken, arXiv:2608.20875. I read the copy in the ctrl snapshot at
    `$C/ctrl-devsnapshot/work/pod/mf13/proof/refs/kv.pdf`; arxiv.org itself is blocked. Its abstract says
    the norm conjecture holds for n ≤ 5, fails for n = 7 via an integer 7×7 matrix, fails for every
    n ≥ 7 by direct sums, and "the case n = 6 remains open".
* `STATUS_AND_ROADMAP.md` writes s, k as **minima** over unit symmetric/skew matrices. That is a
  different problem, and false in both directions (`log_minform.txt`, 3000 Gaussian A per n):
  - "k_min ≤ s_min" fails for about 97% of A at n = 3 and n = 6.
  - The symmetric-minimizer statement s_min ≤ k_min fails at n = 3 for 38/3000 A (worst relative gap
    10.9%) and at n = 6 for 71/3000. It never fails at n = 2.
* Explicit operator matrices: `core.op_mats` builds L_A on Sym_n (dim n(n+1)/2) and Skew_n
  (dim n(n−1)/2) in orthonormal bases E_ii, (E_ij ± E_ji)/√2.

## 2. Reproduction of known facts

| check | result |
|---|---|
| Orthogonal decoupling (`lyap_symm_skew_orthogonal_decomp`): I⊗A + A⊗I in the basis [Sym; Skew] is block-diagonal, blocks equal to the restricted matrices, n = 3..7 | off-block ≤ 1.1e-16 |
| Identity I2: ‖L_A(KT)‖² = 4‖H_c(T)‖² + ‖Y_a(T)‖² | agrees to 1e-14 |
| Lean `eight_involution_byers_nash_identity`: Σ₈ ‖L_A(KT_g)‖² = 16‖H‖² + 16‖isoH‖² + 4‖Y‖² + 4‖Y_d‖² | confirmed (418.569 = 418.569) |
| STATUS-doc version: "Σ₈ = 8‖L_AK‖² − 6‖Y_d‖² + 2‖Y_off‖²" | **wrong** (gives 467.04 on the same data) |
| n = 4, 5: 300 L-BFGS multistarts each, maximising k²/s² with exact top-singular gradients | max k/s = 1 − 7e-11 (n = 4), 1.000000000000 (n = 5); none > 1 |
| n = 7, Kressner–Vandereycken integer A (copied in the pod's `test_n7_control.py`) | **[exact]** s² < 1196 < ‖L_A K̃‖²/‖K̃‖² ≤ k², k/s ≈ 1.00018 (`verify_kv.py`, Fraction LDLᵀ) |
| n ≥ 7: A ⊕ 0 | s, k unchanged for n = 8, 9, 10 (numerical) |
| n = 7, the pod's stronger integer certificate `cert_n7.json` | **[exact]**, independent code (`verify_n7.py`): k²/s² > 1.0146, so k/s > 1.00727 |
| n = 7 positive control for my SDP ascent | from the pod's integer A: 1.0073578 → 1.0077887. From random Gaussian starts: 1 of 3 reached 1.0077697, the other 2 stalled at 1 − 1e-8 |

Two caveats:
* Plain L-BFGS on k²/s² found no n = 7 counterexample in 5 starts; it stalls just below 1 on the
  nonsmooth ridge. Only the SDP-dual ascent is a credible search tool here, which is why §3 relies on it.
* I did not rebuild a counterexample *family*. The paper's n ≥ 7 family is the direct sum with zero
  blocks, which I checked numerically.

## 3. n = 6 search

Search tool: a monotone SDP ascent (`gauge.py`), an independent re-implementation of the pod's Theorem 1/5 idea:
* For symmetric U, V and skew Y, K: ⟨U, L_A V⟩ = 2⟨A, UV⟩ and ⟨Y, L_A K⟩ = −2⟨A, YK⟩.
* Hence s(A) = 2‖B(A)‖₂ with B_ij = ⟨A, S_iS_j⟩, and sup_A k/s = max over unit skew pairs of N(−YK).
* N(P) = max{⟨A, P⟩ : ‖B(A)‖₂ ≤ 1} is a 21×21 spectral-norm SDP in 36 variables.
* One iteration: (K, Y) = top skew singular pair of L_A, then A ← argmax N(−YK).
  This satisfies k/s(A_t) ≤ N ≤ k/s(A_{t+1}), so the ratio never decreases.

| batch | starts | max k/s | limits |
|---|---|---|---|
| A (`ascent_n6_0.json`): Gaussian, sparse, nilpotent-ish, Cauchy, low-rank, plus 36 compressions of the n = 7 counterexample to 6-dim subspaces (random, and nearly orthogonal to ker K or ker Y) | 96 | 0.9999999999990 | all → 1 from below; 26 full-rank limits (σ₃/σ₁ ≤ 0.16), rest rank 4 or rank 2 |
| B (`ascent_n6_b.json`): perturbations (0.05–0.5) of full-rank limits, of the pod's SS-fail matrix, and of comparator-adversarial points | 48 | 0.9999999999895 | full-rank limits up to σ₃/σ₁ = 0.41 |

* Every full-rank limit lies on the **common-T locus**: there is a symmetric involution anticommuting
  with both K and Y. The defect min_T ‖TYT + Y‖/‖Y‖ is ≤ 3e-5 in all 10 classified limits, at ascent
  tolerance. The other limits are rank 4 or rank 2.
* Both kinds are cases ctrl/pod has already proved (Lean rank-4 exclusion; common-T lemma).
* This agrees with the pod's independent result: 54 ascents plus 18,857 starts, maximum 1, attained on
  the same atom set.
* **Best near-violation:** k/s = 1 − 1.0e-12, reached on the known equality set
  (K = diag(0.6188J, 0.3420J, 0.0121J), common-T defect 5e-6). There is no off-atom near-miss.

Interpretation (evidence only):
* In n = 6 the global maximum k/s = 1 looks like it is attained exactly on the settled atom set.
* n = 7 has a clean basin above 1 that the same method finds from random starts.
* Compressing the n = 7 optimum to 6 dimensions always loses the excess. This matches the pod's
  Theorem 3: n = 7 counterexamples need ker K ≠ ker Y.

## 4. Rationalisation / exact verification of an n = 6 violation

Not applicable, since no violation was found. The exact machinery is ready (`exact.py`: Fraction Gram
matrices and LDLᵀ for s² < c and for k² ≥ ‖L_A K̃‖²/‖K̃‖²). It verified both n = 7 certificates in under 2 s.

## 5. The documented "J vs {I₂,F,G} cross-term" gap (step 5)

### 5.1 What exactly is claimed
No file states the inequality itself. I checked the Lean files, README, STATUS, IDEA_PORTFOLIO and
frontier docs. What exists:
* The Lean criterion `eight_involution_dominance_of_commutator_or_diag`: if
  ‖Y_off‖² ≤ 4‖H‖² + 4‖isoBlockTrace H‖², one of the 8 comparators K·T_r, K·G_r dominates.
  Here K = diag(aJ, bJ, cJ), Y = L_A K, H = (AK − KAᵀ)/2.
* The open case is therefore ‖Y_off‖² > 4(‖H‖² + ‖isoH‖²). The STATUS doc says this case should be
  closed by combining the 8 comparators, the 4 canonical U_r and the plane swaps W_pq.
* The caller's regime ½‖Y_off‖² > ¾‖Y_diag‖² does not appear in any repo file. Algebraically it equals
  Σ_r‖U_r‖² > ‖Y_diag‖², by `canonical_four_term_norm_identity`.

Any argument in this family ends by producing a symmetric comparator V, or pairings
Σ_r⟨U_r, L_A V_r⟩ = ‖Y‖², where every V is built from involutions anticommuting with K. For distinct
moduli a, b, c, all of these are **block-diagonal** in K's Darboux frame. The plane swaps W_pq and P_F
anticommute with K only when two moduli are equal.

A pairing bound gives at most ‖Y‖² ≤ Σ‖U_r‖·‖L_A V_r‖ ≤ s_BD·Σ‖U_r‖‖V_r‖. So the strongest conclusion
any such argument can reach is

  **k(A) ≤ s_BD(A) := ‖L_A restricted to Sym ∩ comm(K²)‖**, where K is the top skew singular vector.

Sym ∩ comm(K²) is 9-dimensional and equals the block-diagonal symmetric matrices in the Darboux frame.

### 5.2 Diagnostics (`gap.py`)
For each A, I put the top skew singular vector K in Darboux form and computed:

| quantity | definition |
|---|---|
| c8 | max over the 8 Lean comparators of ‖L_A S‖²/‖L_A K‖² |
| cSS | the same max over the full same-square class (27 components; ±aI or a·reflection per plane) |
| cT6 | s²/k² restricted to the span of torus comparators (traceless block-diagonal, 6-dim) |
| cBD | s²/k² restricted to all block-diagonal symmetric matrices (9-dim) |
| lean8 | (4‖H‖² + 4‖isoH‖²)/‖Y_off‖². The Lean criterion holds iff lean8 ≥ 1 |
| regime | ½‖Y_off‖² / (¾‖Y_d‖²). The caller's gap regime is regime > 1 |

Always c8 ≤ cSS ≤ cBD and cT6 ≤ cBD. A comparator proof for that A needs the relevant value ≥ 1.

### 5.3 Results
| point | k/s | top-skew gap k₂/k₁ | moduli (normalised) | c8 | cSS | cT6 | cBD | lean8 | regime |
|---|---|---|---|---|---|---|---|---|---|
| pod SS-fail matrix (`cert_ss_fail.json`) | 0.893 | 0.998 | .532/.403/.233 | 0.795 | **0.917** (reproduces pod value 0.91703) | – | 1.115 | 0.158 | 7.08 |
| adversarial, full-rank constraint (`adv_fr.json`[1]) | 0.903 | 0.99945 | .506/.429/.245 | 0.880 | 0.956 | 0.956 | **0.970** | 0.138 | 3.28 |
| adversarial, gap enforced k₂/k₁ ≤ 0.97 (`adv_fr2.json`, 8 runs) | – | 0.970 | e.g. .634/.250/.190 | 0.78–0.96 | – | 0.9945–0.9988 | **0.9952–0.9991** | 0.21–0.45 | 0.81–283 |
| adversarial, gap enforced k₂/k₁ ≤ 0.90 (`adv_fr2.json`, 8 runs) | – | 0.900 | e.g. .635/.246/.190 | 0.83–0.94 | – | 0.99976–1.0016 | **0.99976–1.0017** (7/8 below 1) | 0.33–0.45 | 0.83–655 |
| adversarial, no constraint (`adv_bd.json`) | – | 0.68–0.96 | K tends to rank 2 or 4 | 0.97–0.999 | – | – | → 1.0000 from above | – | – |
| n = 6 ascent limits (k/s ≈ 1) | ≈ 1 | 0.80–0.99 | atoms | 0.82–1.0 | – | – | 1.000000 | – | – |

Findings:
* **Verdict on the cross-term step: false, with margin.** No inequality of comparator type can close it.
  - c8 < 1 occurs with margin up to about 22%.
  - cSS < 1 up to about 8% (the pod's exact SS-fail certificate).
  - Even the 9-dim block-diagonal span fails: cBD = 0.970 near a top-skew crossing, and 0.995 with a 3%
    gap. Reproduce with `adv_fr2.json` and `cert_bd.py`.
* The failures are not confined to the caller's regime: one failing point has regime = 0.81.
* At every failing point the Lean criterion is far off (lean8 = 0.14–0.45).
* **Not a degeneracy artefact, but the margin shrinks with the gap.** K is full rank with
  well-separated moduli, and the top skew singular value is simple. The minimisers drift toward
  near-crossings of the top two skew singular values. The best cBD found by enforced gap:

  | enforced k₂/k₁ | best cBD |
  |---|---|
  | 0.9994 | 0.970 |
  | ≤ 0.97 | 0.995 |
  | ≤ 0.90 | 0.99976 |

  So the block-diagonal span fails everywhere it was tested, with large margins only near top-skew crossings.
  - A gap condition does not save it. Near the rank-4 atoms it also fails at gap k₂/k₁ = 0.867, by
    3.6e-6 with an exact certificate (§5.5).
  - The exact obstructions are: the pod's cSS certificate, and my three cBD certificates (§5.4, §5.5).

### 5.4 Exact obstruction certificates (`cert_bd.py`, `cert_bd_adv_fr_1.json`, `cert_bd_adv_fr2_1.json`)
Inputs: a rational A (entries /10⁶) and a rational skew K̃, the rounded top skew singular vector.
Cosine with the float top vector is 1 − 1e-13.

* Sym ∩ comm(K̃²) is computed exactly with a sympy nullspace (dimension 9). The 9×9 Gram matrices are
  exact rationals.
* **[exact]** c·G − M ≻ 0 by Fraction LDLᵀ, with:
  - c = (1 − 1/50)·‖L_A K̃‖²/‖K̃‖² for the first point;
  - c = (1 − 1/1000)·‖L_A K̃‖²/‖K̃‖² for the gap-enforced point (top-skew gap 0.9703).
* So ‖L_A S‖ < ‖L_A K̃‖/‖K̃‖ · ‖S‖ for every S ∈ Sym ∩ comm(K̃²).
* What is numerical: that K̃ approximates the true top skew vector closely enough for the conclusion to
  transfer. Same status as the pod's SS-fail certificate.
* These A satisfy BN with margin (k/s ≈ 0.90). The certificate says the comparator *method* fails,
  not the conjecture.

### 5.5 Block-diagonal span ∪ rank-one comparators (numerical): better, still insufficient
At the cBD-failing points, the top symmetric singular vector is nearly rank one: eigenvalues
(−0.992, −0.055, …, 0.117). Only 42% of its energy is block-diagonal.

Rank-one comparators have a closed form: ‖L_A(vvᵀ)‖² = 2(‖Av‖² + (vᵀAv)²) for unit v.
Define cHyb = max(s_BD², s_R1²)/k², with s_R1² = max over unit v of 2(‖Av‖² + (vᵀAv)²).

* At the four adv_fr points, cR1 = 1.006–1.223 and cHyb = 1.006–1.223. At the SS-fail matrix, cHyb = 1.185.
* Over 200 random A, the minimum cHyb was 1.121.
* Adversarial minimisation of cHyb (`adv_hyb.py`, `adv_hyb.json`), unconstrained runs:
  - cHyb = 0.99538 (cR1 0.9945) at a full-rank K at a top-skew crossing (k₂/k₁ = 1.0000, moduli .587/.364/.152);
  - cHyb = 0.999902 (cR1 0.9947) at gap 0.938, moduli .701/.082/.041;
  - cHyb = 0.9999964 (cR1 0.9921) at gap 0.867, moduli .702/.079/.033, k/s = 0.99971.
* The last point has a **[exact]** block-diagonal obstruction certificate (`cert_bd_adv_hyb_snap_2.json`):
  denominators 10⁹, s_BD(K̃)² < (1 − 3·10⁻⁶)·‖L_A K̃‖²/‖K̃‖². Its rank-one margin (0.8%) is numerical.
* Conclusions:
  - Failures concentrate near the rank-4 atom set, and near crossings of the top two skew singular values.
  - Near the atoms the comparator deficit is tiny but nonzero.
  - Even infinitesimally close to the settled rank-4 case, the optimal symmetric partner is not in
    block-diagonal ∪ rank-one. A local lemma must allow general symmetric directions.
* Gap- and rank-constrained runs (k₂/k₁ ≤ 0.98, σ₃/σ₁ ≥ 0.25): 4 of 10 jobs finished before I
  stopped the batch, and all 4 fail. cHyb = 0.99369, 0.99623, 0.99666, 0.99702, with moduli e.g.
  .615/.302/.174. The adversary balances the two families: cBD ≈ cR1 at these points. So the hybrid
  family fails by about 0.6% for full-rank, well-conditioned K with a simple top skew singular value.

## 6. Guidance for closing (or abandoning) the Lean proof

1. **Stop pursuing the comparator cross-term as stated.** The 8- or 12-comparator route, and every
   refinement that keeps comparators block-diagonal in K's frame, is refuted by exact-arithmetic
   obstruction certificates (§5.3–5.4).
   - Fix the STATUS doc's formulation (min → max).
   - Fix the misquoted 8-involution identity.
   - Withdraw "only a single cross-term inequality remains" and "90% complete".
2. **The proved results stay useful as case lemmas.** These remain valid:
   - rank ≤ 4 exclusion;
   - the common-T lemma;
   - the 8-comparator criterion in its own regime (lean8 ≥ 1);
   - Lean files for rank ≤ 4 and common-T pairs.

   These are exactly the sets where the n = 6 maximum k/s = 1 is attained (§3).
3. **No small comparator family suffices, as far as these numerics show.**
   I tested, adversarially:
   - fixed involution comparators;
   - the same-square class;
   - the 9-dim block-diagonal span;
   - block-diagonal plus all rank-one vvᵀ.

   All fail somewhere. "For all K" versions fail outright: k ≤ s_BD over all skew K, not just the top
   one, has ratio 0.763 at moduli (1, 1.02, 0.89) (`t_strongBD.py`, `log_strongBD.txt`).
   Any proof must use K being the *top* skew singular vector (L_A*L_A K = k²K), together with symmetric
   partners outside these families.
4. **The only fully general route I can see is the pod's static form.** BN(6) ⇔ N(−YK) ≤ ‖Y‖‖K‖ for
   all K, Y ∈ Skew_6. Modulo O(6) and the stabiliser torus this is 13 parameters. Equality holds exactly
   on the settled atom set, with quadratic decay 1 − N ≈ cε², c ∈ [0.044, 0.58] (pod).
   A kernel-checked proof would combine:
   - a local lemma near the atoms (second-order, using the I2 and common-T identities);
   - a finite cover of the rest by exact rational SDP certificates. Primal decompositions
     YK = Σ c_k U_kV_k with full-rank, non-same-square factors; the pod showed atoms alone do not suffice.

   This is a large but well-posed computation. The exact Gram/LDLᵀ checker here is the verifier
   component it would need.
5. **For a counterexample.** Nothing in this lane or in the pod's runs suggests one exists at n = 6.
   Any search should target invertible K, Y off the common-T locus with dim(range K + range Y) = 6.
   Every ascent here was attracted back to the atom set.

## 7. Evidence vs proof; limits of this lane
* **[exact]**: the two n = 7 certificates; the three BD-obstruction certificates. The latter are exact
  given the rounded K̃; their transfer to the true top singular vector is numerical.
* Everything else is floating-point numerics (cvxpy/Clarabel SDPs, LAPACK SVDs, local optimisation).
  This includes "no n = 6 violation", "limits lie on the atom set" and the rank-one half of the hybrid-family failures.
* **Compute was constrained.** The 4 cores were shared with other lanes (load average 20–33). I stopped
  the n = 6 L-BFGS multistart batch early, since SDP ascent is far stronger. Total ascents: 144 at n = 6,
  4 at n = 7.
* **Not verified:**
  - Chen–Tian's n ≤ 5 proof. I only reproduced the numerics; their SIAM note is
    https://epubs.siam.org/doi/10.1137/140974031, seen only as a search result.
  - The arXiv page itself. The PDF metadata and abstract come from the copy in the ctrl snapshot.
* No Lean was compiled in this lane.
