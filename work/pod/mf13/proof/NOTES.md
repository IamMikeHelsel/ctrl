# mf13/proof — prover notes (n = 6 Byers–Nash)

Run anything with `./pfx.sh script.py args` (= `uv run --with numpy --with scipy --with cvxpy --with clarabel --with mpmath --with cma python`).
Background jobs: `./launch.sh LOGNAME script.py args` (own session via setsid; plain nohup jobs were being reaped).
Logs in `logs/`. Max 4 processes used.

## 0. Literature: how Chen–Tian works, and where it stops

* KV arXiv 2608.20875 fetched (abstract page + PDF in `refs/kv.pdf`). It is only the counterexample (integer 7×7 A, LDLᵀ certificate
  that 1196·D_S − B_Sᵀ D_S B_S ≻ 0, explicit integer skew K with ‖L_A K‖²/‖K‖² > 1196) plus a direct-sum padding for n ≥ 7.
  No structural explanation of why 7 works.
* Chen–Tian 2015 (SIAM, paywalled) not accessible; their 2016 follow-up (Operators & Matrices 10:611, `refs/oam-10-35.pdf`,
  open access) reproduces the technique. **Lemma 2.2 (Chen–Tian):** the max is attained at a symmetric matrix iff for every
  skew P there is a symmetric Q with ‖Q‖ = ‖P‖ and tr(L(Q+P)²) ≥ 0, because tr(L(Q+P)²) = ‖L Q‖² − ‖L P‖².
  Their proofs (n ≤ 3 generalized; n ≤ 5 in the SIAM note) choose Q = the matrix obtained from P in its real Schur basis
  by flipping the sign of the lower triangle — i.e. Q = P·T with T = block reflection anticommuting with P — after a rotation
  that diagonalises the coupling blocks, so tr(L(Q+P)²) becomes a sum of squares. This is exactly the Lean-checked rank ≤ 4
  same-square argument (`theory/SameSquareExclusion.lean`).
* **Where it breaks at n = 6:** skew P of rank 6 has three 2×2 blocks; tr(L(PT+P)²) = (diagonal squares) + three cross terms,
  one per pair of blocks (12),(13),(23). For rank ≤ 4 there is only one cross term and the SO(2)² signed SVD kills it.
  With three blocks, the six phases (θ_i − θ_j, θ_i + θ_j) the cross terms depend on are functions of only three angles,
  so the cross terms cannot all be made favourable for arbitrary A (see §2 for the exact formula). For n = 7 the KV witness
  has rank 6 too, and there the same-square class provably fails (theory/NOTES.md §2: 1183.2 < 1196.0).

## 1. Verified identities (`e01_identities.py`, max error 4e-14 over 200 random trials)

For any A, any skew K, any symmetric orthogonal T with TK = −KT, M := AK, H := sym(AK), Y := L_A K, X_c := (X + TXT)/2, X_a := (X − TXT)/2:

* (I1) E_A(KT) − E_A(K) = tr((M + TMT)²) = 4 tr(M_c²)   [Chen–Tian quantity for Q = KT]
* (I2) ‖L_A(KT)‖² = 4‖H_c‖² + ‖Y_a‖²,  hence  E_A(KT) − E_A(K) = 4‖H_c‖² − ‖Y_c‖².
  (Proof: AKT + KTAᵀ = HT + TH + (YT − TY)/2 = 2H_c T + Y_a T and ⟨Y_aT, H_cT⟩ = 0.)
* (I3) common-T lemma: if also TY = −YT then ⟨YT, L_A(KT)⟩ = ‖Y‖² (only uses Y = L_A K).
* (I4) on the affine family of a compatible pair: 2tr(A K Z₁) = tr(Z₁Y), 2tr(A Z₂ Y) = tr(Z₂K) for all skew Z₁,Z₂.
* (I5) ⟨U, L_A V⟩ = 2 tr(A V U) for symmetric U, V.

## 2. The pointwise Chen–Tian class at the top pair  (new; much stronger than bilevel's fss class)

Define for a compatible pair (K,Y)
  g_K(K,Y) := min_z max_{T∈T(K)} ‖L_{A(z)}(KT)‖ / ‖K‖ ,  T(K) = {F diag(R(θ₁),R(θ₂),R(θ₃)) Fᵀ} (3-torus).
f ≥ g_K (KT are particular symmetric matrices).  bilevel's `fss.py` restricted BOTH singular vectors to same-square
classes and got 0.74–0.95 < 1; here only the right vector is restricted, the left one is free.

* `ssclass.py`: exact evaluation.  L_{A(z)}(KT) = Σ_j d_j v_j(z), d = (cos θ_i, sin θ_i), so the oracle is
  max over the torus of dᵀG(z)d; outer min over z by SOCP cutting planes (Clarabel), with dual weights = measure ν.
* **Minimax reformulation (rigorous):** ‖L_{A(z)}(KT)‖² is a convex quadratic in z for each T, so
  g_K² = max_ν min_z E_ν ‖L_{A(z)}(KT)‖² (ν probability on the torus). By (I2) the condition g_K ≥ 1 is
  ∃ν :  min_{H ∈ H₀+ker Φ}  E_ν [4‖H_c(T)‖² − ‖Y_c(T)‖²] ≥ 0.
  Everything depends on ν only through the 9 complex Fourier moments E e^{i(θ_i−θ_j)}, E e^{i(θ_i+θ_j)}, E e^{2iθ_i}.
* Numerically the optimal ν has **two atoms** (pairs 1, 3 of seed 0; pair 2: two tight clusters). No single T works for all z.
* First 6 gaussian compatible pairs: f = 2.165, 1.289, 1.459, 2.242, 1.992, 15.39;  g_K = 1.4245, 1.0159, 1.0495, 1.5790, 1.3771, 1.9988.
  Natural pairs (top pair of a random A): f = 1.0019, g_K = 1.0000099; f = 1.0038, g_K = 1.0000016.

**Conjecture SS6.** For every A ∈ ℝ^{6×6} and every skew singular triple (σ,K,Y) of L_A|K with K invertible,
max_{T∈T(K)} ‖L_A(KT)‖ ≥ σ‖K‖.   (⇔ g_K ≥ 1 on all compatible pairs; ⇒ Byers–Nash for n = 6 together with the rank ≤ 4 theorem.)

### Failed / artefact log
* e03 first version: cutting planes with per-cut BFGS, minutes per sample — replaced by `ssclass.py`.
* e04 sparse first run reported ρ = 0.982: artefact. For rank-deficient K the real Schur form is not aligned with
  the 2×2 block positions, so the torus was built in a wrong frame. Fixed `ssclass.frame` (eigenspaces of −K², v₂ = Kv₁/|Kv₁|);
  the case re-evaluates to ρ = 1.0467. All other ρ ≤ 1 + 1e-6 hits there had σ_min(K) < 1e-15 (rank ≤ 4, covered by Lean; equality cases).

## 3. Conjecture SS6 is FALSE (exact certificate) — same-square / Chen–Tian cannot prove n = 6

* e05 (CMA over A, minimising ρ_top = max_T ‖L_A(K_A T)‖/k(A), barrier σ_min(K) ≥ 0.05):
  seed 1 ρ = 0.9576 (K moduli 0.532, 0.403, 0.233, full rank; k₂/k₁ = 0.9978; s/k = 1.12); seed 2 ρ = 0.9885.
  e04 plain gaussian sampling: min ρ = 0.9992 (non-top triple, σ_min = 0.17).
* `cert_ss_fail.py` → `cert_ss_fail.json`: A rounded to 1e-6 (rational), K̃ = F̃ diag(w̃J) F̃ᵀ with F̃ exact Cayley-orthogonal,
  w̃ = (0.532388, 0.403066, 0.232597). For **all 27 components** of the same-square class of K̃ (all T anticommuting with K̃,
  incl. the non-toral components when moduli coincide — here they don't) the exact bound UB/E_A(K̃) ≤ 0.91703 holds, with
  exact rational LDLᵀ PSD checks; cos(K̃, top skew vector of L_A) = 1 − 2.3e-13.
  Hence: **there is a 6×6 A whose top skew singular vector K is full rank and every same-square comparator KT has
  ‖L_A(KT)‖ < k(A)‖K‖.** The Chen–Tian Lemma-2.2 test with Q = PT fails at n = 6. Since the same class also fails
  at the n = 7 KV witness, the same-square obstruction is NOT what separates 6 from 7.

## 4. Structure of the optimal f-dual (inner problem at a compatible pair)

* The dual P = Σσ_k V_kU_k = KZ₁ + Z₂Y (verified, residual 1e-10) has rank 1–2; U, V far from same-square.
* At the SS-fail pair: f = 1.0443 while g_K = 0.954.
* single-V certificate h = max_V min_z ‖L_{A(z)}V‖/‖V‖ is within 1e-4 of f (so rank-1 dual "almost" suffices, but is not exact).
* V* frequently has 1–3 near-zero eigenvalues; V* is NOT a polynomial in K,Y (least-squares fit residual 0.2–0.8 over
  the 1, K², Y², KY+YK, ... words up to degree 4), though ‖[V*,K²]‖ is fairly small.

## 5. Structured certificate classes (`classes.py`, `e10_adv_class.py`): all single classes FAIL

g_class = min_z σ_max(B(z)Q) where Q = isometric embedding of a subspace class of symmetric right vectors.

| class | SS-fail pair | adversarial CMA over compatible pairs |
|---|---|---|
| C6K (same-square torus span) | 0.9655 | — |
| C9K (span of K·sym-anticommuting) | 0.9927 | 0.9068 (fails) |
| C9Y-left | 1.008 | 0.9204 (fails) |
| C9K + C9Y (sum) | 1.0308 | 1.0057 at gen 40, still descending (stopped) |
| either (max of C9K, C9Y-left) | — | 1 + 8e-9 at gen 90 (tight at the ridge, no failure found; stopped) |

So no fixed small linear family of right vectors works; the "either" observation is weak evidence only.

## 6. Trivial constants

* Averaging (I2) over the torus with Haar measure: E‖Y_c‖² = ‖Y_off‖²/2 ⇒ k ≤ √2·s, any n. Not new
  (s ≥ √2‖A‖₂ via X = vvᵀ... and k ≤ 2‖A‖₂).  Quantitative: s ≥ k·√(1 − δ²), δ = min_T ‖Y_c(T)‖/‖Y‖.

## 7. Static A-free reformulation (rigorous, all n)  — `staticN.py`

For U,V symmetric, ⟨U, L_A V⟩ = 2⟨A, UV⟩; for K,Y skew, ⟨Y, L_A K⟩ = −2⟨A, YK⟩. Hence
  s(A) = 2 h_C(A), C = conv{UV : ‖U‖=‖V‖=1 symmetric};   k(A) = 2 h_D(A), D = {YK : ‖Y‖=‖K‖=1 skew}
(h = support function). Therefore, by the bipolar theorem,

  **Byers–Nash(n)  ⇔  D ⊂ C  ⇔  N(YK) ≤ ‖Y‖‖K‖ for all skew K,Y,**

N := gauge of C = min{Σ|c_k| : P = Σc_k U_kV_k, U_k,V_k unit symmetric} = min{‖W‖_* : Σ W_ij S_iS_j = P} (SDP), and
sup_A k/s = max_{K,Y unit} N(YK).  Dual variable of the SDP = maximising A.
Known facts: N ≥ ‖·‖_*; N(Σ) = ‖Σ‖_* for Σ symmetric; N(Ω) = ‖Ω‖_* for Ω skew; N(P) ≤ ‖sym P‖_* + ‖skew P‖_*;
common T ⇒ YK = (YT)(TK) ⇒ N(YK) ≤ 1; rank K ≤ 4 or rank Y ≤ 4 ⇒ N(YK) ≤ 1 (Lean rank-4 theorem + adjoint L_A* = L_{Aᵀ}).

Numerics (`t_static.py`): n=7 KV top pair N = 1.00128 > 1 (positive control). n=6: 30 random unit pairs N ∈ [0.663, 0.964]
(nuclear ∈ [0.52,0.85], sym+skew-nuclear ∈ [0.91,1.32] — so the cheap bound is useless); K=Y: N=1; SS-fail pairs 0.99375, 0.98903;
natural pairs 0.9903–0.9998.

Optimal decompositions (`t_decomp.py`): rank(W) = 2–3 (random), 2–4 (natural, with tiny tails); factors U_k,V_k are NOT
same-square (‖U²+Y²‖, ‖V²+K²‖ = 0.1–0.6); at natural pairs the leading factors are close to rank 2
(e.g. eig U ≈ (−0.75,−0.65,0,0,0.07,0.10)), i.e. concentrated on 2-planes.

### 7a. Monotone MM ascent ⇒ much stronger n = 7 counterexample (`t_n7dual.py`, `e12_mm_ascent.py`)
Iteration (K_t,Y_t) = top skew pair of A_t; A_{t+1} = SDP-dual maximiser of ⟨A, Y_tK_t⟩ s.t. s(A) ≤ 2. Then
ratio(A_t) ≤ N(Y_tK_t) ≤ ratio(A_{t+1}) (monotone). From KV's A (ratio 1.0001803) it reaches
**k/s = 1.0077887212980870** after 30 steps (`logs/n7_dual_best.npy`; independently verified by Kronecker form + 40-digit
mpmath, `t_kron.py`). ~43× KV's margin. The limit matrix keeps KV's sparsity pattern approximately (dominant blocks rows 3–5×cols 1–3, rows 6–7×cols 4–6) plus small fill.
* **Exact certificate** `cert_n7.py` → `cert_n7.json`: integer A (entries ≤ 200, rounded), integer skew K; exact rational
  q = ‖L_AK‖²/‖K‖² = 148771.98…, c = 146621.35… with c·⟨X,X⟩ − ‖L_AX‖² PD on Sym_7 by exact LDLᵀ (min pivot 5196.7).
  ⇒ **k/s > 1.007307 rigorously** (KV: 1.00018).
* n = 7 ascent from random starts (`e12_n7_g`, `e12_n7_sp`): most starts converge to the SAME value 1.0077888 (moduli
  (0.5764, 0.3581, 0.1988), equal for K and Y), others to 1.0073, 1.0045, or to 1 (rank-4 limit). ⇒ numerically
  sup_{n=7} k/s ≈ 1.0077888, reached from generic starts.
* n = 6 ascent, 54 starts (gaussian 20, sparse 33, from SS-fail A 16+3): max k/s = 1 − O(1e-11), never > 1.
  `t_endpoints.py` classification: limits either have rank K → 4 (most gaussian/sparse starts) or are full rank
  (σ₃ up to 0.27) and **on the common-T locus** (defect ≤ 6e-6, involution of signature (3,3) found).
  n = 7 limit: common-T defect 0.155, |⟨ker K, ker Y⟩| = 0.26.

## 8. 6 vs 7: dimension reduction (rigorous) and kernel geometry

* N_n(YK) = N_d(YK|_W), W = range K + range Y (embed decompositions / compress the dual A). Checked numerically
  (N₆(P) = 8.1044951 = N₇(P⊕0)). ⇒ BN(6) ⇔ BN(7) on aligned-kernel pairs; 7-counterexamples need ker K ≠ ker Y.
* `t_n7kernels.py`: rotating ker Y onto ker K (fixing everything else) moves N monotonically:
  KV pair 1.00128 → 1.00085 → 1.00026 → 0.99986 → 0.99972;  MM pair 1.00779 → 1.00695 → 1.00410 → 0.99931 → 0.99674.

## 9. Maximiser structure in n = 6 and local behaviour

* On the common-T locus N is generally < 1 (random common-T pairs: 0.70–0.97; nuclear norm lower bound below that);
  N = 1 only on a thin sub-locus (`t_commonT.py`). So the n = 6 maximiser set is a thin subvariety of
  (common-T locus) ∪ (rank-4 boundary).
* Second order (`t_curv.py`): at a full-rank common-T maximiser and at a rank-4 maximiser, along 40 random directions
  transverse to the O(6) × scaling orbit, 1 − N(e) ≈ c e² with c ∈ [0.044, 0.58] (all > 0). Scaling checked:
  e = 1e-2 → 7.4e-6, 3e-3 → 6.6e-7. Strict local maximality numerically (transversal Hessian positive in sampled directions).

## 10. Atomic certificate attempt (YK = convex combination of Thm-2 atoms) — FAILS (numerically robust)

**Verified** (`t_atoms_verify.py SSfail`): at the bundle's final G (⟨G,YK⟩ = 1), a heavy oracle (200 BFGS starts per
family, all three families; top-5 values coincide) gives max_atoms ⟨G,a⟩ = 0.994174 ⇒ **N4(YK) ≥ 1.00586 > 1 > 0.99375 = N(YK)**.
(Not a certificate: rigorous would require global optimisation over SO(6) for the atom oracle.)
n = 7 ascent statistics (14 starts): 5 → 1 (rank-4 limits), 9 → >1: 1.0045, 1.0073, 1.0076, 1.0076, 1.00779 (×5).


Atoms: Y'K' unit with rank K' ≤ 4, or rank Y' ≤ 4, or common-T (all have N ≤ 1 by Lean / identity). N ≤ N4 := atomic gauge.
* `atoms.py` (plain cutting-plane LP): too slow (36-dim, ~3000 cuts, still not converged). Abandoned.
* `atoms2.py` (proximal bundle on min{φ(G): ⟨G,P⟩ = 1}, φ = max_atoms⟨G,a⟩, started from the N-SDP dual):
  heuristic N4 lower bounds 1/φ(center): random0 0.9613 (N = 0.9439); natural0 0.99983 (N = 0.99937);
  **natural1 1.00105 (N = 0.99943); SS-fail 1.00557 (N = 0.99375)**. The rigorous LP upper bound is useless
  (atoms found do not span well; bounds 90–2000).
  If confirmed by the heavy oracle (`t_atoms_verify.py`), then YK at these pairs is NOT a convex combination of
  rank-4/common-T atoms, i.e. the n = 6 proof cannot be a "reduction to rank 4 + common T" decomposition; genuinely
  full-rank UV terms are required.
