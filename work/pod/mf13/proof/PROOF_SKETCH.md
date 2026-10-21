# Byers–Nash for n = 6: proof sketch, status, precise gap

Notation: L_A(X) = AX + XAᵀ; s(A) = ‖L_A|Sym‖, k(A) = ‖L_A|Skew‖ (Frobenius operator norms).
BN(n): k(A) ≤ s(A) for all A ∈ ℝ^{n×n}. Known: true for n ≤ 5 (Chen–Tian), false for n ≥ 7 (Kressner–Vandereycken).

Labels: **[P]** proved here (short proof given or exact computation), **[L]** Lean-checked (pod `theory/SameSquareExclusion.lean`),
**[N]** numerically verified (no certificate), **[C]** conjectural.

---------------------------------------------------------------------------------------------------------------------

## 1. Proved statements

### Theorem 1 [P] (A-free static reformulation, all n)
For symmetric U, V and skew K, Y:  ⟨U, L_A V⟩ = 2⟨A, UV⟩  and  ⟨Y, L_A K⟩ = −2⟨A, YK⟩. Hence

  s(A) = 2·h_C(A),  C = {UV : U,V ∈ Sym_n, ‖U‖ = ‖V‖ = 1},   k(A) = 2·h_D(A),  D = {YK : K,Y ∈ Skew_n unit},

with h the support function (D = −D). By the bipolar theorem

  **BN(n) ⇔ D ⊂ conv C ⇔ N(YK) ≤ ‖Y‖·‖K‖ for all skew K, Y,**   and   sup_A k(A)/s(A) = max_{unit K,Y} N(YK),

where N = gauge of conv C = min{Σ|c_k| : P = Σ c_k U_kV_k, U_k, V_k unit symmetric} = min{‖W‖_* : Σ_{ij} W_ij S_iS_j = P}
(an SDP; S_i orthonormal basis of Sym_n). The SDP dual variable of N(YK) is an A attaining ⟨Y, L_A K⟩ = N(YK)·s(A).
*Proof.* tr(U(AV + VAᵀ)) = tr(AVU) + tr(AᵀUV) = 2⟨A,UV⟩; similarly for skew with a sign. Closed convex sets with
h_{conv D} ≤ h_{conv C} satisfy conv D ⊂ conv C. ∎

So BN(6) is a statement about factoring the product of two skew matrices into products of symmetric matrices:
**every YK (K, Y ∈ Skew_6) is a combination Σ c_k U_kV_k with Σ|c_k|·‖U_k‖‖V_k‖ ≤ ‖Y‖‖K‖.**

### Theorem 2 [P]+[L] (the cases that are already settled, n = 6)
N(YK) ≤ ‖Y‖‖K‖ whenever
 (a) rank K ≤ 4 or rank Y ≤ 4  [L: `rank_four_conjugated_exclusion` gives ‖L_A K‖ ≤ ‖L_A S‖ ≤ s(A)‖K‖ for some symmetric
     S with ‖S‖ = ‖K‖; for rank Y ≤ 4 use L_A* = L_{Aᵀ} and s(Aᵀ) = s(A)];
 (b) K and Y share an anticommuting symmetric involution T (TK = −KT, TY = −YT)  [P: YK = (YT)(TK), with YT and TK
     symmetric of norms ‖Y‖ and ‖K‖].
In the pod's A-language, (b) is the common-T lemma ⟨YT, L_A(KT)⟩ = ‖Y‖² (identity I3, NOTES §1).

### Theorem 3 [P] (dimension reduction; the 6-vs-7 relation)
For skew K, Y in ℝⁿ put W = range K + range Y, d = dim W. Then N_n(YK) = N_d(YK|_W).
(≤: embed decompositions, (U⊕0)(V⊕0) = UV⊕0. ≥: compress the dual A to W; s cannot increase because
⟨Π_W A Π_W, UV⟩ = ⟨A, (U⊕0)(V⊕0)⟩.)
Consequences:
* BN(6) ⇔ "every pair K, Y in any dimension with dim(range K + range Y) ≤ 6 satisfies N(YK) ≤ ‖Y‖‖K‖".
* BN(6) ⇔ BN(7) restricted to pairs with ker K = ker Y. **Every 7×7 counterexample needs misaligned kernels.**
  (The KV pair has |⟨ker K, ker Y⟩| = 0.155. Rotating ker Y onto ker K moves N(YK) continuously from 1.00128 to
  0.99972 < 1; `t_n7kernels.py`.)
* With Theorem 2(a): in any dimension a violating pair needs rank K = rank Y = 6 and dim(range K + range Y) ≥ 7.
  In n = 6 the only room left is "both invertible and not common-T".

### Theorem 4 [P] (the Chen–Tian / same-square mechanism cannot prove n = 6; exact certificate)
There is an explicit rational A ∈ ℚ^{6×6} (`cert_ss_fail.json`) whose top skew singular vector K̃ (exact rational
approximation, cos = 1 − 2.3e-13) is invertible (moduli 0.532, 0.403, 0.233), and for **every** symmetric involution T
anticommuting with K̃ (all 27 components of the same-square class), ‖L_A(K̃T)‖² ≤ 0.91703·‖L_A K̃‖², certified by exact
LDLᵀ PSD checks. So the Chen–Tian Lemma-2.2 comparator Q = PT, and the Lean rank-4 argument, fail at n = 6 as they do at
n = 7. Being same-square is therefore not what separates 6 from 7.

### Theorem 5 [P] (monotone ascent; much stronger n = 7 counterexample)
The iteration (K_t, Y_t) = top skew pair of L_{A_t}, A_{t+1} = SDP-dual maximiser of N(Y_tK_t) satisfies
k/s(A_t) ≤ N(Y_tK_t) ≤ k/s(A_{t+1}). Started from KV (ratio 1.00018) it converges to 1.0077887 (40-digit mpmath).
Rounded to an **integer 7×7 matrix with entries ≤ 200** (`cert_n7.json`, `cert_n7.py`, exact rational arithmetic:
‖L_A K‖²/‖K‖² = 148771.98… for an integer skew K, and c·I − (L_A|Sym)*(L_A|Sym) ≻ 0 by exact LDLᵀ with c = 146621.35…):
**k(A)/s(A) > 1.00730**, about 40 times KV's margin. At the limit, K and Y have equal moduli (0.5768, 0.3574, 0.1988),
|⟨ker K, ker Y⟩| = 0.26, and the pair is far from common-T (defect 0.155).

### Trivial bounds [P]
k ≤ √2·s for all n (Haar-average of identity I2 over the torus; also immediate from s ≥ √2‖A‖₂ and k ≤ 2‖A‖₂).
Quantitative: s ≥ k·√(1 − δ²), δ = min_T ‖(L_AK)_c(T)‖/‖L_A K‖.

---------------------------------------------------------------------------------------------------------------------

## 2. Numerically verified [N]

* max_{K,Y ∈ Skew_6 unit} N(YK) = 1 (`staticN.py`):
  - random pairs: N ∈ [0.66, 0.96];
  - top pairs of random A: 0.990–0.9998;
  - SS-fail pairs: 0.9938, 0.9890;
  - CMA maximisation of N (e11, stopped early): 0.991.
  - Positive control, n = 7 KV pair: 1.00128.
* The monotone ascent (Thm 5) in n = 6, 54 starts (gaussian, sparse, and from the SS-fail matrix) gives
  max k/s = 1 − O(1e-11) and never exceeds 1. Every limit is an **atom of Thm 2**: either rank K → 4, or
  (full-rank limits, σ₃(K) up to 0.27) the pair lies on the common-T locus (defect ≤ 6e-6, with a (3,3)-signature
  involution found). In n = 7 the same ascent leaves the atom set (Thm 5).
* Pod results this rests on: f(K,Y) = min_z s(A(z)) ≥ 1 on all sampled compatible pairs, with minimum 1 on the
  common-T ridge.
* Identities I1–I5 (NOTES §1), to 4e-14.

## 3. What the certificates look like [N]

* Optimal decompositions YK = Σ c_kU_kV_k (SDP for N) have rank 2–4. The factors are NOT same-square
  (‖U²+Y²‖, ‖V²+K²‖ ≈ 0.1–0.6), are not polynomials in K, Y, and near the extremal set are almost rank 2
  (concentrated on 2-planes). On the common-T locus the decomposition degenerates to the single term (YT)(TK).
* Fixed linear classes of right singular vectors in the inner problem all fail adversarially:
  - same-square torus span C6K;
  - C9K: 0.907;
  - C9Y-left: 0.920;
  - the C9K+C9Y sum (1.0057, still decreasing when stopped) and the "either" class (1 + 8e-9) were inconclusive.
* **Atomic certificates fail.** Can YK always be written as a convex combination of Theorem-2 atoms (rank-4 or common-T
  products)? At the SS-fail pair (N = 0.99375), a dual G with ⟨G, YK⟩ = 1 has max over atoms ⟨G, a⟩ = 0.99417
  (heavy multistart in all three families, consistent top-5; NOTES §10). Hence the atomic gauge is ≥ 1.0059 > 1, and
  similarly 1.0010 at a natural pair. So **BN(6) cannot be proved by decomposing YK into already-settled cases**.
  The certificate needs UV terms with genuinely full-rank, non-same-square factors.
* In n = 6 the maximisers of N are strict: 1 − N ≈ c·ε² with c ∈ [0.044, 0.58] in all sampled transverse directions.
* n = 7 contrast: the monotone ascent from generic random starts reaches k/s > 1 in 9 of 14 starts, and 5 of those reach
  the same value 1.0077888. Numerically sup_{n=7} k/s ≈ 1.00779.

## 4. Conjectural [C]

* **(BN6-static)** N(YK) ≤ ‖Y‖‖K‖ for all K, Y ∈ Skew_6, with equality only on the atom set of Theorem 2.
* (Ridge) The set of maximisers of k/s in n = 6 is contained in {A : the top skew pair is rank-4 or common-T}.

## 5. The precise remaining gap

> Show N(YK) ≤ 1 for unit K, Y ∈ Skew_6 that are both invertible and have no common anticommuting symmetric
> involution. Equivalently, exhibit for every such pair symmetric U_k, V_k with YK = Σ U_kV_k and Σ‖U_k‖‖V_k‖ ≤ 1.
> Equivalently (pod form), f(K,Y) ≥ 1 for compatible pairs with full-rank K off the common-T locus.

What is known about this gap:
1. No same-square comparator works (Thm 4). The certificate must involve factors U, V that are not of the form
   (Y or K)·T. Convex combinations of settled cases (rank-4 / common-T atoms) do not suffice either (§3, numerically
   robust).
2. By Theorem 3, the n = 6 statement is exactly the "aligned-kernel" slice of n = 7, and n = 7 fails only through
   misaligned kernels (Thm 5 example). Any proof must use, at least implicitly, that ℝ⁶ has no room for a seventh
   direction: invertibility of K and Y in dimension 6.
3. The natural proof route suggested by the numerics is local-to-global. Maximisers sit on the atom set, where
   N = 1 is proved (Thm 2). What is missing is (i) a second-order statement that the atom set is a strict local maximum
   in normal directions, and (ii) a global argument that excludes interior local maxima above 1. Neither is done.
