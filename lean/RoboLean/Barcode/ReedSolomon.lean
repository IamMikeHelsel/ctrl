import Mathlib

/-!
# Reed–Solomon codes

Reed–Solomon (RS) codes are the error-correcting layer of essentially every 2D barcode:
QR, Data Matrix, Aztec and MaxiCode use RS over `GF(2^8)` (Aztec also smaller `GF(2^m)`),
and PDF417 uses RS over the prime field `GF(929)`.

We work over an arbitrary field `F`, with `n` pairwise distinct evaluation points
`α : Fin n → F` (`Function.Injective α`). A message is a polynomial `p` of degree `< k`
(an element of `Polynomial.degreeLT F k`), and its codeword is `(p(α 0), …, p(α (n-1)))`.

## Main results

* `dist_ge`, `minDist_eq`: distinct codewords differ in `≥ n - k + 1` places, and this is
  attained — RS codes are MDS. `singleton_bound`: no code beats `n - k + 1`.
* `encodeLinear`, `encodeLinear_injective`: encoding is linear and injective (`k ≤ n`).
* `unique_decoding`: with `s` erasures and `e` errors, `2e + s ≤ n - k` ⇒ unique decoding;
  `corrects_half_ecc`, `corrects_ecc_erasures`: the barcode corollaries
  (`⌊(n-k)/2⌋` errors or `n - k` erasures per block).
* `erasure_decode`: any `k` surviving symbols decode by Lagrange interpolation.
* `bw_exists`, `bw_correct`, `bw_div`: the Berlekamp–Welch key equation has a solution with a
  monic degree-`e` error locator, and **every** nonzero solution yields the message as `Q / E`.
* `bruteDecode_eq` plus concrete `decide` checks over `ZMod 7` and `ZMod 929` (PDF417's field).
* `twisted_range_eq_ker`, `genPoly_dvd_iff`: the generator-polynomial/syndrome view used by
  ZXing (`g(x) = ∏ (x - ω^(b+l))`, generator base `b`) is the same code as the evaluation view.

## Prior art

ArkLib (Verified-zkEVM) has Reed–Solomon codes, MDS/distance and a Berlekamp–Welch development
in Lean 4 (aimed at SNARK proximity proofs); Affeldt–Garrigue–Saikawa formalize RS/BCH codes in
Coq/MathComp (`infotheo`). This file is self-contained over Mathlib only.
-/

namespace RoboLean.Barcode.ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- Reed–Solomon encoding: evaluate the message polynomial at the evaluation points. -/
def encode (α : Fin n → F) (p : F[X]) : Fin n → F := fun i => p.eval (α i)

@[simp] lemma encode_apply (α : Fin n → F) (p : F[X]) (i : Fin n) :
    encode α p i = p.eval (α i) := rfl

/-- RS encoding as an `F`-linear map from messages (polynomials of degree `< k`). -/
noncomputable def encodeLinear (α : Fin n → F) (k : ℕ) : degreeLT F k →ₗ[F] (Fin n → F) where
  toFun p := encode α p
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

lemma encode_sub (α : Fin n → F) (p q : F[X]) :
    encode α (p - q) = encode α p - encode α q := by ext i; simp

/-- **Root bound.** A polynomial of degree `< |S|` vanishing at the (distinct) points
`α i`, `i ∈ S`, is zero. -/
lemma eq_zero_of_vanish {α : Fin n → F} (hα : Function.Injective α) {f : F[X]}
    (S : Finset (Fin n)) (hdeg : f.degree < #S) (hz : ∀ i ∈ S, f.eval (α i) = 0) : f = 0 :=
  Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero S (hα.injOn) hdeg hz

variable [DecidableEq F]

/-- A nonzero polynomial of degree `< k` vanishes at fewer than `k` of the evaluation points. -/
lemma card_zeros_lt {α : Fin n → F} (hα : Function.Injective α) {f : F[X]} {k : ℕ}
    (hf : f ≠ 0) (hdeg : f.degree < k) : #{i | f.eval (α i) = 0} < k := by
  by_contra h
  push Not at h
  exact hf (eq_zero_of_vanish hα _ (lt_of_lt_of_le hdeg (by exact_mod_cast h))
    (fun i hi => (mem_filter.1 hi).2))

/-- The Hamming distance between two codewords is `n` minus the number of points where the
difference polynomial vanishes. -/
lemma hammingDist_encode (α : Fin n → F) (p q : F[X]) :
    hammingDist (encode α p) (encode α q) + #{i | (p - q).eval (α i) = 0} = n := by
  unfold hammingDist
  have : (#{i | (p - q).eval (α i) = 0} : ℕ) = #{i | ¬ (encode α p i ≠ encode α q i)} := by
    congr 1; ext i; simp [sub_eq_zero]
  rw [this, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

/-- **Minimum distance lower bound.** Two distinct RS codewords (messages of degree `< k`)
differ in at least `n - k + 1` positions. -/
theorem dist_ge {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} {p q : F[X]}
    (hp : p ∈ degreeLT F k) (hq : q ∈ degreeLT F k) (hpq : p ≠ q) :
    n + 1 ≤ hammingDist (encode α p) (encode α q) + k := by
  have hd : (p - q).degree < k := by
    have := (degreeLT F k).sub_mem hp hq
    exact mem_degreeLT.1 this
  have := card_zeros_lt hα (sub_ne_zero.2 hpq) hd
  have := hammingDist_encode α p q
  omega

/-- RS encoding is injective on messages of degree `< k` as long as `k ≤ n`. -/
theorem encode_injOn {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk : k ≤ n) :
    Set.InjOn (encode α) (degreeLT F k) := by
  intro p hp q hq h
  by_contra hpq
  have := dist_ge hα hp hq hpq
  rw [h, hammingDist_self] at this
  omega

/-- The linear encoder `encodeLinear` is injective (for `k ≤ n`). -/
theorem encodeLinear_injective {α : Fin n → F} (hα : Function.Injective α) {k : ℕ}
    (hk : k ≤ n) : Function.Injective (encodeLinear α k) := by
  intro p q h
  exact Subtype.ext (encode_injOn hα hk p.2 q.2 h)

/-- The distance `n - k + 1` is attained: for `1 ≤ k ≤ n` the message `0` and the message
`∏_{i ∈ S} (X - α i)` with `|S| = k - 1` give codewords at distance exactly `n - k + 1`. -/
theorem dist_attained {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ n) : ∃ p ∈ degreeLT F k, ∃ q ∈ degreeLT F k, p ≠ q ∧
      hammingDist (encode α p) (encode α q) + k = n + 1 := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (n := k - 1) (by simp; omega)
  set q : F[X] := ∏ i ∈ S, (X - C (α i)) with hqdef
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hqdeg : q.natDegree = k - 1 := by rw [hqdef, natDegree_finsetProd_X_sub_C_eq_card, hS]
  have hzero : ∀ j, q.eval (α j) = 0 ↔ j ∈ S := by
    intro j
    simp only [hqdef, eval_prod, eval_sub, eval_X, eval_C, prod_eq_zero_iff, sub_eq_zero]
    constructor
    · rintro ⟨i, hi, h⟩; rwa [hα h]
    · intro h; exact ⟨j, h, rfl⟩
  refine ⟨q, ?_, 0, Submodule.zero_mem _, hqm.ne_zero, ?_⟩
  · rw [mem_degreeLT, degree_eq_natDegree hqm.ne_zero, hqdeg]
    exact_mod_cast (by omega : k - 1 < k)
  · have h1 := hammingDist_encode α q 0
    have h2 : #{i | (q - 0).eval (α i) = 0} = k - 1 := by
      rw [← hS]; congr 1; ext j; simp [hzero]
    omega

/-- **RS codes are MDS.** For `1 ≤ k ≤ n`, the minimum distance of the RS code is exactly
`n - k + 1`: every pair of distinct codewords is at distance `≥ n - k + 1`, and some pair
attains it. -/
theorem minDist_eq {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ n) :
    (∀ p ∈ degreeLT F k, ∀ q ∈ degreeLT F k, p ≠ q →
        n - k + 1 ≤ hammingDist (encode α p) (encode α q)) ∧
    (∃ p ∈ degreeLT F k, ∃ q ∈ degreeLT F k, p ≠ q ∧
        hammingDist (encode α p) (encode α q) = n - k + 1) := by
  refine ⟨fun p hp q hq hpq => ?_, ?_⟩
  · have := dist_ge hα hp hq hpq; omega
  · obtain ⟨p, hp, q, hq, hpq, h⟩ := dist_attained hα hk1 hk
    exact ⟨p, hp, q, hq, hpq, by omega⟩

/-! ### The Singleton bound for arbitrary codes -/

/-- **Singleton bound** (general block codes over any finite alphabet `A`). If a code
`C ⊆ Aⁿ` has more than `|A|^m` words (`m ≤ n`), then two distinct codewords are at Hamming
distance `≤ n - m`. In particular a code with `|A|^k` words (`|A| ≥ 2`) has minimum
distance `≤ n - k + 1` (take `m = k - 1`), so RS codes attain the bound. -/
theorem singleton_bound {A : Type*} [Fintype A] [DecidableEq A] (C : Finset (Fin n → A))
    {m : ℕ} (hm : m ≤ n) (hC : Fintype.card A ^ m < #C) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y ≤ n - m := by
  let proj : (Fin n → A) → (Fin m → A) := fun x i => x (Fin.castLE hm i)
  have hcard : #(univ : Finset (Fin m → A)) < #C := by simpa using hC
  obtain ⟨x, hx, y, hy, hxy, h⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := proj) (fun _ _ => mem_coe.2 (mem_univ _))
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  unfold hammingDist
  have hsub : ({i | x i ≠ y i} : Finset (Fin n)) ⊆ ({i | ¬ ((i : ℕ) < m)} : Finset (Fin n)) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    intro hlt
    exact hi (congrFun h ⟨i, hlt⟩)
  refine (card_le_card hsub).trans ?_
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < m)
  have h2 : #({i | (i : ℕ) < m} : Finset (Fin n)) = min n m := Fin.card_filter_val_lt
  simp only [card_univ, Fintype.card_fin] at h1
  omega

/-- Singleton bound specialised to codes of size `|F|^k` over a finite field: some pair of
distinct codewords is at distance `≤ n - k + 1`. -/
theorem singleton_bound_field {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (C : Finset (Fin n → K)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (hC : #C = Fintype.card K ^ k) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y ≤ n - k + 1 := by
  obtain ⟨x, hx, y, hy, hxy, h⟩ := singleton_bound C (m := k - 1) (by omega) (by
    rw [hC]; exact Nat.pow_lt_pow_right Fintype.one_lt_card (by omega))
  exact ⟨x, hx, y, hy, hxy, by omega⟩


/-! ### Unique decoding with errors and erasures -/

/-- The error positions of a word `c` relative to the received word `r`, ignoring the erased
positions `E` (positions whose symbol the reader knows to be unreadable). -/
def errorsOff (E : Finset (Fin n)) (c r : Fin n → F) : Finset (Fin n) :=
  {i | i ∉ E ∧ c i ≠ r i}

/-- **Unique decoding with errors and erasures.** Let `E` be a set of `s` erased positions and
suppose `2e + s ≤ n - k`. If two messages `p, q` of degree `< k` both have codewords that agree
with the received word `r` outside `E` except in at most `e` positions, then `p = q`.
So the transmitted codeword is the unique codeword consistent with `r` up to `e` errors. -/
theorem unique_decoding {α : Fin n → F} (hα : Function.Injective α) {k e : ℕ}
    (E : Finset (Fin n)) (r : Fin n → F) (hbound : 2 * e + #E + k ≤ n)
    {p q : F[X]} (hp : p ∈ degreeLT F k) (hq : q ∈ degreeLT F k)
    (hpe : #(errorsOff E (encode α p) r) ≤ e) (hqe : #(errorsOff E (encode α q) r) ≤ e) :
    p = q := by
  by_contra hpq
  have hd := dist_ge hα hp hq hpq
  have hsub : ({i | encode α p i ≠ encode α q i} : Finset (Fin n)) ⊆
      E ∪ (errorsOff E (encode α p) r ∪ errorsOff E (encode α q) r) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [errorsOff, mem_union, mem_filter, mem_univ, true_and]
    by_cases hiE : i ∈ E
    · exact Or.inl hiE
    · by_cases h1 : encode α p i = r i
      · exact Or.inr (Or.inr ⟨hiE, fun h2 => hi (h1.trans h2.symm)⟩)
      · exact Or.inr (Or.inl ⟨hiE, h1⟩)
  have := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_union_le _ _) _))
  unfold hammingDist at hd
  omega

/-- **Error correction capacity** (e.g. one QR block with `n - k` ECC codewords): any
`⌊(n - k)/2⌋` symbol errors are corrected — the transmitted message is the unique message whose
codeword is within Hamming distance `⌊(n-k)/2⌋` of the received word. -/
theorem corrects_half_ecc {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk : k ≤ n)
    (r : Fin n → F) {p q : F[X]} (hp : p ∈ degreeLT F k) (hq : q ∈ degreeLT F k)
    (hpe : hammingDist (encode α p) r ≤ (n - k) / 2)
    (hqe : hammingDist (encode α q) r ≤ (n - k) / 2) : p = q := by
  refine unique_decoding hα ∅ r (e := (n - k) / 2) (by simp; omega) hp hq ?_ ?_
  · refine le_trans (card_le_card (fun i hi => ?_)) hpe
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.2⟩
  · refine le_trans (card_le_card (fun i hi => ?_)) hqe
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.2⟩

/-- **Erasure capacity**: with `n - k` ECC symbols, up to `n - k` erasures (known unreadable
positions, no errors) are corrected — two messages agreeing with `r` off the erasure set `E`
(`|E| ≤ n - k`) coincide. -/
theorem corrects_ecc_erasures {α : Fin n → F} (hα : Function.Injective α) {k : ℕ}
    (E : Finset (Fin n)) (hE : #E + k ≤ n) (r : Fin n → F) {p q : F[X]}
    (hp : p ∈ degreeLT F k) (hq : q ∈ degreeLT F k)
    (hpr : ∀ i ∉ E, encode α p i = r i) (hqr : ∀ i ∉ E, encode α q i = r i) : p = q :=
  unique_decoding hα E r (e := 0) (by omega) hp hq
    (by rw [show errorsOff E (encode α p) r = ∅ from
          filter_eq_empty_iff.2 (fun i _ h => h.2 (hpr i h.1))]; simp)
    (by rw [show errorsOff E (encode α q) r = ∅ from
          filter_eq_empty_iff.2 (fun i _ h => h.2 (hqr i h.1))]; simp)

/-! ### Erasure decoding is Lagrange interpolation -/

omit [DecidableEq F] in
/-- **Erasure decoding.** If `S` is any set of `k` (or more) unerased positions, Lagrange
interpolation of the received symbols on `S` recovers the message polynomial. -/
theorem erasure_decode {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} {p : F[X]}
    (hp : p ∈ degreeLT F k) (S : Finset (Fin n)) (hS : k ≤ #S) (r : Fin n → F)
    (hr : ∀ i ∈ S, r i = encode α p i) :
    Lagrange.interpolate S α r = p := by
  have hdeg : p.degree < (#S : ℕ) :=
    lt_of_lt_of_le (mem_degreeLT.1 hp) (WithBot.coe_le_coe.2 (Nat.cast_le.2 hS))
  exact (Lagrange.eq_interpolate_of_eval_eq (s := S) (v := α) (r := r) hα.injOn hdeg
    (fun i hi => (hr i hi).symm)).symm

omit [DecidableEq F] in
/-- Any `k` positions determine a message of degree `< k`. -/
theorem eq_of_agree_on {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} {p q : F[X]}
    (hp : p ∈ degreeLT F k) (hq : q ∈ degreeLT F k) (S : Finset (Fin n)) (hS : k ≤ #S)
    (h : ∀ i ∈ S, encode α p i = encode α q i) : p = q := by
  rw [← erasure_decode hα hp S hS (encode α p) (fun _ _ => rfl),
    ← erasure_decode hα hq S hS (encode α p) (fun i hi => h i hi)]

/-! ### Berlekamp–Welch -/

/-- The **Berlekamp–Welch key equation** for a received word `r`: `Q(α i) = r i · E(α i)`
for every position `i`. -/
def KeyEq (α : Fin n → F) (r : Fin n → F) (E Q : F[X]) : Prop :=
  ∀ i, Q.eval (α i) = r i * E.eval (α i)

/-- **Berlekamp–Welch, existence.** If `r` differs from the codeword of `p` (degree `< k`) in
at most `e` positions, then there is a monic *error locator* `E` of degree exactly `e`
and a `Q` of degree `< e + k` solving the key equation (namely `Q = p · E`). -/
theorem bw_exists {α : Fin n → F} {k e : ℕ} {p : F[X]} (hp : p ∈ degreeLT F k)
    (r : Fin n → F) (he : hammingDist (encode α p) r ≤ e) :
    ∃ E Q : F[X], E.Monic ∧ E.natDegree = e ∧ Q.degree < (e + k : ℕ) ∧ KeyEq α r E Q := by
  set B : Finset (Fin n) := {i | encode α p i ≠ r i} with hB
  have hBe : #B ≤ e := he
  set E : F[X] := (∏ i ∈ B, (X - C (α i))) * X ^ (e - #B) with hE
  have hEm : E.Monic :=
    (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)).mul (monic_X_pow _)
  have hEdeg : E.natDegree = e := by
    rw [hE, (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)).natDegree_mul
      (monic_X_pow _), natDegree_finsetProd_X_sub_C_eq_card, natDegree_X_pow]
    omega
  refine ⟨E, p * E, hEm, hEdeg, ?_, ?_⟩
  · by_cases hp0 : p = 0
    · simp [hp0]
    · rw [degree_mul, degree_eq_natDegree hEm.ne_zero, hEdeg]
      have := mem_degreeLT.1 hp
      rw [degree_eq_natDegree hp0] at this ⊢
      have h' : p.natDegree < k := by exact_mod_cast this
      rw [← Nat.cast_add]; exact_mod_cast (by omega : p.natDegree + e < e + k)
  · intro i
    rw [eval_mul]
    by_cases hi : i ∈ B
    · have : E.eval (α i) = 0 := by
        rw [hE, eval_mul, eval_prod, prod_eq_zero hi (by simp), zero_mul]
      rw [this, mul_zero, mul_zero]
    · have h' : encode α p i = r i := by
        by_contra h; exact hi (by rw [hB]; exact mem_filter.2 ⟨mem_univ _, h⟩)
      rw [encode_apply] at h'
      rw [h']

/-- **Berlekamp–Welch, correctness (the key-equation lemma).** Suppose `r` is within `e`
errors of the codeword of `p` (degree `< k`) and `2e + k ≤ n` (i.e. `2e < n - k + 1`). Then
for **any** solution `(E, Q)` of the key equation with `E ≠ 0`, `deg E ≤ e`,
`deg Q < e + k`, we have `Q = p · E`. This is what makes the decoder work: solve the linear
system for `(E, Q)` (any nonzero solution) and output `Q / E`. -/
theorem bw_correct {α : Fin n → F} (hα : Function.Injective α) {k e : ℕ} {p : F[X]}
    (hp : p ∈ degreeLT F k) (r : Fin n → F) (he : hammingDist (encode α p) r ≤ e)
    (hn : 2 * e + k ≤ n) {E Q : F[X]} (hEdeg : E.degree ≤ e)
    (hQdeg : Q.degree < (e + k : ℕ)) (hkey : KeyEq α r E Q) : Q = p * E := by
  rw [← sub_eq_zero]
  set G : Finset (Fin n) := {i | encode α p i = r i} with hG
  have hGcard : n ≤ #G + e := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i => encode α p i = r i)
    simp only [card_univ, Fintype.card_fin] at h1
    have : hammingDist (encode α p) r = #({i | ¬ encode α p i = r i} : Finset (Fin n)) := rfl
    rw [hG]; omega
  apply eq_zero_of_vanish hα G
  · have hpE : (p * E).degree < (e + k : ℕ) := by
      by_cases hp0 : p = 0
      · simp [hp0]
      by_cases hE0 : E = 0
      · simp [hE0]
      rw [degree_mul]
      have h1 := mem_degreeLT.1 hp
      rw [degree_eq_natDegree hp0] at h1
      rw [degree_eq_natDegree hE0] at hEdeg ⊢
      rw [degree_eq_natDegree hp0]
      have a : p.natDegree < k := by exact_mod_cast h1
      have b : E.natDegree ≤ e := by exact_mod_cast hEdeg
      rw [← Nat.cast_add]; exact_mod_cast (by omega : p.natDegree + E.natDegree < e + k)
    refine (degree_sub_le _ _).trans_lt ((max_lt hQdeg hpE).trans_le ?_)
    exact WithBot.coe_le_coe.2 (Nat.cast_le.2 (by omega))
  · intro i hi
    rw [hG] at hi
    have hi' := (mem_filter.1 hi).2
    rw [encode_apply] at hi'
    rw [eval_sub, hkey i, eval_mul, hi', sub_self]

/-- Corollary: for a solution with `E ≠ 0`, exact polynomial division `Q / E` returns the
message. -/
theorem bw_div {α : Fin n → F} (hα : Function.Injective α) {k e : ℕ} {p : F[X]}
    (hp : p ∈ degreeLT F k) (r : Fin n → F) (he : hammingDist (encode α p) r ≤ e)
    (hn : 2 * e + k ≤ n) {E Q : F[X]} (hE0 : E ≠ 0) (hEdeg : E.degree ≤ e)
    (hQdeg : Q.degree < (e + k : ℕ)) (hkey : KeyEq α r E Q) : Q / E = p := by
  rw [bw_correct hα hp r he hn hEdeg hQdeg hkey, mul_div_cancel_right₀ _ hE0]


/-! ### Messages as coefficient vectors and a brute-force reference decoder -/

/-- The message polynomial `m 0 + m 1 X + ⋯ + m (k-1) X^(k-1)` of a coefficient vector. -/
noncomputable def msgPoly {k : ℕ} (m : Fin k → F) : F[X] := ∑ i, C (m i) * X ^ (i : ℕ)

omit [DecidableEq F] in
lemma msgPoly_mem {k : ℕ} (m : Fin k → F) : msgPoly m ∈ degreeLT F k := by
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [mem_degreeLT]
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast i.2)

omit [DecidableEq F] in
lemma coeff_msgPoly {k : ℕ} (m : Fin k → F) (j : Fin k) : (msgPoly m).coeff j = m j := by
  simp only [msgPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h.symm)
  · simp

omit [DecidableEq F] in
lemma msgPoly_injective {k : ℕ} : Function.Injective (msgPoly (F := F) (k := k)) := by
  intro m m' h; funext j; rw [← coeff_msgPoly m j, h, coeff_msgPoly]

/-- Computable RS encoding of a coefficient vector: `c j = ∑ᵢ m i · (α j)^i`. -/
def encodeVec {k : ℕ} (α : Fin n → F) (m : Fin k → F) : Fin n → F :=
  fun j => ∑ i, m i * α j ^ (i : ℕ)

omit [DecidableEq F] in
lemma encode_msgPoly {k : ℕ} (α : Fin n → F) (m : Fin k → F) :
    encode α (msgPoly m) = encodeVec α m := by
  funext j; simp [msgPoly, encodeVec, eval_finsetSum]

/-- Brute-force (maximum-likelihood within radius `e`) decoder over a finite field: the set of
all messages whose codeword is within Hamming distance `e` of the received word. -/
def bruteDecode [Fintype F] {k : ℕ} (α : Fin n → F) (e : ℕ) (r : Fin n → F) :
    Finset (Fin k → F) :=
  {m | hammingDist (encodeVec α m) r ≤ e}

/-- Correctness of the brute-force decoder: within the unique-decoding radius
(`2e + k ≤ n`) it returns exactly the transmitted message. -/
theorem bruteDecode_eq [Fintype F] {k e : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    (hn : 2 * e + k ≤ n) (m : Fin k → F) (r : Fin n → F)
    (hm : hammingDist (encodeVec α m) r ≤ e) : bruteDecode α e r = {m} := by
  ext m'
  simp only [bruteDecode, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    apply msgPoly_injective
    apply unique_decoding hα ∅ r (e := e) (by simp; omega) (msgPoly_mem m') (msgPoly_mem m)
    · refine le_trans (card_le_card (fun i hi => ?_)) h
      rw [← encode_msgPoly]; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.2⟩
    · refine le_trans (card_le_card (fun i hi => ?_)) hm
      rw [← encode_msgPoly]; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.2⟩
  · rintro rfl; exact hm

/-! ### Syndromes and the generator-polynomial (BCH) view -/

section BCH

open Module

omit [DecidableEq F]

/-- **Syndromes** of a received word `c` (ZXing's view). Reading `c` as the polynomial
`c(x) = ∑ⱼ c j xʲ`, the `l`-th syndrome is `c(ω^(b+l))` for `l = 0, …, n-k-1`; `b` is the
generator base (QR: `b = 0`; Data Matrix / Aztec: `b = 1`). -/
def syndrome (ω : F) (b k : ℕ) : (Fin n → F) →ₗ[F] (Fin (n - k) → F) where
  toFun c l := ∑ j, c j * (ω ^ (b + (l : ℕ))) ^ (j : ℕ)
  map_add' c d := by ext l; simp [add_mul, sum_add_distrib]
  map_smul' a c := by ext l; simp [mul_sum, mul_assoc]

/-- The (twisted) evaluation-view encoder at the points `ω⁰, …, ω^(n-1)`:
`c j = τ^j · p(ω^j)`. For narrow-sense codes (`b = 1`) take `τ = 1`, which is plain RS
evaluation encoding; in general `τ = ω^(1-b)`. -/
noncomputable def twistedEncode (ω τ : F) (k : ℕ) : degreeLT F k →ₗ[F] (Fin n → F) where
  toFun p j := τ ^ (j : ℕ) * (p : F[X]).eval (ω ^ (j : ℕ))
  map_add' p q := by ext j; simp [mul_add]
  map_smul' a p := by ext j; simp; ring

/-- Geometric sums of nontrivial `n`-th roots of unity vanish. -/
lemma geom_zero {ω : F} (hω : IsPrimitiveRoot ω n) {e : ℕ} (he0 : e ≠ 0) (hen : e < n) :
    ∑ j : Fin n, (ω ^ e) ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (ω ^ e) ^ j), geom_sum_eq (hω.pow_ne_one_of_pos_of_lt he0 hen)]
  rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]

/-- Every evaluation-view codeword has zero syndromes. -/
theorem twisted_le_ker {ω τ : F} {b k : ℕ} (hω : IsPrimitiveRoot ω n) (hτ : τ * ω ^ b = ω) :
    LinearMap.range (twistedEncode (n := n) ω τ k) ≤ LinearMap.ker (syndrome ω b k) := by
  rintro c ⟨p, rfl⟩
  rw [LinearMap.mem_ker]
  funext l
  have hp := mem_degreeLT.1 p.2
  simp only [syndrome, twistedEncode, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  have hpn : (p : F[X]).natDegree < k ∨ (p : F[X]) = 0 := by
    by_cases h0 : (p : F[X]) = 0
    · exact Or.inr h0
    · left; rw [degree_eq_natDegree h0] at hp; exact_mod_cast hp
  rcases hpn with hpn | h0
  swap
  · simp [h0]
  simp_rw [eval_eq_sum_range' hpn, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have : ∀ j : Fin n, τ ^ (j : ℕ) * ((p : F[X]).coeff m * (ω ^ (j : ℕ)) ^ m) * (ω ^ (b + (l : ℕ))) ^ (j : ℕ)
      = (p : F[X]).coeff m * (ω ^ (1 + m + l)) ^ (j : ℕ) := by
    intro j
    have : ω ^ (1 + m + (l : ℕ)) = τ * ω ^ m * ω ^ (b + (l : ℕ)) := by
      rw [mul_comm τ, mul_assoc, pow_add ω b, ← mul_assoc τ, hτ]; ring
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← mul_sum, geom_zero hω (by omega) (by omega), mul_zero]

/-- The syndrome map is onto (Lagrange interpolation at the `n - k` distinct points
`ω^(b+l)`), so its kernel has dimension exactly `k`. -/
theorem syndrome_surjective {ω : F} {b k : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    Function.Surjective (syndrome (n := n) ω b k) := by
  intro y
  set v : Fin (n - k) → F := fun l => ω ^ (b + (l : ℕ)) with hv
  have hvinj : Set.InjOn v (univ : Finset (Fin (n - k))) := by
    intro l _ l' _ h
    simp only [hv, pow_add] at h
    have := mul_left_cancel₀ (pow_ne_zero b (hω.ne_zero hn.ne')) h
    exact Fin.ext (hω.pow_inj (by omega) (by omega) this)
  set P := Lagrange.interpolate univ v y with hP
  have hPdeg : P.degree < n - k := by
    have := Lagrange.degree_interpolate_lt (s := univ) (r := y) hvinj
    rw [card_univ, Fintype.card_fin] at this
    exact this
  refine ⟨fun j => P.coeff j, ?_⟩
  funext l
  simp only [syndrome, LinearMap.coe_mk, AddHom.coe_mk]
  have hPn : P.natDegree < n := by
    by_cases h0 : P = 0
    · simp [h0]; exact hn
    · rw [degree_eq_natDegree h0] at hPdeg
      have : P.natDegree < n - k := by exact_mod_cast hPdeg
      omega
  rw [Fin.sum_univ_eq_sum_range (fun j => P.coeff j * (ω ^ (b + (l : ℕ))) ^ j),
    ← eval_eq_sum_range' hPn]
  exact Lagrange.eval_interpolate_at_node y hvinj (mem_univ l)

/-- The twisted evaluation encoder is injective (`k ≤ n`, `τ ≠ 0`). -/
theorem twistedEncode_injective {ω τ : F} {k : ℕ} (hω : IsPrimitiveRoot ω n) (hτ : τ ≠ 0)
    (hk : k ≤ n) : Function.Injective (twistedEncode (n := n) ω τ k) := by
  intro p q h
  apply Subtype.ext
  -- reuse distinct-points argument
  have hinj : Set.InjOn (fun j : Fin n => ω ^ (j : ℕ)) (univ : Finset (Fin n)) :=
    fun i _ j _ hij => Fin.ext (hω.pow_inj i.2 j.2 hij)
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := univ) hinj
  · have := (degreeLT F k).sub_mem p.2 q.2
    rw [mem_degreeLT] at this
    simp only [card_univ, Fintype.card_fin]
    exact this.trans_le (by exact_mod_cast hk)
  · intro j _
    have := congrFun h j
    simp only [twistedEncode, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact mul_left_cancel₀ (pow_ne_zero _ hτ) this

/-- **BCH view = evaluation view.** With `ω` a primitive `n`-th root of unity and
`τ · ω^b = ω`, the evaluation-view RS code (messages of degree `< k`) is exactly the set of words
whose `n - k` syndromes `c(ω^b), …, c(ω^(b+n-k-1))` vanish. -/
theorem twisted_range_eq_ker {ω τ : F} {b k : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (hτ : τ * ω ^ b = ω) (hk : k ≤ n) :
    LinearMap.range (twistedEncode (n := n) ω τ k) = LinearMap.ker (syndrome ω b k) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl; simp at hτ; exact hω.ne_zero hn.ne' hτ.symm
  apply Submodule.eq_of_le_of_finrank_le (twisted_le_ker hω hτ)
  have h1 := LinearMap.finrank_range_add_finrank_ker (syndrome (n := n) ω b k)
  rw [LinearMap.range_eq_top.2 (syndrome_surjective hω hn), finrank_top] at h1
  have h2 := LinearMap.finrank_range_of_inj (twistedEncode_injective hω hτ0 hk)
  simp only [finrank_fin_fun] at h1
  rw [h2, (degreeLTEquiv F k).finrank_eq, finrank_fin_fun]
  omega

/-- The RS **generator polynomial** `g(x) = ∏_{l < m} (x - ω^(b+l))` (ZXing's
`ReedSolomonEncoder` builds exactly this with `m = n - k`). -/
noncomputable def genPoly (ω : F) (b m : ℕ) : F[X] := ∏ l : Fin m, (X - C (ω ^ (b + (l : ℕ))))

/-- A word read as a polynomial, `c(x) = ∑ⱼ c j xʲ`. -/
noncomputable def wordPoly (c : Fin n → F) : F[X] := ∑ j, C (c j) * X ^ (j : ℕ)

/-- All syndromes vanish iff the generator polynomial divides the word polynomial
(systematic RS encoding in barcodes appends the remainder of `m(x)·x^(n-k)` mod `g`). -/
theorem syndrome_eq_zero_iff_genPoly_dvd {ω : F} {b k : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : 0 < n) (c : Fin n → F) :
    syndrome ω b k c = 0 ↔ genPoly ω b (n - k) ∣ wordPoly c := by
  have hev : ∀ l : Fin (n - k), (wordPoly c).eval (ω ^ (b + (l : ℕ))) = syndrome ω b k c l := by
    intro l; simp [wordPoly, syndrome, eval_finsetSum]
  have hvinj : Function.Injective (fun l : Fin (n - k) => ω ^ (b + (l : ℕ))) := by
    intro l l' h
    simp only [pow_add] at h
    have := mul_left_cancel₀ (pow_ne_zero b (hω.ne_zero hn.ne')) h
    exact Fin.ext (hω.pow_inj (by omega) (by omega) this)
  constructor
  · intro h
    refine Finset.prod_dvd_of_coprime ?_ (fun l _ => ?_)
    · intro l _ l' _ hll'
      exact pairwise_coprime_X_sub_C hvinj hll'
    · rw [dvd_iff_isRoot, IsRoot, hev, h, Pi.zero_apply]
  · intro h
    unfold genPoly at h
    funext l
    rw [Pi.zero_apply, ← hev]
    have : X - C (ω ^ (b + (l : ℕ))) ∣ wordPoly c :=
      (Finset.dvd_prod_of_mem (fun l : Fin (n - k) => X - C (ω ^ (b + (l : ℕ))))
        (mem_univ l)).trans h
    exact IsRoot.def.1 (dvd_iff_isRoot.1 this)

/-- **ZXing's code equals the evaluation code.** A word `c` is a codeword in the
generator-polynomial sense (`g ∣ c(x)`) iff it is the twisted evaluation encoding of a message
polynomial of degree `< k`. -/
theorem genPoly_dvd_iff {ω τ : F} {b k : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (hτ : τ * ω ^ b = ω) (hk : k ≤ n) (c : Fin n → F) :
    genPoly ω b (n - k) ∣ wordPoly c ↔
      ∃ p ∈ degreeLT F k, c = fun j : Fin n => τ ^ (j : ℕ) * p.eval (ω ^ (j : ℕ)) := by
  rw [← syndrome_eq_zero_iff_genPoly_dvd (k := k) hω hn, ← LinearMap.mem_ker,
    ← twisted_range_eq_ker hω hn hτ hk, LinearMap.mem_range]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩

end BCH

/-! ### Concrete sanity checks -/

section Examples

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_929 : Fact (Nat.Prime 929) := ⟨by norm_num⟩

/-- Evaluation points `0, 1, …, 5` in `ZMod 7`. -/
def α7 : Fin 6 → ZMod 7 := fun j => (j : ℕ)

lemma α7_injective : Function.Injective α7 := by decide

/-- Message `3 + 5X` encodes to `(3, 1, 6, 4, 2, 0)` over `ZMod 7`. -/
example : encodeVec α7 ![3, 5] = ![3, 1, 6, 4, 2, 0] := by decide

/-- Received word: the codeword with two symbol errors (positions 1 and 4). -/
def r7 : Fin 6 → ZMod 7 := ![3, 4, 6, 4, 0, 0]

example : hammingDist (encodeVec α7 ![3, 5]) r7 = 2 := by decide

/-- Encode → corrupt (2 errors) → decode, checked exhaustively by `decide`: the only
message within distance 2 of `r7` is `3 + 5X`. -/
example : bruteDecode (k := 2) α7 2 r7 = {![3, 5]} := by decide

/-- The same fact, derived from the general theorem `bruteDecode_eq` (`n = 6, k = 2, e = 2`). -/
example : bruteDecode (k := 2) α7 2 r7 = {![3, 5]} :=
  bruteDecode_eq α7_injective (by norm_num) _ _ (by decide)

/-- Evaluation points `1, …, 6` in PDF417's field `ZMod 929`. -/
def α929 : Fin 6 → ZMod 929 := fun j => ((j : ℕ) + 1 : ℕ)

lemma α929_injective : Function.Injective α929 := by decide

/-- Received PDF417-style word: codeword of `100 + 7X` = `(107,114,121,128,135,142)` with
errors in positions 0 and 3. -/
def r929 : Fin 6 → ZMod 929 := ![500, 114, 121, 9, 135, 142]

/-- **Berlekamp–Welch over GF(929), concretely.** The error locator `E = (X-1)(X-4)` and
`Q = 7X³ + 65X² - 472X + 400` solve the key equation for `r929`, and `Q / E` is the
transmitted message `100 + 7X`. -/
example :
    (C 7 * X ^ 3 + C 65 * X ^ 2 - C 472 * X + C 400 : (ZMod 929)[X]) /
      (X ^ 2 - C 5 * X + C 4 : (ZMod 929)[X]) = C 100 + C 7 * X := by
  have hp : (C 100 + C 7 * X : (ZMod 929)[X]) ∈ degreeLT (ZMod 929) 2 := by
    rw [mem_degreeLT]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (degree_C_le).trans_lt (by norm_num)
    · exact (degree_C_mul_X_le _).trans_lt (by norm_num)
  have henc : encode α929 (C 100 + C 7 * X) = ![107, 114, 121, 128, 135, 142] := by
    funext j; fin_cases j <;> simp [α929] <;> decide
  refine bw_div α929_injective hp r929 (e := 2) (by rw [henc]; decide) (by norm_num)
    (E := X ^ 2 - C 5 * X + C 4) ?_ ?_ ?_ ?_
  · intro h
    have := congrArg (fun f => f.coeff 2) h
    simp at this
  · exact (degree_add_le _ _).trans (max_le ((degree_sub_le _ _).trans (max_le
      (by rw [degree_X_pow]) ((degree_C_mul_X_le _).trans (by norm_num))))
      (degree_C_le.trans (by norm_num)))
  · refine (degree_add_le _ _).trans_lt (max_lt ((degree_sub_le _ _).trans_lt (max_lt
      ((degree_add_le _ _).trans_lt (max_lt ?_ ?_)) ?_)) ?_)
    · exact (degree_C_mul_X_pow_le _ _).trans_lt (by norm_num)
    · exact (degree_C_mul_X_pow_le _ _).trans_lt (by norm_num)
    · exact (degree_C_mul_X_le _).trans_lt (by norm_num)
    · exact degree_C_le.trans_lt (by norm_num)
  · intro j; fin_cases j <;> simp [α929, r929] <;> decide

end Examples

end RoboLean.Barcode.ReedSolomon
