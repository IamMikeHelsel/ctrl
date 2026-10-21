import Mathlib

/-!
# Check digits and small block codes in real barcode symbologies

Applied, sorry-free error-detection / error-correction guarantees, stated against the actual
parameters of the standards, together with executable (decidable / `#eval`-able) checkers and
decoders.

1. **GS1 (UPC-A, EAN-13, EAN-8, GTIN-14)**, weights 3,1 alternating mod 10: every single-digit
   error is detected (`gs1_single_error`); an adjacent transposition `a b ↦ b a` escapes iff
   `a = b ∨ |a - b| = 5` (`gs1_adjacent_swap_iff`); the check digit is computed correctly and is
   unique (`gs1_snoc_valid_iff`, `gs1CheckDigit_existsUnique`).
2. **ISBN-10** (weights 10..1 mod 11, `X` = 10) detects all single errors and *all*
   transpositions (`isbn10_single_error`, `isbn10_swap`); **ISBN-13** = EAN-13.
3. **Code 128** (`start + ∑ i·vᵢ mod 103`): exact characterisation of undetected substitutions
   and transpositions (`code128_subst_iff`, `code128_swap_iff`, `code128_swap_iff_of_le`).
4. **Luhn**: all single errors, all adjacent transpositions except `09 ↔ 90`
   (`luhn_single_error`, `luhn_adjacent_swap_iff`).
5. **QR format information** (BCH(15,5), generator `0x537`, mask `0x5412`): the 32 codewords
   equal ZXing's table, minimum distance exactly 7, and the nearest-codeword decoder corrects
   3 errors (`format_min_dist`, `formatDecode_correct`).
6. **QR version information** ((18,6) Golay-derived, generator `0x1F25`): minimum distance 8 over
   versions 7–40 (indeed over the full code), and the decoder corrects 3 errors
   (`version_min_dist`, `versionDecode_correct`).
7. **GF(256)** for QR (`0x11D`) and Data Matrix (`0x12D`): irreducibility over `ZMod 2` and
   primitivity of `α = x` as genuine `Polynomial`/`AdjoinRoot` statements
   (`qr_irreducible`, `qr_orderOf_root`, `dm_irreducible`, `dm_orderOf_root`), obtained from
   bit-vector computations via a verified bridge `toPoly : ℕ → (ZMod 2)[X]`
   (XOR = `+`, shift = `· * X^k`, carry-less product = `*`).

All finite checks use `decide` (elaborator) or `decide +kernel` (kernel only); no `native_decide`.
-/

open Finset

namespace RoboLean.Barcode.CheckDigits

/-! ## Generic position-sum codes -/

section Framework

variable {α : Type*} [AddCommGroup α] {n : ℕ}

/-- Generic position-dependent sum code `∑ i, g i (d i)` over an additive group. GS1 (weights), ISBN, Code 128 and Luhn are all instances. -/
def psum (g : Fin n → α → α) (d : Fin n → α) : α := ∑ i, g i (d i)

/-- Generic: effect of a single-symbol substitution on a position-sum code. -/
theorem psum_update (g : Fin n → α → α) (d : Fin n → α) (j : Fin n) (b : α) :
    psum g (Function.update d j b) = psum g d + (g j b - g j (d j)) := by
  unfold psum
  rw [← Finset.add_sum_erase _ _ (mem_univ j), ← Finset.add_sum_erase _ _ (mem_univ j)]
  rw [Finset.sum_congr rfl (fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)])]
  simp only [Function.update_self]
  abel

omit [AddCommGroup α] in
/-- A transposition of two distinct positions is two successive updates. -/
theorem comp_swap_eq_update (d : Fin n → α) {j k : Fin n} (h : j ≠ k) :
    d ∘ Equiv.swap j k = Function.update (Function.update d j (d k)) k (d j) := by
  funext i
  by_cases hik : i = k
  · subst hik; simp
  · by_cases hij : i = j
    · subst hij; simp [Function.update_of_ne hik]
    · simp [Equiv.swap_apply_of_ne_of_ne hij hik, Function.update_of_ne hik,
        Function.update_of_ne hij]

/-- Generic: effect of transposing positions `j ≠ k` on a position-sum code. -/
theorem psum_swap (g : Fin n → α → α) (d : Fin n → α) {j k : Fin n} (h : j ≠ k) :
    psum g (d ∘ Equiv.swap j k) =
      psum g d + ((g j (d k) - g j (d j)) + (g k (d j) - g k (d k))) := by
  rw [comp_swap_eq_update d h, psum_update, psum_update, Function.update_of_ne h.symm]
  abel

/-- Generic: if the last position map is the identity, the unique valid completing check symbol is `-(sum of the rest)`. -/
theorem psum_snoc (g : Fin (n + 1) → α → α) (hg : g (Fin.last n) = id) (d : Fin n → α) (c : α) :
    psum g (Fin.snoc (α := fun _ => α) d c) = 0 ↔
      c = -∑ i : Fin n, g i.castSucc (d i) := by
  unfold psum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hg, id]
  rw [eq_neg_iff_add_eq_zero, add_comm]

end Framework

section Weighted

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Weighted sum code `∑ i, w i * d i` (GS1 / ISBN / Code 128 checksums). -/
def wsum (w : Fin n → R) (d : Fin n → R) : R := psum (fun i x => w i * x) d

/-- Weighted code: a substituted word `update d j b` of a valid `d` is still valid iff `w j * (b - d j) = 0`. -/
theorem wsum_update_iff (w : Fin n → R) {d : Fin n → R} (hd : wsum w d = 0) (j : Fin n) (b : R) :
    wsum w (Function.update d j b) = 0 ↔ w j * (b - d j) = 0 := by
  unfold wsum at *
  rw [psum_update, hd, zero_add, mul_sub]

/-- Weighted code: transposing positions `j ≠ k` of a valid word keeps it valid iff `(w j - w k) * (d k - d j) = 0`. -/
theorem wsum_swap_iff (w : Fin n → R) {d : Fin n → R} (hd : wsum w d = 0) {j k : Fin n}
    (h : j ≠ k) :
    wsum w (d ∘ Equiv.swap j k) = 0 ↔ (w j - w k) * (d k - d j) = 0 := by
  unfold wsum at *
  rw [psum_swap _ _ h, hd, zero_add]
  constructor <;> intro H <;> linear_combination H

/-- Weighted code with last weight 1: the check symbol is uniquely `-(∑ w_i d_i)` over the data. -/
theorem wsum_snoc (w : Fin (n + 1) → R) (hw : w (Fin.last n) = 1) (d : Fin n → R) (c : R) :
    wsum w (Fin.snoc (α := fun _ => R) d c) = 0 ↔ c = -∑ i : Fin n, w i.castSucc * d i :=
  psum_snoc _ (by funext x; simp [hw]) d c

end Weighted

/-! ## 1. GS1: UPC-A, EAN-13, EAN-8 -/

/-- GS1 General Specifications §7.9 (UPC-A, EAN-13, EAN-8, GTIN-14): weight 1 on the check digit (rightmost) and alternating 3,1,3,… going left, i.e. weight 1 iff the distance from the right end is even. -/
def gs1Weight (n : ℕ) (i : Fin n) : ZMod 10 := if (n - 1 - i.val) % 2 = 0 then 1 else 3

/-- GS1 check-digit validity (UPC-A `n = 12`, EAN-13 / ISBN-13 `n = 13`, EAN-8 `n = 8`): `∑ wᵢ dᵢ ≡ 0 (mod 10)`. -/
def GS1Valid {n : ℕ} (d : Fin n → ZMod 10) : Prop := wsum (gs1Weight n) d = 0

instance {n : ℕ} (d : Fin n → ZMod 10) : Decidable (GS1Valid d) :=
  inferInstanceAs (Decidable (_ = _))

example : GS1Valid (n := 12) ![0, 3, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2] := by decide
example : GS1Valid (n := 13) ![4, 0, 0, 6, 3, 8, 1, 3, 3, 3, 9, 3, 1] := by decide
example : GS1Valid (n := 8) ![9, 6, 3, 8, 5, 0, 7, 4] := by decide
example : ¬ GS1Valid (n := 8) ![9, 6, 3, 8, 5, 0, 7, 5] := by decide

/-- GS1: the weights 1 and 3 are units mod 10. -/
lemma gs1Weight_mul_ne_zero {n : ℕ} (j : Fin n) {x : ZMod 10} (hx : x ≠ 0) :
    gs1Weight n j * x ≠ 0 := by
  unfold gs1Weight
  split_ifs
  · simpa using hx
  · revert x; decide

/-- GS1 (UPC-A / EAN-13 / EAN-8 / GTIN-14): every single-digit substitution error is detected. -/
theorem gs1_single_error {n : ℕ} {d : Fin n → ZMod 10} (hd : GS1Valid d) (j : Fin n)
    {b : ZMod 10} (hb : b ≠ d j) : ¬ GS1Valid (Function.update d j b) := by
  unfold GS1Valid at *
  rw [wsum_update_iff _ hd]
  exact gs1Weight_mul_ne_zero j (sub_ne_zero.2 hb)

/-- GS1 helper table: `±2·(b-a) ≡ 0 (mod 10)` iff `a = b` or `|a-b| = 5`. -/
lemma two_mul_sub_eq_zero_iff : ∀ a b : ZMod 10,
    ((1 - 3) * (b - a) = 0 ↔ a = b ∨ Int.natAbs ((a.val : ℤ) - b.val) = 5) ∧
    ((3 - 1) * (b - a) = 0 ↔ a = b ∨ Int.natAbs ((a.val : ℤ) - b.val) = 5) := by
  decide

/-- GS1 (UPC-A / EAN-13 / EAN-8): an adjacent transposition `a b ↦ b a` of a valid code goes undetected iff `a = b` or `|a - b| = 5`; hence a genuine adjacent transposition (`a ≠ b`) is detected iff `|a - b| ≠ 5`. -/
theorem gs1_adjacent_swap_iff {n : ℕ} {d : Fin n → ZMod 10} (hd : GS1Valid d) {j k : Fin n}
    (hjk : k.val = j.val + 1) :
    GS1Valid (d ∘ Equiv.swap j k) ↔
      d j = d k ∨ Int.natAbs (((d j).val : ℤ) - (d k).val) = 5 := by
  have hne : j ≠ k := fun h => by rw [h] at hjk; omega
  unfold GS1Valid at *
  rw [wsum_swap_iff _ hd hne]
  have hk := k.isLt
  unfold gs1Weight
  split_ifs with h1 h2 h2
  · omega
  · exact (two_mul_sub_eq_zero_iff _ _).1
  · exact (two_mul_sub_eq_zero_iff _ _).2
  · omega

/-- GS1: the check digit (rightmost position) has weight 1. -/
theorem gs1Weight_last (n : ℕ) : gs1Weight (n + 1) (Fin.last n) = 1 := by
  simp [gs1Weight]

/-- GS1 check-digit computation: `c = -(∑ wᵢ dᵢ) mod 10` over the data digits (weights of the full code). -/
def gs1CheckDigit {n : ℕ} (d : Fin n → ZMod 10) : ZMod 10 :=
  -∑ i : Fin n, gs1Weight (n + 1) i.castSucc * d i

/-- GS1: appending `c` to data `d` yields a valid code iff `c = gs1CheckDigit d` (correctness of the check-digit algorithm). -/
theorem gs1_snoc_valid_iff {n : ℕ} (d : Fin n → ZMod 10) (c : ZMod 10) :
    GS1Valid (Fin.snoc (α := fun _ => ZMod 10) d c) ↔ c = gs1CheckDigit d :=
  wsum_snoc _ (gs1Weight_last n) d c

/-- GS1: every data string has exactly one completing check digit. -/
theorem gs1CheckDigit_existsUnique {n : ℕ} (d : Fin n → ZMod 10) :
    ∃! c : ZMod 10, GS1Valid (Fin.snoc (α := fun _ => ZMod 10) d c) :=
  ⟨gs1CheckDigit d, (gs1_snoc_valid_iff d _).2 rfl, fun _ h => (gs1_snoc_valid_iff d _).1 h⟩

example : gs1CheckDigit (n := 11) ![0, 3, 6, 0, 0, 0, 2, 9, 1, 4, 5] = 2 := by decide

/-- GS1: prefixing a `0` does not change validity; in particular a UPC-A code is valid iff the EAN-13 code `0 ++ upc` is (UPC-A ⊂ EAN-13). -/
theorem gs1_cons_zero {n : ℕ} (d : Fin n → ZMod 10) :
    GS1Valid (Fin.cons (α := fun _ => ZMod 10) 0 d) ↔ GS1Valid d := by
  unfold GS1Valid wsum psum
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
  have hw : ∀ i : Fin n, gs1Weight (n + 1) i.succ = gs1Weight n i := by
    intro i
    unfold gs1Weight
    rw [Fin.val_succ, show n + 1 - 1 - (i.val + 1) = n - 1 - i.val by omega]
  simp only [hw]

/-! ## ISBN-13 = EAN-13 -/

/-- ISBN-13 (ISO 2108:2005) is exactly an EAN-13 (GS1) code with prefix 978/979. -/
abbrev ISBN13Valid (d : Fin 13 → ZMod 10) : Prop := GS1Valid d

example : ISBN13Valid ![9, 7, 8, 0, 3, 0, 6, 4, 0, 6, 1, 5, 7] := by decide

/-- ISBN-13 / EAN-13 do **not** detect all transpositions: swapping positions 0 and 2 (equal
weights) of 978-0-306-40615-7 gives another valid ISBN-13 (contrast with `isbn10_swap`). -/
example : ISBN13Valid (![9, 7, 8, 0, 3, 0, 6, 4, 0, 6, 1, 5, 7] ∘ Equiv.swap 0 2) := by decide

/-- ISBN-13: every single-digit substitution is detected (EAN-13 behaviour). -/
theorem isbn13_single_error {d : Fin 13 → ZMod 10} (hd : ISBN13Valid d) (j : Fin 13)
    {b : ZMod 10} (hb : b ≠ d j) : ¬ ISBN13Valid (Function.update d j b) :=
  gs1_single_error hd j hb

/-- ISBN-13: an adjacent transposition of distinct digits `a, b` is detected iff `|a - b| ≠ 5` (EAN-13 behaviour). -/
theorem isbn13_adjacent_swap_iff {d : Fin 13 → ZMod 10} (hd : ISBN13Valid d) {j k : Fin 13}
    (hjk : k.val = j.val + 1) (hne : d j ≠ d k) :
    ¬ ISBN13Valid (d ∘ Equiv.swap j k) ↔ Int.natAbs (((d j).val : ℤ) - (d k).val) ≠ 5 := by
  unfold ISBN13Valid at *
  rw [gs1_adjacent_swap_iff hd hjk]
  simp [hne]

/-! ## 2. ISBN-10 -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 103) := ⟨by norm_num⟩

/-- ISBN-10 (ISO 2108:1992): weights 10, 9, …, 1 from left to right. -/
def isbn10Weight (i : Fin 10) : ZMod 11 := ((10 - i.val : ℕ) : ZMod 11)

/-- ISBN-10 validity: `∑ (10-i)·dᵢ ≡ 0 (mod 11)`, digits in `ZMod 11` (`X` = 10). -/
def ISBN10Valid (d : Fin 10 → ZMod 11) : Prop := wsum isbn10Weight d = 0

instance (d : Fin 10 → ZMod 11) : Decidable (ISBN10Valid d) :=
  inferInstanceAs (Decidable (_ = _))

example : ISBN10Valid ![0, 3, 0, 6, 4, 0, 6, 1, 5, 2] := by decide
example : ISBN10Valid ![0, 8, 0, 4, 4, 2, 9, 5, 7, 10] := by decide

/-- ISBN-10: all weights are nonzero mod 11. -/
lemma isbn10Weight_ne_zero : ∀ i, isbn10Weight i ≠ 0 := by decide
/-- ISBN-10: the weights are pairwise distinct mod 11. -/
lemma isbn10Weight_injective : Function.Injective isbn10Weight := by decide

/-- ISBN-10 (ISO 2108): every single-digit substitution error is detected. -/
theorem isbn10_single_error {d : Fin 10 → ZMod 11} (hd : ISBN10Valid d) (j : Fin 10)
    {b : ZMod 11} (hb : b ≠ d j) : ¬ ISBN10Valid (Function.update d j b) := by
  unfold ISBN10Valid at *
  rw [wsum_update_iff _ hd]
  exact mul_ne_zero (isbn10Weight_ne_zero j) (sub_ne_zero.2 hb)

/-- ISBN-10 (ISO 2108): every transposition of two distinct digits — at any two positions, adjacent or not — is detected. -/
theorem isbn10_swap {d : Fin 10 → ZMod 11} (hd : ISBN10Valid d) {j k : Fin 10}
    (hjk : d j ≠ d k) : ¬ ISBN10Valid (d ∘ Equiv.swap j k) := by
  have hne : j ≠ k := fun h => hjk (h ▸ rfl)
  unfold ISBN10Valid at *
  rw [wsum_swap_iff _ hd hne]
  exact mul_ne_zero (sub_ne_zero.2 fun h => hne (isbn10Weight_injective h))
    (sub_ne_zero.2 hjk.symm)

/-- ISBN-10 check digit: `c = -(∑_{i<9} (10-i)·dᵢ) mod 11` (`10` printed as `X`). -/
def isbn10CheckDigit (d : Fin 9 → ZMod 11) : ZMod 11 :=
  -∑ i : Fin 9, isbn10Weight i.castSucc * d i

/-- ISBN-10: appending `c` to 9 data digits gives a valid ISBN iff `c = isbn10CheckDigit d`. -/
theorem isbn10_snoc_valid_iff (d : Fin 9 → ZMod 11) (c : ZMod 11) :
    ISBN10Valid (Fin.snoc (α := fun _ => ZMod 11) d c) ↔ c = isbn10CheckDigit d :=
  wsum_snoc _ (by decide) d c

example : isbn10CheckDigit ![0, 8, 0, 4, 4, 2, 9, 5, 7] = 10 := by decide

/-! ## 3. Code 128 -/

/-- Code 128 (ISO/IEC 15417 §4.7.2) position weights for the full symbol vector `[start, data₁, …, dataₙ, check]`: start has weight 1, `dataᵢ` weight `i`, and the check symbol weight `102 ≡ -1 (mod 103)`. -/
def code128WeightNat (n : ℕ) (i : Fin (n + 2)) : ℕ :=
  if i.val = n + 1 then 102 else if i.val = 0 then 1 else i.val

/-- Code 128 weights as elements of `ZMod 103`. -/
def code128Weight (n : ℕ) (i : Fin (n + 2)) : ZMod 103 := (code128WeightNat n i : ZMod 103)

/-- Code 128 (ISO/IEC 15417): a symbol vector is valid iff `check ≡ start + ∑ i·dataᵢ (mod 103)`, written as a single weighted sum. -/
def Code128Valid {n : ℕ} (x : Fin (n + 2) → ZMod 103) : Prop := wsum (code128Weight n) x = 0

instance {n : ℕ} (x : Fin (n + 2) → ZMod 103) : Decidable (Code128Valid x) :=
  inferInstanceAs (Decidable (_ = _))

example : Code128Valid (n := 7) ![104, 48, 42, 42, 17, 18, 19, 35, 55] := by decide

/-- Code 128 (ISO/IEC 15417): `Code128Valid [start, data, check] ↔ check = (start + ∑ i·dataᵢ) mod 103` — the weighted-sum encoding matches the standard's checksum rule. -/
theorem code128_valid_iff {n : ℕ} (start : ZMod 103) (data : Fin n → ZMod 103)
    (check : ZMod 103) :
    Code128Valid (Fin.snoc (α := fun _ => ZMod 103) (Fin.cons start data) check) ↔
      check = start + ∑ i : Fin n, ((i.val + 1 : ℕ) : ZMod 103) * data i := by
  unfold Code128Valid wsum psum
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hl : code128Weight n (Fin.last (n + 1)) = -1 := by
    simp [code128Weight, code128WeightNat]; decide
  have h0 : code128Weight n (Fin.castSucc 0) = 1 := by
    simp [code128Weight, code128WeightNat]
  have hs : ∀ i : Fin n,
      code128Weight n (Fin.succ i).castSucc = ((i.val + 1 : ℕ) : ZMod 103) := by
    intro i
    have := i.isLt
    simp only [code128Weight, code128WeightNat, Fin.val_castSucc, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega)]
  simp only [hl, h0, hs, Fin.snoc_castSucc, Fin.snoc_last, Fin.cons_zero, Fin.cons_succ,
    one_mul]
  constructor <;> intro H <;> linear_combination -H

/-- Code 128: a single symbol substitution escapes detection iff it hits a data position `p` with `103 ∣ p` (only possible for messages with ≥ 103 data symbols). -/
theorem code128_subst_iff {n : ℕ} {x : Fin (n + 2) → ZMod 103} (hx : Code128Valid x)
    (p : Fin (n + 2)) {b : ZMod 103} (hb : b ≠ x p) :
    Code128Valid (Function.update x p b) ↔ (p.val ≠ 0 ∧ p.val ≠ n + 1 ∧ 103 ∣ p.val) := by
  unfold Code128Valid at *
  rw [wsum_update_iff _ hx, mul_eq_zero, or_iff_left (sub_ne_zero.2 hb), code128Weight,
    ZMod.natCast_eq_zero_iff, code128WeightNat]
  split_ifs <;> omega

/-- Code 128: with at most 102 data symbols, every single symbol substitution (start, data, or check) is detected. -/
theorem code128_subst_detected {n : ℕ} (hn : n ≤ 102) {x : Fin (n + 2) → ZMod 103}
    (hx : Code128Valid x) (p : Fin (n + 2)) {b : ZMod 103} (hb : b ≠ x p) :
    ¬ Code128Valid (Function.update x p b) := by
  rw [code128_subst_iff hx p hb]
  have := p.isLt
  omega

/-- Code 128: a transposition of two distinct symbol values escapes detection iff the two positions have the same weight mod 103 (exact characterisation). -/
theorem code128_swap_iff {n : ℕ} {x : Fin (n + 2) → ZMod 103} (hx : Code128Valid x)
    {p q : Fin (n + 2)} (hpq : x p ≠ x q) :
    Code128Valid (x ∘ Equiv.swap p q) ↔
      code128WeightNat n p % 103 = code128WeightNat n q % 103 := by
  have hne : p ≠ q := fun h => hpq (h ▸ rfl)
  unfold Code128Valid at *
  rw [wsum_swap_iff _ hx hne, mul_eq_zero, or_iff_left (sub_ne_zero.2 hpq.symm), sub_eq_zero,
    code128Weight, code128Weight, ZMod.natCast_eq_natCast_iff']

/-- Code 128: for `1 ≤ n ≤ 101` data symbols, the only transposition of distinct values that escapes detection is start ↔ first data symbol (both weight 1). In practice the start symbol has a distinct bar pattern, so this cannot arise from mis-reading. -/
theorem code128_swap_iff_of_le {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 101) {x : Fin (n + 2) → ZMod 103}
    (hx : Code128Valid x) {p q : Fin (n + 2)} (hpq : x p ≠ x q) :
    Code128Valid (x ∘ Equiv.swap p q) ↔
      (p.val = 0 ∧ q.val = 1) ∨ (p.val = 1 ∧ q.val = 0) := by
  have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h ▸ rfl)
  rw [code128_swap_iff hx hpq]
  have := p.isLt
  have := q.isLt
  unfold code128WeightNat
  split_ifs <;> constructor <;> intro <;> omega

/-- Code 128: the start ↔ first-data transposition really escapes (here Start B = 104 and
data `P` = 48 in "PJJ123C"). -/
example : Code128Valid (n := 7)
    (![104, 48, 42, 42, 17, 18, 19, 35, 55] ∘ Equiv.swap 0 1) := by decide

/-! ## 4. Luhn -/

/-- Luhn (ISO/IEC 7812-1 Annex B): doubling with digit sum, `x ↦ 2x` (x < 5), `x ↦ 2x - 9 ≡ 2x + 1` (x ≥ 5). -/
def luhnDouble (x : ZMod 10) : ZMod 10 := if x.val < 5 then 2 * x else 2 * x + 1

/-- Luhn: every second digit, counting the check digit (rightmost) as position 0, is doubled. -/
def luhnMap (n : ℕ) (i : Fin n) : ZMod 10 → ZMod 10 :=
  if (n - 1 - i.val) % 2 = 1 then luhnDouble else id

/-- Luhn validity (ISO/IEC 7812-1): `∑ gᵢ(dᵢ) ≡ 0 (mod 10)`. -/
def LuhnValid {n : ℕ} (d : Fin n → ZMod 10) : Prop := psum (luhnMap n) d = 0

instance {n : ℕ} (d : Fin n → ZMod 10) : Decidable (LuhnValid d) :=
  inferInstanceAs (Decidable (_ = _))

example : LuhnValid (n := 11) ![7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3] := by decide
example : ¬ LuhnValid (n := 11) ![7, 9, 9, 2, 7, 3, 9, 8, 7, 3, 1] := by decide

/-- Luhn: the doubling map is a permutation of the digits. -/
lemma luhnDouble_injective : Function.Injective luhnDouble := by decide

/-- Luhn: every position map is injective. -/
lemma luhnMap_injective {n : ℕ} (i : Fin n) : Function.Injective (luhnMap n i) := by
  unfold luhnMap; split_ifs
  · exact luhnDouble_injective
  · exact Function.injective_id

/-- Luhn (ISO/IEC 7812-1): every single-digit substitution error is detected. -/
theorem luhn_single_error {n : ℕ} {d : Fin n → ZMod 10} (hd : LuhnValid d) (j : Fin n)
    {b : ZMod 10} (hb : b ≠ d j) : ¬ LuhnValid (Function.update d j b) := by
  unfold LuhnValid at *
  rw [psum_update, hd, zero_add, sub_eq_zero]
  exact fun h => hb (luhnMap_injective j h)

/-- Luhn helper table: `(f a - a) = (f b - b)` iff `a = b` or `{a, b} = {0, 9}`. -/
lemma luhn_swap_table : ∀ a b : ZMod 10,
    ((luhnDouble b - luhnDouble a + (id a - id b) = 0 ↔
        a = b ∨ (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0)) ∧
     (id b - id a + (luhnDouble a - luhnDouble b) = 0 ↔
        a = b ∨ (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0))) := by
  decide

/-- Luhn (ISO/IEC 7812-1): an adjacent transposition of a valid number goes undetected iff the digits are equal or are `0, 9` / `9, 0`. So all adjacent transpositions except 09 ↔ 90 are detected. -/
theorem luhn_adjacent_swap_iff {n : ℕ} {d : Fin n → ZMod 10} (hd : LuhnValid d) {j k : Fin n}
    (hjk : k.val = j.val + 1) :
    LuhnValid (d ∘ Equiv.swap j k) ↔
      d j = d k ∨ (d j = 0 ∧ d k = 9) ∨ (d j = 9 ∧ d k = 0) := by
  have hne : j ≠ k := fun h => by rw [h] at hjk; omega
  unfold LuhnValid at *
  rw [psum_swap _ _ hne, hd, zero_add]
  have hk := k.isLt
  unfold luhnMap
  split_ifs with h1 h2 h2
  · omega
  · exact (luhn_swap_table _ _).1
  · exact (luhn_swap_table _ _).2
  · omega

/-- Luhn: the check digit (rightmost) is not doubled. -/
theorem luhnMap_last (n : ℕ) : luhnMap (n + 1) (Fin.last n) = id := by
  simp [luhnMap]

/-- Luhn check-digit computation. -/
def luhnCheckDigit {n : ℕ} (d : Fin n → ZMod 10) : ZMod 10 :=
  -∑ i : Fin n, luhnMap (n + 1) i.castSucc (d i)

/-- Luhn: appending `c` gives a valid number iff `c = luhnCheckDigit d`. -/
theorem luhn_snoc_valid_iff {n : ℕ} (d : Fin n → ZMod 10) (c : ZMod 10) :
    LuhnValid (Fin.snoc (α := fun _ => ZMod 10) d c) ↔ c = luhnCheckDigit d :=
  psum_snoc _ (luhnMap_last n) d c

example : luhnCheckDigit (n := 10) ![7, 9, 9, 2, 7, 3, 9, 8, 7, 1] = 3 := by decide

/-! ## Bit vectors, Hamming distance, nearest-codeword decoding -/

/-- One step of GF(2)[x] long division on bit vectors: cancel bit `i + deg` with `g·xⁱ`. -/
def polyModStep (g deg : ℕ) (a i : ℕ) : ℕ :=
  if a.testBit (i + deg) then a ^^^ (g <<< i) else a

/-- Remainder of the bit-vector polynomial `a` (degree `< len + deg`) modulo `g` (degree `deg`) — the BCH remainder used in ISO/IEC 18004 Annex C/D. -/
def polyMod (g deg len a : ℕ) : ℕ := (List.range len).reverse.foldl (polyModStep g deg) a

/-- Hamming distance between the low `k` bits of two naturals. -/
def hd : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, x, y => hd k x y + (if x.testBit k = y.testBit k then 0 else 1)

/-- Hamming distance is symmetric. -/
theorem hd_comm (k x y : ℕ) : hd k x y = hd k y x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [hd, ih, eq_comm]

/-- Triangle inequality for the Hamming distance. -/
theorem hd_triangle (k x y z : ℕ) : hd k x z ≤ hd k x y + hd k y z := by
  induction k with
  | zero => simp [hd]
  | succ k ih =>
    simp only [hd]
    generalize x.testBit k = a, y.testBit k = b, z.testBit k = c
    cases a <;> cases b <;> cases c <;> simp <;> omega

section Argmin
variable {β : Type*} (f : β → ℕ)

/-- First-minimum search (what ZXing's format/version decoders do). -/
def argminFold (init : β) (l : List β) : β :=
  l.foldl (fun b c => if f c < f b then c else b) init

/-- `argminFold` returns an element of the list that minimises `f`. -/
theorem argminFold_spec : ∀ (l : List β) (init : β),
    (argminFold f init l = init ∨ argminFold f init l ∈ l) ∧
    f (argminFold f init l) ≤ f init ∧ ∀ x ∈ l, f (argminFold f init l) ≤ f x
  | [], init => by simp [argminFold]
  | c :: l, init => by
    have ih := argminFold_spec l (if f c < f init then c else init)
    have hrw : argminFold f init (c :: l) =
        argminFold f (if f c < f init then c else init) l := rfl
    rw [hrw]
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases h : f c < f init
    · simp only [h, if_true] at h1 h2 h3 ⊢
      refine ⟨?_, by omega, ?_⟩
      · rcases h1 with h1 | h1 <;> simp [h1]
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h2
        · exact h3 x hx
    · simp only [h, if_false] at h1 h2 h3 ⊢
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1 <;> simp [h1]
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact h3 x hx

/-- If `c` is the strict unique minimiser, `argminFold` returns `c`. -/
theorem argminFold_eq {init : β} {l : List β} {c : β} (hc : c = init ∨ c ∈ l)
    (huniq : ∀ y, (y = init ∨ y ∈ l) → y ≠ c → f c < f y) : argminFold f init l = c := by
  obtain ⟨h1, h2, h3⟩ := argminFold_spec f l init
  by_contra hne
  have hlt := huniq _ h1 hne
  rcases hc with rfl | hc
  · omega
  · have := h3 c hc; omega

end Argmin

/-- Generic nearest-codeword decoder over a codeword list, accepting only if the best distance is `≤ t` (ZXing `doDecodeFormatInformation` / `decodeVersionInformation` style). -/
def nearestDecode (k t : ℕ) (enc : ℕ → ℕ) (cs : List ℕ) (r : ℕ) : Option ℕ :=
  match cs with
  | [] => none
  | c0 :: rest =>
    let c := argminFold (fun c => hd k r (enc c)) c0 rest
    if hd k r (enc c) ≤ t then some c else none

/-- Generic decoder correctness: if the code has minimum distance `D > 2t` and the received word is within `t` of codeword `c`, the decoder returns `c`. -/
theorem nearestDecode_correct {k t D : ℕ} {enc : ℕ → ℕ} {cs : List ℕ}
    (hD : ∀ a ∈ cs, ∀ b ∈ cs, a ≠ b → D ≤ hd k (enc a) (enc b)) (ht : 2 * t < D)
    {c r : ℕ} (hc : c ∈ cs) (hr : hd k r (enc c) ≤ t) : nearestDecode k t enc cs r = some c := by
  cases cs with
  | nil => simp at hc
  | cons c0 rest =>
    have huniq : ∀ y, (y = c0 ∨ y ∈ rest) → y ≠ c →
        hd k r (enc c) < hd k r (enc y) := by
      intro y hy hne
      have hy' : y ∈ c0 :: rest := by rcases hy with rfl | hy <;> simp [*]
      have h1 := hD c hc y hy' (Ne.symm hne)
      have h2 := hd_triangle k (enc c) r (enc y)
      rw [hd_comm k (enc c) r] at h2
      omega
    have hc' : c = c0 ∨ c ∈ rest := List.mem_cons.1 hc
    have := argminFold_eq (fun c => hd k r (enc c)) hc' huniq
    simp only [nearestDecode, this, if_pos hr]

/-- Generic decoder soundness: any returned value is a codeword within distance `t`. -/
theorem nearestDecode_sound {k t : ℕ} {enc : ℕ → ℕ} {cs : List ℕ} {r c : ℕ}
    (h : nearestDecode k t enc cs r = some c) : c ∈ cs ∧ hd k r (enc c) ≤ t := by
  cases cs with
  | nil => simp [nearestDecode] at h
  | cons c0 rest =>
    simp only [nearestDecode] at h
    split_ifs at h with h1
    · cases h
      refine ⟨?_, h1⟩
      rcases (argminFold_spec (fun c => hd k r (enc c)) rest c0).1 with h2 | h2
      · rw [h2]; simp
      · exact List.mem_cons_of_mem _ h2

/-! ## 5. QR format information -/

/-- ISO/IEC 18004 Annex C: format-information BCH(15,5) generator `x¹⁰+x⁸+x⁵+x⁴+x²+x+1` = `0x537`. -/
def formatGen : ℕ := 0x537
/-- ISO/IEC 18004 Annex C: format-information XOR mask `101010000010010` = `0x5412`. -/
def formatMask : ℕ := 0x5412

/-- ISO/IEC 18004 Annex C: 15-bit QR format information for 5 data bits (2-bit EC level, 3-bit mask pattern): BCH(15,5) systematic encoding, then XOR with the mask. -/
def formatEncode (d : ℕ) : ℕ := ((d <<< 10) ||| polyMod formatGen 10 5 (d <<< 10)) ^^^ formatMask

/-- ZXing `FormatInformation.FORMAT_INFO_DECODE_LOOKUP` codewords, indexed by the 5 data bits. -/
def zxingFormatTable : List ℕ :=
  [0x5412, 0x5125, 0x5E7C, 0x5B4B, 0x45F9, 0x40CE, 0x4F97, 0x4AA0, 0x77C4, 0x72F3, 0x7DAA,
   0x789D, 0x662F, 0x6318, 0x6C41, 0x6976, 0x1689, 0x13BE, 0x1CE7, 0x19D0, 0x0762, 0x0255,
   0x0D0C, 0x083B, 0x355F, 0x3068, 0x3F31, 0x3A06, 0x24B4, 0x2183, 0x2EDA, 0x2BED]

/-- ISO/IEC 18004: the 32 computed format codewords coincide with ZXing's lookup table. -/
theorem formatEncode_eq_table : (List.range 32).map formatEncode = zxingFormatTable := by
  decide

/-- ISO/IEC 18004: format codewords fit in 15 bits. -/
theorem formatEncode_lt : ∀ d ∈ List.range 32, formatEncode d < 2 ^ 15 := by decide

/-- ISO/IEC 18004: every unmasked format codeword is a multiple of the generator polynomial (BCH code membership). -/
theorem format_unmasked_multiple :
    ∀ d ∈ List.range 32, polyMod formatGen 10 5 (formatEncode d ^^^ formatMask) = 0 := by
  decide

/-- ISO/IEC 18004: the 32 QR format-information codewords have pairwise Hamming distance ≥ 7. -/
theorem format_min_dist : ∀ a ∈ List.range 32, ∀ b ∈ List.range 32, a ≠ b →
    7 ≤ hd 15 (formatEncode a) (formatEncode b) := by
  decide

/-- ISO/IEC 18004: the minimum distance of the format code is exactly 7. -/
theorem format_min_dist_attained : hd 15 (formatEncode 0) (formatEncode 1) = 7 := by
  decide

/-- QR format-information decoder: nearest of the 32 codewords, accepted if within 3 bit errors. -/
def formatDecode (r : ℕ) : Option ℕ := nearestDecode 15 3 formatEncode (List.range 32) r

/-- ISO/IEC 18004: the format decoder corrects up to 3 bit errors — if `r` is within Hamming distance 3 of the codeword for `d`, `formatDecode r = some d`. Justifies ZXing's lookup decoder. -/
theorem formatDecode_correct {d r : ℕ} (hd32 : d < 32) (hr : hd 15 r (formatEncode d) ≤ 3) :
    formatDecode r = some d :=
  nearestDecode_correct format_min_dist (by norm_num) (List.mem_range.2 hd32) hr

/-! ## 6. QR version information -/

/-- ISO/IEC 18004 Annex D: version-information (18,6) Golay-derived generator `x¹²+x¹¹+x¹⁰+x⁹+x⁸+x⁵+x²+1` = `0x1F25`. -/
def versionGen : ℕ := 0x1F25

/-- ISO/IEC 18004 Annex D: 18-bit version information for version `v` (6 bits), systematic BCH encoding, no mask. -/
def versionEncode (v : ℕ) : ℕ := (v <<< 12) ||| polyMod versionGen 12 6 (v <<< 12)

/-- ZXing `Version.VERSION_DECODE_INFO` (versions 7–40). -/
def zxingVersionTable : List ℕ :=
  [0x07C94, 0x085BC, 0x09A99, 0x0A4D3, 0x0BBF6, 0x0C762, 0x0D847, 0x0E60D, 0x0F928, 0x10B78,
   0x1145D, 0x12A17, 0x13532, 0x149A6, 0x15683, 0x168C9, 0x177EC, 0x18EC4, 0x191E1, 0x1AFAB,
   0x1B08E, 0x1CC1A, 0x1D33F, 0x1ED75, 0x1F250, 0x209D5, 0x216F0, 0x228BA, 0x2379F, 0x24B0B,
   0x2542E, 0x26A64, 0x27541, 0x28C69]

/-- ISO/IEC 18004: the computed version codewords for versions 7–40 coincide with ZXing's table. -/
theorem versionEncode_eq_table : (List.range' 7 34).map versionEncode = zxingVersionTable := by
  decide

/-- ISO/IEC 18004: the 34 used version-information codewords (versions 7–40) have pairwise Hamming distance ≥ 8. -/
theorem version_min_dist : ∀ a ∈ List.range' 7 34, ∀ b ∈ List.range' 7 34, a ≠ b →
    8 ≤ hd 18 (versionEncode a) (versionEncode b) := by
  decide

/-- ISO/IEC 18004: the minimum distance 8 among used version codewords is attained. -/
theorem version_min_dist_attained :
    ∃ a ∈ List.range' 7 34, ∃ b ∈ List.range' 7 34, hd 18 (versionEncode a) (versionEncode b) = 8 :=
  ⟨7, by decide, 8, by decide, by decide⟩

/-- ISO/IEC 18004: even the full (18,6) code (all 64 six-bit messages) has minimum distance 8. -/
theorem version_full_code_min_dist : ∀ a < 64, ∀ b < 64, a ≠ b →
    8 ≤ hd 18 (versionEncode a) (versionEncode b) := by
  decide +kernel

/-- QR version-information decoder over versions 7–40, accepting within 3 bit errors. -/
def versionDecode (r : ℕ) : Option ℕ := nearestDecode 18 3 versionEncode (List.range' 7 34) r

/-- ISO/IEC 18004: the version decoder corrects up to 3 bit errors for every version 7–40. -/
theorem versionDecode_correct {v r : ℕ} (hv1 : 7 ≤ v) (hv2 : v ≤ 40)
    (hr : hd 18 r (versionEncode v) ≤ 3) : versionDecode r = some v :=
  nearestDecode_correct version_min_dist (by norm_num)
    (List.mem_range'_1.2 ⟨hv1, by omega⟩) hr

/-- Our bit-level `hd` agrees with Mathlib's `hammingDist` on `Fin k → Bool`. -/
theorem hd_eq_hammingDist (k x y : ℕ) :
    hd k x y = hammingDist (fun i : Fin k => x.testBit i) (fun i : Fin k => y.testBit i) := by
  induction k with
  | zero => simp [hd, hammingDist]
  | succ k ih =>
    rw [hd, ih]
    simp only [hammingDist, Finset.card_filter]
    rw [Fin.sum_univ_castSucc]
    simp [Fin.val_last, Fin.val_castSucc]

/-- ISO/IEC 18004: minimum distance 7, stated with Mathlib's `hammingDist`. -/
theorem format_min_hammingDist : ∀ a ∈ List.range 32, ∀ b ∈ List.range 32, a ≠ b →
    7 ≤ hammingDist (fun i : Fin 15 => (formatEncode a).testBit i)
      (fun i : Fin 15 => (formatEncode b).testBit i) := by
  intro a ha b hb hab
  rw [← hd_eq_hammingDist]
  exact format_min_dist a ha b hb hab

/-- Executable check: three bit flips on the codeword for data 0b10110 are corrected. -/
example : formatDecode (formatEncode 22 ^^^ 0b100000100000001) = some 22 := by
  decide +kernel

/-- Executable check: version 40 with three bit flips is recovered. -/
example : versionDecode (versionEncode 40 ^^^ 0b100000000100000001) = some 40 := by
  decide +kernel

/-! ## 7. GF(256) for QR and Data Matrix -/

section GF256

open Polynomial

/-- Bit vector `n` as the polynomial `∑ bitᵢ(n) Xⁱ` over `ZMod 2`. -/
noncomputable def toPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

/-- Coefficients of `toPoly n` are the bits of `n`. -/
theorem coeff_toPoly (n j : ℕ) : (toPoly n).coeff j = if n.testBit j then 1 else 0 := by
  unfold toPoly
  rw [finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff j), coeff_X_pow, coeff_zero]
  rw [Finset.sum_eq_single j]
  · by_cases h : n.testBit j <;> simp [h]
  · intro b _ hb; simp [Ne.symm hb]
  · intro hj
    have : n.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      have := Nat.lt_two_pow_self (n := n)
      simp at hj
      calc n < 2 ^ n := this
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    simp [this]

/-- `toPoly` is injective. -/
theorem toPoly_injective : Function.Injective toPoly := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_toPoly] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

/-- `toPoly 0 = 0`. -/
theorem toPoly_zero : toPoly 0 = 0 := by simp [toPoly]

/-- `toPoly 1 = 1`. -/
theorem toPoly_one : toPoly 1 = 1 := by
  ext j; rw [coeff_toPoly, coeff_one]
  rcases j with _ | j
  · simp
  · simp [Nat.testBit_succ]

/-- XOR of bit vectors is addition in `(ZMod 2)[X]`. -/
theorem toPoly_xor (a b : ℕ) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext j
  simp only [coeff_add, coeff_toPoly, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

/-- Left shift by `k` is multiplication by `X^k`. -/
theorem toPoly_shiftLeft (a k : ℕ) : toPoly (a <<< k) = X ^ k * toPoly a := by
  ext j
  rw [coeff_X_pow_mul', coeff_toPoly, coeff_toPoly, Nat.testBit_shiftLeft]
  by_cases h : k ≤ j <;> simp [h]

/-- `toPoly (2m + b) = b + X·toPoly m`. -/
theorem toPoly_bit (m : ℕ) (b : Bool) :
    toPoly (2 * m + b.toNat) = C (if b then 1 else 0) + X * toPoly m := by
  ext j
  rcases j with _ | j
  · rw [coeff_toPoly, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, Nat.testBit_zero]
    cases b <;> simp
  · rw [coeff_toPoly, coeff_add, coeff_C_succ, coeff_X_mul, zero_add, coeff_toPoly,
      Nat.testBit_succ]
    have : (2 * m + b.toNat) / 2 = m := by cases b <;> (simp; try omega)
    rw [this]

/-- Bits above `k` vanish for `n < 2^k`. -/
theorem toPoly_coeff_eq_zero {n k : ℕ} (hn : n < 2 ^ k) {j : ℕ} (hj : k ≤ j) :
    (toPoly n).coeff j = 0 := by
  rw [coeff_toPoly, Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hj))]
  simp

/-- `n < 2^(k+1)` gives `natDegree (toPoly n) ≤ k`. -/
theorem toPoly_natDegree_lt {n k : ℕ} (hn : n < 2 ^ (k + 1)) : (toPoly n).natDegree ≤ k :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hN => toPoly_coeff_eq_zero hn hN

/-- Every polynomial over `ZMod 2` with no coefficients at or above `k` is `toPoly n` for some `n < 2^k`. -/
theorem exists_toPoly : ∀ (k : ℕ) (p : (ZMod 2)[X]), (∀ j, k ≤ j → p.coeff j = 0) →
    ∃ n < 2 ^ k, toPoly n = p
  | 0, p, hp => ⟨0, by norm_num, by
      rw [toPoly_zero]; ext j; simp [hp j (Nat.zero_le _)]⟩
  | k + 1, p, hp => by
    obtain ⟨m, hm, hmp⟩ := exists_toPoly k p.divX (fun j hj => by
      rw [coeff_divX]; exact hp _ (by omega))
    refine ⟨2 * m + (decide (p.coeff 0 = 1)).toNat, ?_, ?_⟩
    · rw [pow_succ]; cases decide (p.coeff 0 = 1) <;> simp <;> omega
    · rw [toPoly_bit, hmp]
      conv_rhs => rw [← X_mul_divX_add p]
      rw [add_comm]
      congr 2
      generalize p.coeff 0 = c
      fin_cases c <;> rfl

/-! carry-less multiplication -/

/-- Carry-less (GF(2)[x]) multiplication of bit vectors, `k` bits of the first factor. -/
def clmul : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => (if a % 2 = 1 then b else 0) ^^^ (clmul k (a / 2) b <<< 1)

/-- Carry-less multiplication is polynomial multiplication over `ZMod 2`. -/
theorem toPoly_clmul : ∀ (k a b : ℕ), a < 2 ^ k → toPoly (clmul k a b) = toPoly a * toPoly b
  | 0, a, b, ha => by
    have : a = 0 := by simpa using ha
    subst this; simp [clmul, toPoly_zero]
  | k + 1, a, b, ha => by
    have ih := toPoly_clmul k (a / 2) b (by rw [pow_succ] at ha; omega)
    have ha' : a = 2 * (a / 2) + (decide (a % 2 = 1)).toNat := by
      by_cases h : a % 2 = 1 <;> simp [h] <;> omega
    rw [clmul, toPoly_xor, toPoly_shiftLeft, ih]
    conv_rhs => rw [ha', toPoly_bit]
    by_cases h : a % 2 = 1 <;> simp [h, toPoly_zero] <;> ring

/-- Multiply by `α = x` (i.e. by 2) in GF(256) = GF(2)[x]/(P): shift left, reduce by `P` if bit 7 was set. This is the `xtime` used by QR / Data Matrix Reed–Solomon implementations. -/
def mulX (P a : ℕ) : ℕ := if a.testBit 7 then (a <<< 1) ^^^ P else a <<< 1

/-- `powX P k` = bit representation of `α^k` under the bitwise reduction by `P`. -/
def powX (P : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => mulX P (powX P k)

/-- Connection: the bit vector `powX P k` represents `root^k` in `AdjoinRoot (toPoly P)`. -/
theorem mk_toPoly_powX (P k : ℕ) :
    AdjoinRoot.mk (toPoly P) (toPoly (powX P k)) = AdjoinRoot.root (toPoly P) ^ k := by
  induction k with
  | zero => simp [powX, toPoly_one]
  | succ k ih =>
    rw [pow_succ, ← ih, powX, mulX]
    have hX : AdjoinRoot.mk (toPoly P) X = AdjoinRoot.root (toPoly P) := AdjoinRoot.mk_X
    split_ifs
    · rw [toPoly_xor, toPoly_shiftLeft, map_add, AdjoinRoot.mk_self, add_zero, map_mul,
        pow_one, hX, mul_comm]
    · rw [toPoly_shiftLeft, map_mul, pow_one, hX, mul_comm]

/-! generic degree-8 theorems -/

section Deg8
variable {P : ℕ} (h8 : P.testBit 8 = true) (hP : P < 512)
include h8 hP

/-- A 9-bit pattern with bit 8 set is a degree-8 polynomial. -/
theorem toPoly_natDegree_eight : (toPoly P).natDegree = 8 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (toPoly_natDegree_lt (k := 8) (by omega))
  rw [coeff_toPoly]
  simp [h8]

/-- A 9-bit pattern with bit 8 set is a monic polynomial. -/
theorem toPoly_monic : (toPoly P).Monic := by
  rw [Monic, leadingCoeff, toPoly_natDegree_eight h8 hP, coeff_toPoly]
  simp [h8]

/-- Connection: a degree-8 polynomial is irreducible over `ZMod 2` if no product of a degree ≤ 7 and a degree 1–4 bit vector equals it. -/
theorem irreducible_of_clmul (hfac : ∀ a < 256, ∀ b < 32, 2 ≤ b → clmul 8 a b ≠ P) :
    Irreducible (toPoly P) := by
  have hdeg8 := toPoly_natDegree_eight h8 hP
  rw [(toPoly_monic h8 hP).irreducible_iff_natDegree']
  refine ⟨fun h => by rw [h] at hdeg8; simp at hdeg8, ?_⟩
  intro f g hf hg hfg hdeg
  rw [hdeg8] at hdeg
  simp only [Finset.mem_Ioc] at hdeg
  have hsum := hf.natDegree_mul hg
  rw [hfg, hdeg8] at hsum
  obtain ⟨a, ha, rfl⟩ := exists_toPoly 8 f
    (fun j hj => coeff_eq_zero_of_natDegree_lt (by omega))
  obtain ⟨b, hb, rfl⟩ := exists_toPoly 5 g
    (fun j hj => coeff_eq_zero_of_natDegree_lt (by omega))
  have hb2 : 2 ≤ b := by
    by_contra hcon
    interval_cases b
    · simp [toPoly_zero] at hdeg
    · simp [toPoly_one] at hdeg
  exact hfac a (by simpa using ha) b (by simpa using hb) hb2
    (toPoly_injective (by rw [toPoly_clmul 8 a b ha, hfg]))

/-- Connection: if the bitwise powers of 2 return to 1 exactly at 255, then `X` has multiplicative order 255 in `AdjoinRoot P`. -/
theorem orderOf_root_eq (h255 : powX P 255 = 1) (hlt : ∀ m < 255, 0 < m → powX P m ≠ 1)
    (hbound : ∀ m < 255, powX P m < 256) :
    orderOf (AdjoinRoot.root (toPoly P)) = 255 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [← mk_toPoly_powX, h255, toPoly_one, map_one]
  · intro m hm hm0 h
    rw [← mk_toPoly_powX, ← map_one (AdjoinRoot.mk (toPoly P)), ← toPoly_one,
      AdjoinRoot.mk_eq_mk, CharTwo.sub_eq_add, ← toPoly_xor] at h
    have hz := eq_zero_of_dvd_of_natDegree_lt h (by
      rw [toPoly_natDegree_eight h8 hP]
      have := toPoly_natDegree_lt (k := 7)
        (Nat.xor_lt_two_pow (by simpa using hbound m hm) (by norm_num : 1 < 2 ^ 8))
      omega)
    rw [← toPoly_zero] at hz
    have := toPoly_injective hz
    exact hlt m hm hm0 (Nat.eq_of_xor_eq_zero this)

end Deg8

/-! ### Concrete fields: QR (0x11D) and Data Matrix (0x12D) -/

/-- `0x11D` is `x⁸+x⁴+x³+x²+1` (QR code GF(256), ISO/IEC 18004 §7.5.2). -/
theorem toPoly_0x11D : toPoly 0x11D = X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1 := by
  ext j
  rw [coeff_toPoly]
  simp only [coeff_add, coeff_X_pow, coeff_one]
  by_cases hj : j < 9
  · interval_cases j <;> decide
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 0x11D < 2 ^ 9)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [show j ≠ 8 by omega, show j ≠ 4 by omega, show j ≠ 3 by omega,
      show j ≠ 2 by omega, show j ≠ 0 by omega]

/-- `0x12D` is `x⁸+x⁵+x³+x²+1` (Data Matrix GF(256), ISO/IEC 16022 §5.7.1). -/
theorem toPoly_0x12D : toPoly 0x12D = X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1 := by
  ext j
  rw [coeff_toPoly]
  simp only [coeff_add, coeff_X_pow, coeff_one]
  by_cases hj : j < 9
  · interval_cases j <;> decide
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 0x12D < 2 ^ 9)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [show j ≠ 8 by omega, show j ≠ 5 by omega, show j ≠ 3 by omega,
      show j ≠ 2 by omega, show j ≠ 0 by omega]

/-- ISO/IEC 18004: bit-level factor search for `0x11D` (no degree 1–4 factor). -/
theorem qr_noFactor : ∀ a < 256, ∀ b < 32, 2 ≤ b → clmul 8 a b ≠ 0x11D := by
  decide +kernel
/-- ISO/IEC 16022: bit-level factor search for `0x12D` (no degree 1–4 factor). -/
theorem dm_noFactor : ∀ a < 256, ∀ b < 32, 2 ≤ b → clmul 8 a b ≠ 0x12D := by decide +kernel

/-- ISO/IEC 18004: `2^255 = 1` under reduction by `0x11D`. -/
theorem qr_powX_255 : powX 0x11D 255 = 1 := by decide +kernel
/-- ISO/IEC 18004: `2^m ≠ 1` for `0 < m < 255` under reduction by `0x11D`. -/
theorem qr_powX_ne : ∀ m < 255, 0 < m → powX 0x11D m ≠ 1 := by decide +kernel
/-- ISO/IEC 18004: the bitwise powers of 2 stay below 256 under reduction by `0x11D`. -/
theorem qr_powX_lt : ∀ m < 255, powX 0x11D m < 256 := by decide +kernel
/-- ISO/IEC 16022: `2^255 = 1` under reduction by `0x12D`. -/
theorem dm_powX_255 : powX 0x12D 255 = 1 := by decide +kernel
/-- ISO/IEC 16022: `2^m ≠ 1` for `0 < m < 255` under reduction by `0x12D`. -/
theorem dm_powX_ne : ∀ m < 255, 0 < m → powX 0x12D m ≠ 1 := by decide +kernel
/-- ISO/IEC 16022: the bitwise powers of 2 stay below 256 under reduction by `0x12D`. -/
theorem dm_powX_lt : ∀ m < 255, powX 0x12D m < 256 := by decide +kernel

/-- ISO/IEC 18004 (QR code): `x⁸+x⁴+x³+x²+1` is irreducible over `ZMod 2`, so `GF(2)[x]/(0x11D)` is GF(256). -/
theorem qr_irreducible : Irreducible (X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  rw [← toPoly_0x11D]; exact irreducible_of_clmul (by decide) (by norm_num) qr_noFactor

/-- ISO/IEC 16022 (Data Matrix): `x⁸+x⁵+x³+x²+1` is irreducible over `ZMod 2`. -/
theorem dm_irreducible : Irreducible (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  rw [← toPoly_0x12D]; exact irreducible_of_clmul (by decide) (by norm_num) dm_noFactor

/-- ISO/IEC 18004 (QR code): `α = x` (the byte 2) has multiplicative order 255 in `GF(2)[x]/(x⁸+x⁴+x³+x²+1)`, i.e. it is primitive. -/
theorem qr_orderOf_root :
    orderOf (AdjoinRoot.root (X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X])) = 255 := by
  rw [← toPoly_0x11D]
  exact orderOf_root_eq (by decide) (by norm_num) qr_powX_255 qr_powX_ne qr_powX_lt

/-- ISO/IEC 16022 (Data Matrix): `α = x` (the byte 2) has multiplicative order 255 in `GF(2)[x]/(x⁸+x⁵+x³+x²+1)`, i.e. it is primitive. -/
theorem dm_orderOf_root :
    orderOf (AdjoinRoot.root (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X])) = 255 := by
  rw [← toPoly_0x12D]
  exact orderOf_root_eq (by decide) (by norm_num) dm_powX_255 dm_powX_ne dm_powX_lt

/-- ISO/IEC 18004: `α = x` is a primitive 255th root of unity in the QR field. -/
theorem qr_isPrimitiveRoot :
    IsPrimitiveRoot (AdjoinRoot.root (X ^ 8 + X ^ 4 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X])) 255 :=
  IsPrimitiveRoot.iff_orderOf.2 qr_orderOf_root

/-- ISO/IEC 16022: `α = x` is a primitive 255th root of unity in the Data Matrix field. -/
theorem dm_isPrimitiveRoot :
    IsPrimitiveRoot (AdjoinRoot.root (X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X])) 255 :=
  IsPrimitiveRoot.iff_orderOf.2 dm_orderOf_root

end GF256

end RoboLean.Barcode.CheckDigits
