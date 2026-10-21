import RoboLean.Barcode.Decoder

/-!
# Generalized Reed–Solomon duality and completeness of the QR decoder

* `colW α j = ∏_{i ≠ j} (α j - α i)`; the column multipliers are `v j = 1 / colW α j`.
* `sum_eval_div_colW` — for distinct points and `deg p < n`,
  `∑ⱼ p(αⱼ) / colW α j = coeff p (n-1)` (Lagrange / partial fractions; via Mathlib's
  `Lagrange.coeff_eq_sum`). `sum_pow_div_colW`: `∑ⱼ αⱼ^m / colW α j = [m = n-1]` for `m < n`.
* `grs_dual_iff` — **GRS duality for arbitrary distinct points**: `c` is orthogonal to every
  evaluation codeword `(g(αⱼ))ⱼ`, `deg g < n - k`, iff `c = (f(αⱼ) / colW α j)ⱼ` for some
  `deg f < k` (`k ≤ n`). `grs_dual_iff'` is the same with the roles of `k`, `n-k` swapped.
  `grsCode_eq_dual` packages it as `grsCode α k = {c | c ⊥ evalCode α (n-k)}`.
* `syndrome_eq_zero_iff_grs` — shortened BCH view: for `β` whose powers `β⁰,…,β^(n-1)` are
  distinct (no primitivity / full-length assumption), all syndromes `c(β^(b+l))`, `l < n-k`,
  vanish iff `c j = f(β^j) / (β^(bj) · colW j)` with `deg f < k`.
* `qrDecodeWord_complete` — for every QR codeword `c` (`n ≤ 255`, `k ≤ n`, syndromes zero, base
  `b = 0`) and every received word `r` with at most `⌊(n-k)/2⌋` symbol errors,
  `qrDecodeWord n k r = some c`. Together with `qrDecodeWord_sound` this is full correctness.
-/

namespace RoboLean.Barcode.Duality

open Polynomial Finset RoboLean.Barcode.ReedSolomon RoboLean.Barcode.Decoder

section General

variable {F : Type*} [Field F] {n : ℕ}

/-- The column weight `∏_{i ≠ j} (α j - α i)`; the GRS column multiplier is its inverse. -/
def colW (α : Fin n → F) (j : Fin n) : F := ∏ i ∈ univ.erase j, (α j - α i)

lemma colW_ne_zero {α : Fin n → F} (hα : Function.Injective α) (j : Fin n) : colW α j ≠ 0 := by
  refine prod_ne_zero_iff.2 (fun i hi => sub_ne_zero.2 (fun h => ?_))
  exact (mem_erase.1 hi).1 (hα h).symm

/-- **Lagrange / partial-fraction identity.** For distinct points and `deg p < n`,
`∑ⱼ p(αⱼ) / ∏_{i≠j}(αⱼ - αᵢ)` is the coefficient of `X^(n-1)` in `p`. -/
theorem sum_eval_div_colW {α : Fin n → F} (hα : Function.Injective α) {p : F[X]}
    (hp : p.degree < n) : ∑ j, p.eval (α j) / colW α j = p.coeff (n - 1) := by
  have := Lagrange.coeff_eq_sum (s := univ) (v := α) hα.injOn (P := p)
    (by rwa [card_univ, Fintype.card_fin])
  rw [card_univ, Fintype.card_fin] at this
  rw [this]; rfl

/-- `∑ⱼ αⱼ^m / ∏_{i≠j}(αⱼ - αᵢ) = 0` for `m ≤ n - 2` and `= 1` for `m = n - 1`. -/
theorem sum_pow_div_colW {α : Fin n → F} (hα : Function.Injective α) {m : ℕ} (hm : m < n) :
    ∑ j, α j ^ m / colW α j = if m = n - 1 then 1 else 0 := by
  have := sum_eval_div_colW hα (p := X ^ m) (by rw [degree_X_pow]; exact_mod_cast hm)
  simp only [eval_X_pow] at this
  rw [this, coeff_X_pow]
  by_cases h : m = n - 1
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The evaluation code `{(g(αⱼ))ⱼ : deg g < d}`. -/
noncomputable def evalCode (α : Fin n → F) (d : ℕ) : Submodule F (Fin n → F) :=
  Submodule.map (encodeLinear α d) ⊤

/-- The generalized RS code `{(f(αⱼ) / colW α j)ⱼ : deg f < d}`. -/
noncomputable def grsCode (α : Fin n → F) (d : ℕ) : Submodule F (Fin n → F) :=
  Submodule.map ((LinearMap.pi fun j => (colW α j)⁻¹ • LinearMap.proj j).comp
    (encodeLinear α d)) ⊤

lemma mem_evalCode {α : Fin n → F} {d : ℕ} {c : Fin n → F} :
    c ∈ evalCode α d ↔ ∃ g ∈ degreeLT F d, ∀ j, c j = g.eval (α j) := by
  constructor
  · rintro ⟨g, -, rfl⟩
    exact ⟨g, g.2, fun j => rfl⟩
  · rintro ⟨g, hg, hc⟩
    exact ⟨⟨g, hg⟩, trivial, funext fun j => (hc j).symm⟩

lemma mem_grsCode {α : Fin n → F} {d : ℕ} {c : Fin n → F} :
    c ∈ grsCode α d ↔ ∃ f ∈ degreeLT F d, ∀ j, c j = f.eval (α j) / colW α j := by
  constructor
  · rintro ⟨f, -, rfl⟩
    refine ⟨f, f.2, fun j => ?_⟩
    simp [encodeLinear, encode, div_eq_inv_mul]
  · rintro ⟨f, hf, hc⟩
    refine ⟨⟨f, hf⟩, trivial, funext fun j => ?_⟩
    simp [encodeLinear, encode, hc j, div_eq_inv_mul]

/-- Orthogonality: a GRS word of degree `< k` and an evaluation word of degree `< n - k`. -/
theorem grs_orth {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} {f g : F[X]}
    (hf : f ∈ degreeLT F k) (hg : g ∈ degreeLT F (n - k)) :
    ∑ j, f.eval (α j) / colW α j * g.eval (α j) = 0 := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  rw [mem_degreeLT, degree_eq_natDegree hf0] at hf
  rw [mem_degreeLT, degree_eq_natDegree hg0] at hg
  have hf' : f.natDegree < k := by exact_mod_cast hf
  have hg' : g.natDegree < n - k := by exact_mod_cast hg
  have hfg : (f * g).natDegree < n - 1 := by
    rw [natDegree_mul hf0 hg0]; omega
  have hdeg : (f * g).degree < n := by
    rw [degree_eq_natDegree (mul_ne_zero hf0 hg0)]; exact_mod_cast (by omega : _ < n)
  have := sum_eval_div_colW hα hdeg
  rw [coeff_eq_zero_of_natDegree_lt hfg] at this
  rw [← this]
  refine sum_congr rfl (fun j _ => ?_)
  rw [eval_mul]; ring

/-- **Generalized RS duality** (arbitrary distinct points). For `k ≤ n`, a word `c` is
orthogonal (standard dot product) to the evaluation code of dimension `n - k` iff it is a GRS
codeword `(f(αⱼ) / ∏_{i≠j}(αⱼ-αᵢ))ⱼ` with `deg f < k`. -/
theorem grs_dual_iff {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk : k ≤ n)
    (c : Fin n → F) :
    (∀ g ∈ degreeLT F (n - k), ∑ j, c j * g.eval (α j) = 0) ↔
      ∃ f ∈ degreeLT F k, ∀ j, c j = f.eval (α j) / colW α j := by
  constructor
  · intro h
    classical
    set f := Lagrange.interpolate univ α (fun j => c j * colW α j) with hfdef
    have hfe : ∀ j, f.eval (α j) = c j * colW α j := fun j =>
      Lagrange.eval_interpolate_at_node _ hα.injOn (mem_univ j)
    have hcf : ∀ j, c j = f.eval (α j) / colW α j := fun j => by
      rw [hfe, mul_div_cancel_right₀ _ (colW_ne_zero hα j)]
    refine ⟨f, ?_, hcf⟩
    have hfn : f.degree < n := by
      have := Lagrange.degree_interpolate_lt (s := univ) (fun j => c j * colW α j) hα.injOn
      rwa [card_univ, Fintype.card_fin] at this
    rw [mem_degreeLT]
    by_contra hfk
    push Not at hfk
    have hf0 : f ≠ 0 := by rintro h0; rw [h0, degree_zero] at hfk; exact absurd hfk (by simp)
    rw [degree_eq_natDegree hf0] at hfk hfn
    have hd1 : k ≤ f.natDegree := by exact_mod_cast hfk
    have hd2 : f.natDegree < n := by exact_mod_cast hfn
    set d := f.natDegree
    have hg : (X ^ (n - 1 - d) : F[X]) ∈ degreeLT F (n - k) := by
      rw [mem_degreeLT, degree_X_pow]; exact_mod_cast (by omega : n - 1 - d < n - k)
    have h1 := h _ hg
    have hdeg : (f * X ^ (n - 1 - d)).degree < ((n : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_X_pow, degree_eq_natDegree hf0]
      exact_mod_cast (by omega : d + (n - 1 - d) < n)
    have h2 := sum_eval_div_colW hα hdeg
    have hcoeff : (f * X ^ (n - 1 - d)).coeff (n - 1) = f.leadingCoeff := by
      have := coeff_mul_X_pow f (n - 1 - d) d
      rw [show d + (n - 1 - d) = n - 1 by omega] at this
      rw [this]; rfl
    rw [hcoeff] at h2
    apply leadingCoeff_ne_zero.2 hf0
    rw [← h2, ← h1]
    refine sum_congr rfl (fun j _ => ?_)
    rw [hcf j, eval_mul]; ring
  · rintro ⟨f, hf, hc⟩ g hg
    rw [← grs_orth hα hf hg]
    exact sum_congr rfl (fun j _ => by rw [hc j])

/-- Duality with the roles swapped: `c ⊥` the evaluation code of dimension `k` iff `c` is a
GRS word of dimension `n - k` (the form `{(vⱼ f(αⱼ)) : deg f < n-k} = (RS_k)^⊥`). -/
theorem grs_dual_iff' {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk : k ≤ n)
    (c : Fin n → F) :
    (∀ g ∈ degreeLT F k, ∑ j, c j * g.eval (α j) = 0) ↔
      ∃ f ∈ degreeLT F (n - k), ∀ j, c j = f.eval (α j) / colW α j := by
  have := grs_dual_iff hα (k := n - k) (by omega) c
  rwa [Nat.sub_sub_self hk] at this

/-- Submodule form: `GRS_k(α, v) = (RS_{n-k}(α))^⊥` for the standard dot product. -/
theorem grsCode_eq_dual {α : Fin n → F} (hα : Function.Injective α) {k : ℕ} (hk : k ≤ n) :
    (grsCode α k : Set (Fin n → F)) =
      {c | ∀ x ∈ evalCode α (n - k), ∑ j, c j * x j = 0} := by
  ext c
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_grsCode]
  rw [← grs_dual_iff hα hk]
  constructor
  · intro h x hx
    obtain ⟨g, hg, hx⟩ := mem_evalCode.1 hx
    simp_rw [hx]; exact h g hg
  · intro h g hg
    exact h _ (mem_evalCode.2 ⟨g, hg, fun j => rfl⟩)

/-- **Shortened BCH / RS syndromes.** If the powers `β^0, …, β^(n-1)` are distinct (no
full-length / primitivity hypothesis), all syndromes `c(β^(b+l))`, `l < n - k`, vanish iff
`c j · β^(bj) · colW j = f(β^j)` for some `deg f < k`. -/
theorem syndrome_eq_zero_iff_grs {β : F} {b k : ℕ} (hk : k ≤ n)
    (hβ : Function.Injective (fun j : Fin n => β ^ (j : ℕ))) (c : Fin n → F) :
    syndrome β b k c = 0 ↔ ∃ f ∈ degreeLT F k,
      ∀ j, c j * β ^ (b * (j : ℕ)) = f.eval (β ^ (j : ℕ)) / colW (fun j : Fin n => β ^ (j : ℕ)) j := by
  rw [← grs_dual_iff hβ hk]
  have key : ∀ l : ℕ, ∑ j : Fin n, c j * (β ^ (b + l)) ^ (j : ℕ) =
      ∑ j : Fin n, c j * β ^ (b * (j : ℕ)) * (β ^ (j : ℕ)) ^ l := fun l =>
    sum_congr rfl (fun j _ => by
      rw [← pow_mul, ← pow_mul, mul_assoc, ← pow_add]; congr 2; ring)
  constructor
  · intro h g hg
    rw [mem_degreeLT] at hg
    have hgs : g = ∑ l ∈ range (n - k), C (g.coeff l) * X ^ l := by
      by_cases hg0 : g = 0
      · simp [hg0]
      exact as_sum_range_C_mul_X_pow' g (by
        rw [degree_eq_natDegree hg0] at hg; exact_mod_cast hg)
    rw [hgs]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_X_pow, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero (fun l hl => ?_)
    have hl' : l < n - k := mem_range.1 hl
    have := congrFun h ⟨l, hl'⟩
    simp only [syndrome, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, key] at this
    calc ∑ j : Fin n, c j * β ^ (b * (j : ℕ)) * (g.coeff l * (β ^ (j : ℕ)) ^ l)
        = g.coeff l * ∑ j : Fin n, c j * β ^ (b * (j : ℕ)) * (β ^ (j : ℕ)) ^ l := by
          rw [mul_sum]; exact sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [this, mul_zero]
  · intro h
    funext l
    simp only [syndrome, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, key]
    have := h (X ^ (l : ℕ)) (by rw [mem_degreeLT, degree_X_pow]; exact_mod_cast l.2)
    simpa using this

end General

/-! ## Completeness of the QR decoder -/

section QR

open GF256

lemma foldl_eq_mul_prod {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (j : Fin n) :
    ∀ (l : List (Fin n)) (acc : F),
      l.foldl (fun acc i => if i = j then acc else acc * (a j - a i)) acc =
        acc * (l.map (fun i => if i = j then 1 else a j - a i)).prod
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_eq_mul_prod a j l, List.map_cons, List.prod_cons]
    split_ifs <;> ring

lemma foldl_eq_colW {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (j : Fin n) :
    (List.finRange n).foldl (fun acc i => if i = j then acc else acc * (a j - a i)) 1 =
      colW a j := by
  rw [foldl_eq_mul_prod, one_mul, ← Fin.prod_univ_def, colW,
    ← mul_prod_erase univ _ (mem_univ j), if_pos rfl, one_mul]
  exact prod_congr rfl (fun i hi => if_neg (mem_erase.1 hi).1)

lemma evalList_eq {F : Type*} [Field F] (β : F) : ∀ l : List F, evalList l β = (lpoly l).eval β
  | [] => by simp [evalList]
  | a :: l => by
    rw [lpoly_cons, eval_add, eval_mul, eval_C, eval_X, ← evalList_eq β l]
    simp [evalList]

lemma msgPoly_coeff_eq {F : Type*} [Field F] {k : ℕ} {f : F[X]} (hf : f ∈ degreeLT F k) :
    msgPoly (fun i : Fin k => f.coeff i) = f := by
  ext j
  by_cases hj : j < k
  · exact coeff_msgPoly (fun i : Fin k => f.coeff i) ⟨j, hj⟩
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (mem_degreeLT.1 (msgPoly_mem _))
      (by exact_mod_cast (by omega : k ≤ j))),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (mem_degreeLT.1 hf)
      (by exact_mod_cast (by omega : k ≤ j)))]

lemma hammingDist_mul_right {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {w : Fin n → F} (hw : ∀ j, w j ≠ 0)
    (x y : Fin n → F) :
    hammingDist (fun j => x j * w j) (fun j => y j * w j) = hammingDist x y := by
  unfold hammingDist
  congr 1
  ext j
  simp [hw j]

lemma qrα_eq_fun {n : ℕ} (hn : n ≤ 255) : qrα n = fun j : Fin n => byte 2 ^ (j : ℕ) :=
  funext fun j => qrα_eq j (by omega)

/-- **Completeness of `qrDecodeWord`.** For any QR codeword `c` (block length `n ≤ 255`,
`k ≤ n` data symbols, all `n - k` syndromes `c(αˡ)` zero, generator base `b = 0`) and any
received word `r` with at most `⌊(n-k)/2⌋` symbol errors, `qrDecodeWord` returns exactly `c`. -/
theorem qrDecodeWord_complete {n k : ℕ} (hn : n ≤ 255) (hk : k ≤ n) {c r : Fin n → GF256}
    (hc : syndrome (byte 2) 0 k c = 0) (hr : hammingDist c r ≤ (n - k) / 2) :
    qrDecodeWord n k r = some c := by
  have hinj := qrα_injective hn
  have ha := qrα_eq_fun hn
  obtain ⟨f, hf, hcf⟩ := (syndrome_eq_zero_iff_grs hk (ha ▸ hinj) c).1 hc
  simp only [zero_mul, pow_zero, mul_one] at hcf
  replace hcf : ∀ j, c j = f.eval (qrα n j) / colW (qrα n) j := fun j => by
    rw [hcf j, ← ha, qrα_eq j (by omega)]
  have hw0 := colW_ne_zero hinj
  set m : Fin k → GF256 := fun i => f.coeff i with hm
  have hmf : msgPoly m = f := msgPoly_coeff_eq hf
  have hcw : ∀ j, c j * colW (qrα n) j = f.eval (qrα n j) := fun j => by
    rw [hcf j, div_mul_cancel₀ _ (hw0 j)]
  have hdist : hammingDist (encodeVec (qrα n) m) (fun j => r j * colW (qrα n) j) ≤ (n - k) / 2 := by
    rw [← encode_msgPoly, hmf]
    have : encode (qrα n) f = fun j => c j * colW (qrα n) j := funext fun j => (hcw j).symm
    rw [this, hammingDist_mul_right hw0]; exact hr
  have hbw := bwDecode_correct hinj (by omega) m _ hdist
  unfold qrDecodeWord
  simp only [Array.getElem_ofFn, foldl_eq_colW, hbw]
  have hc' : (fun j : Fin n => evalList (List.ofFn m) (qrα n j) / colW (qrα n) j) = c := by
    funext j
    rw [evalList_eq, lpoly_ofFn, hmf, hcf j]
  simp only [hc']
  rw [if_pos ⟨hc, hr⟩]

end QR

end RoboLean.Barcode.Duality
