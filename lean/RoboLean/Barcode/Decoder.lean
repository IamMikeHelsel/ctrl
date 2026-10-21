import RoboLean.Barcode.ReedSolomon
import RoboLean.Barcode.CheckDigits

/-!
# A runnable, verified Reed–Solomon decoder (Berlekamp–Welch)

* `kernel` — Gaussian elimination returning a nonzero kernel vector of a homogeneous system
  (rows as lists, any field with decidable equality). `kernel_sound`: a returned vector is
  nonzero and solves the system; `kernel_complete`: if a nonzero solution exists, `kernel`
  returns `some`.
* `psdiv`, `divStrip` — exact polynomial division on coefficient lists; `divStrip_eq`.
* `bwDecode α r e k` — builds the key-equation system, solves it with `kernel`, divides.
  `bwDecode_correct`: if `r` is within Hamming distance `e` of the codeword of `m`, the points
  are distinct and `2e + k ≤ n`, then `bwDecode α r e k = some (List.ofFn m)`.
  (Uses `bw_exists` / `bw_correct` from `ReedSolomon.lean`.)
* `GF256` — computable QR field GF(2)[x]/(0x11D) (byte XOR, 64 KiB multiplication table built
  from the shift-and-add `gmul`, inverse `a^254`) with a proven `Field` instance, obtained by
  transferring the ring axioms along the injective homomorphism into
  `AdjoinRoot (toPoly 0x11D)`; inverses checked by kernel `decide` over all bytes.
* `qrα`, `qrα_injective` (all `n ≤ 255`), `qr_v1L_decode`, `qr_decode`.
* `qrDecodeWord` / `qrDecodeBlock` — decoding real QR (generator-polynomial view) blocks via
  column multipliers, with checked soundness `qrDecodeWord_sound`.
* `#eval`/`#guard_msgs` runs: a 26/19 block with 3 errors, and the standard "HELLO WORLD"
  1-M QR block with 5 corrupted bytes. Benchmarks: `tools/bench_decoder/`.
-/

namespace RoboLean.Barcode.Decoder

open Polynomial Finset RoboLean.Barcode.ReedSolomon RoboLean.Barcode.CheckDigits

section ListPoly

variable {F : Type*} [Field F]

/-- Dot product of two lists (truncating). -/
def dot : List F → List F → F
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

@[simp] lemma dot_nil_left (l : List F) : dot [] l = 0 := rfl
@[simp] lemma dot_nil_right (l : List F) : dot l [] = 0 := by cases l <;> rfl
@[simp] lemma dot_cons (a b : F) (as bs : List F) : dot (a :: as) (b :: bs) = a * b + dot as bs := rfl

lemma dot_zipWith (k : F) : ∀ (u v y : List F), u.length = v.length →
    dot (List.zipWith (fun a b => a - k * b) u v) y = dot u y - k * dot v y
  | [], [], y, _ => by simp
  | a :: u, b :: v, [], _ => by simp
  | a :: u, b :: v, c :: y, h => by
    simp only [List.zipWith_cons_cons, dot_cons]
    rw [dot_zipWith k u v y (by simpa using h)]; ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

lemma dot_map_mul (k : F) : ∀ (u y : List F), dot (u.map (k * ·)) y = k * dot u y
  | [], y => by simp
  | a :: u, [] => by simp
  | a :: u, c :: y => by simp only [List.map_cons, dot_cons, dot_map_mul k u y]; ring

lemma dot_append : ∀ (a1 a2 b1 b2 : List F), a1.length = b1.length →
    dot (a1 ++ a2) (b1 ++ b2) = dot a1 b1 + dot a2 b2
  | [], a2, [], b2, _ => by simp
  | x :: a1, a2, y :: b1, b2, h => by
    simp only [List.cons_append, dot_cons, dot_append a1 a2 b1 b2 (by simpa using h)]; ring
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

lemma dot_eq_zero_of_all_zero : ∀ (u y : List F), (∀ a ∈ y, a = 0) → dot u y = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: u, c :: y, h => by
    simp only [dot_cons, h c (by simp), mul_zero, zero_add]
    exact dot_eq_zero_of_all_zero u y (fun x hx => h x (by simp [hx]))

/-- A list of coefficients `[a₀, a₁, …]` read as the polynomial `a₀ + a₁ X + ⋯`. -/
noncomputable def lpoly : List F → F[X]
  | [] => 0
  | a :: as => C a + X * lpoly as

@[simp] lemma lpoly_nil : lpoly ([] : List F) = 0 := rfl
@[simp] lemma lpoly_cons (a : F) (as : List F) : lpoly (a :: as) = C a + X * lpoly as := rfl

lemma coeff_lpoly : ∀ (l : List F) (j : ℕ), (lpoly l).coeff j = l.getD j 0
  | [], j => by simp
  | a :: l, 0 => by simp
  | a :: l, j + 1 => by simp [coeff_X_mul, coeff_lpoly l j]

lemma lpoly_eq_zero_iff (l : List F) : lpoly l = 0 ↔ ∀ a ∈ l, a = 0 := by
  constructor
  · intro h a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have := coeff_lpoly l j
    rw [h, coeff_zero, List.getD_eq_getElem _ _ hj] at this
    exact this.symm
  · intro h; ext j
    rw [coeff_lpoly, coeff_zero]
    by_cases hj : j < l.length
    · rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]

lemma degree_lpoly_lt (l : List F) : (lpoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_lpoly, List.getD_eq_default _ _ (by exact_mod_cast hj)]

/-- The first `L` coefficients of a polynomial. -/
noncomputable def coeffList (p : F[X]) (L : ℕ) : List F := (List.range L).map p.coeff

lemma lpoly_coeffList {p : F[X]} {L : ℕ} (hp : p.degree < L) : lpoly (coeffList p L) = p := by
  ext j
  rw [coeff_lpoly, coeffList]
  by_cases hj : j < L
  · rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    exact (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast (by omega : L ≤ j)))).symm

@[simp] lemma length_coeffList (p : F[X]) (L : ℕ) : (coeffList p L).length = L := by
  simp [coeffList]

/-- `[x, xβ, xβ², …, xβ^(L-1)]` (linear time). -/
def powsFrom (β : F) : F → ℕ → List F
  | _, 0 => []
  | x, L + 1 => x :: powsFrom β (x * β) L

/-- `[1, β, β², …, β^(L-1)]`. -/
def pows (β : F) (L : ℕ) : List F := powsFrom β 1 L

@[simp] lemma length_pows (β : F) (L : ℕ) : (pows β L).length = L := by
  unfold pows
  suffices ∀ x, (powsFrom β x L).length = L from this 1
  induction L with
  | zero => intro; rfl
  | succ L ih => intro x; simp [powsFrom, ih]

lemma dot_powsFrom (β : F) : ∀ (L : ℕ) (x : F) (xs : List F), xs.length = L →
    dot (powsFrom β x L) xs = x * (lpoly xs).eval β
  | 0, x, [], _ => by simp [powsFrom]
  | L + 1, x, a :: xs, h => by
    simp only [powsFrom, dot_cons, lpoly_cons, eval_add, eval_C, eval_mul, eval_X]
    rw [dot_powsFrom β L _ xs (by simpa using h)]; ring
  | 0, _, _ :: _, h => by simp at h
  | _ + 1, _, [], h => by simp at h

lemma dot_pows (β : F) (L : ℕ) (x : List F) (h : x.length = L) :
    dot (pows β L) x = (lpoly x).eval β := by
  rw [pows, dot_powsFrom β L 1 x h, one_mul]

lemma dot_split (s x : List F) (hs : s ≠ []) (hx : x ≠ []) :
    dot s x = s.headD 0 * x.headD 0 + dot s.tail x.tail := by
  cases s with
  | nil => contradiction
  | cons a s => cases x with
    | nil => contradiction
    | cons b x => rfl

end ListPoly

/-! ## A verified homogeneous linear-system solver (kernel vector by Gaussian elimination) -/

section Kernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- `x` solves the homogeneous system with the given rows. -/
def Sol (rows : List (List F)) (x : List F) : Prop := ∀ r ∈ rows, dot r x = 0

/-- `x` has a nonzero entry. -/
def NZ (x : List F) : Prop := ∃ a ∈ x, a ≠ 0

/-- Find a nonzero vector in the kernel of a matrix with `m` columns (rows as lists),
by Gaussian elimination on the first column. Returns `none` iff the kernel is trivial. -/
def kernel : ℕ → List (List F) → Option (List F)
  | 0, _ => none
  | m + 1, rows =>
    match rows.find? (fun r => r.headD 0 != 0) with
    | none => some (1 :: List.replicate m 0)
    | some r =>
      let ci := (r.headD 0)⁻¹
      let rt := r.tail
      let rows' := rows.map (fun s =>
        let k := s.headD 0 * ci
        List.zipWith (fun a b => a - k * b) s.tail rt)
      match kernel m rows' with
      | none => none
      | some y => some (-(dot rt y) * ci :: y)

theorem kernel_sound : ∀ (m : ℕ) (rows : List (List F)) (x : List F),
    (∀ r ∈ rows, r.length = m) → kernel m rows = some x → x.length = m ∧ NZ x ∧ Sol rows x
  | 0, rows, x, _, h => by simp [kernel] at h
  | m + 1, rows, x, hlen, h => by
    unfold kernel at h
    split at h
    · rename_i hnone
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp, ⟨1, by simp, one_ne_zero⟩, fun r hr => ?_⟩
      have h0 : r.headD 0 = 0 := by
        have := List.find?_eq_none.1 hnone r hr
        simpa using this
      have hr' : r ≠ [] := by intro h; have := hlen r hr; simp [h] at this
      rw [dot_split _ _ hr' (by simp), h0, zero_mul, zero_add]
      exact dot_eq_zero_of_all_zero _ _ (by simp)
    · rename_i r hr
      have hrmem := List.mem_of_find?_eq_some hr
      have hc : r.headD 0 ≠ 0 := by simpa using List.find?_some hr
      dsimp only at h
      split at h
      · simp at h
      · rename_i y hy
        simp only [Option.some.injEq] at h
        subst h
        have hlen' : ∀ s ∈ rows.map (fun s =>
            List.zipWith (fun a b => a - s.headD 0 * (r.headD 0)⁻¹ * b) s.tail r.tail), s.length = m := by
          intro s hs
          obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
          simp [hlen s0 hs0, hlen r hrmem]
        obtain ⟨hyl, hynz, hysol⟩ := kernel_sound m _ y hlen' hy
        refine ⟨by simp [hyl], ?_, ?_⟩
        · obtain ⟨a, ha, ha0⟩ := hynz
          exact ⟨a, by simp [ha], ha0⟩
        · intro s hs
          have hs' : s ≠ [] := by intro h; have := hlen s hs; simp [h] at this
          have hsy := hysol _ (List.mem_map.2 ⟨s, hs, rfl⟩)
          rw [dot_zipWith _ _ _ _ (by simp [hlen s hs, hlen r hrmem])] at hsy
          rw [dot_split _ _ hs' (by simp)]
          simp only [List.headD_cons, List.tail_cons]
          rw [sub_eq_zero] at hsy
          rw [hsy]
          field_simp
          ring

theorem kernel_complete : ∀ (m : ℕ) (rows : List (List F)) (x : List F),
    (∀ r ∈ rows, r.length = m) → x.length = m → NZ x → Sol rows x → (kernel m rows).isSome
  | 0, rows, x, _, hx, hnz, _ => by
    obtain ⟨a, ha, _⟩ := hnz
    rw [List.length_eq_zero_iff] at hx; subst hx; simp at ha
  | m + 1, rows, x, hlen, hxl, hnz, hsol => by
    unfold kernel
    split
    · simp
    · rename_i r hr
      have hrmem := List.mem_of_find?_eq_some hr
      have hc : r.headD 0 ≠ 0 := by simpa using List.find?_some hr
      obtain ⟨x0, xt, rfl⟩ : ∃ x0 xt, x = x0 :: xt := by
        cases x with
        | nil => simp at hxl
        | cons a l => exact ⟨a, l, rfl⟩
      have hr' : r ≠ [] := by intro h; have := hlen r hrmem; simp [h] at this
      have hrx := hsol r hrmem
      rw [dot_split _ _ hr' (by simp)] at hrx
      simp only [List.headD_cons, List.tail_cons] at hrx
      have hcomp := kernel_complete m (rows.map (fun s =>
          List.zipWith (fun a b => a - s.headD 0 * (r.headD 0)⁻¹ * b) s.tail r.tail)) xt
        (by
          intro s hs
          obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
          simp [hlen s0 hs0, hlen r hrmem])
        (by simpa using hxl)
        (by
          by_contra hz
          simp only [NZ, not_exists, not_and, not_not] at hz
          have : dot r.tail xt = 0 := dot_eq_zero_of_all_zero _ _ hz
          rw [this, add_zero] at hrx
          have hx0 : x0 = 0 := by
            rcases mul_eq_zero.1 hrx with h | h
            · exact absurd h hc
            · exact h
          obtain ⟨a, ha, ha0⟩ := hnz
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact ha0 hx0
          · exact ha0 (hz a ha))
        (by
          intro s hs
          obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
          have hs' : s0 ≠ [] := by intro h; have := hlen s0 hs0; simp [h] at this
          have hsx := hsol s0 hs0
          rw [dot_split _ _ hs' (by simp)] at hsx
          simp only [List.headD_cons, List.tail_cons] at hsx
          rw [dot_zipWith _ _ _ _ (by simp [hlen s0 hs0, hlen r hrmem])]
          have e1 : dot r.tail xt = -(r.headD 0 * x0) := by linear_combination hrx
          have e2 : dot s0.tail xt = -(s0.headD 0 * x0) := by linear_combination hsx
          rw [e1, e2]
          field_simp
          ring)
      dsimp only
      split
      · rename_i heq; rw [heq] at hcomp; simp at hcomp
      · simp

end Kernel


/-! ## Exact polynomial division on coefficient lists -/

section Division

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
lemma lpoly_eq_head_tail (l : List F) : lpoly l = C (l.headD 0) + X * lpoly l.tail := by
  cases l <;> simp

/-- Coefficientwise difference of coefficient lists (padding with zeros). -/
def lsub : List F → List F → List F
  | [], b => b.map (fun x => -x)
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a - b) :: lsub as bs

omit [DecidableEq F] in
lemma lpoly_lsub : ∀ (a b : List F), lpoly (lsub a b) = lpoly a - lpoly b
  | [], b => by
    induction b with
    | nil => simp [lsub]
    | cons x b ih => simp only [lsub, List.map_cons, lpoly_cons, lpoly_nil] at ih ⊢; rw [ih]; simp; ring
  | a :: as, [] => by simp [lsub]
  | a :: as, b :: bs => by simp only [lsub, lpoly_cons, lpoly_lsub as bs, C_sub]; ring

omit [DecidableEq F] in
lemma lpoly_map_mul (c : F) : ∀ (l : List F), lpoly (l.map (c * ·)) = C c * lpoly l
  | [] => by simp
  | a :: l => by simp only [List.map_cons, lpoly_cons, lpoly_map_mul c l, C_mul]; ring

omit [DecidableEq F] in
lemma coeff_zero_lpoly (l : List F) : (lpoly l).coeff 0 = l.headD 0 := by
  rw [coeff_lpoly]; cases l <;> simp

omit [DecidableEq F] in
/-- If `lpoly l = X * R` then `lpoly l.tail = R`. -/
lemma lpoly_tail_of_eq_X_mul {l : List F} {R : F[X]} (h : lpoly l = X * R) : lpoly l.tail = R := by
  rw [lpoly_eq_head_tail] at h
  have h0 : l.headD 0 = 0 := by
    have := congrArg (fun f => f.coeff 0) h
    simpa using this
  rw [h0, C_0, zero_add] at h
  exact mul_left_cancel₀ X_ne_zero h

/-- Power-series style division by `E` with `E(0) ≠ 0` (`ci = E(0)⁻¹`), producing `k`
quotient coefficients, lowest first. -/
def psdiv (E : List F) (ci : F) : ℕ → List F → List F
  | 0, _ => []
  | k + 1, Q =>
    let p0 := Q.headD 0 * ci
    p0 :: psdiv E ci k (lsub Q (E.map (p0 * ·))).tail

omit [DecidableEq F] in
theorem psdiv_eq (E : List F) (hE : E.headD 0 ≠ 0) :
    ∀ (pl Q : List F), lpoly Q = lpoly pl * lpoly E → psdiv E (E.headD 0)⁻¹ pl.length Q = pl
  | [], _, _ => rfl
  | p0 :: pl, Q, h => by
    have hq0 : Q.headD 0 = p0 * E.headD 0 := by
      rw [← coeff_zero_lpoly, h, mul_coeff_zero, coeff_zero_lpoly, coeff_zero_lpoly]; rfl
    have hp0 : Q.headD 0 * (E.headD 0)⁻¹ = p0 := by rw [hq0]; field_simp
    simp only [List.length_cons, psdiv, hp0]
    congr 1
    apply psdiv_eq E hE pl
    apply lpoly_tail_of_eq_X_mul
    rw [lpoly_lsub, lpoly_map_mul, h, lpoly_cons]; ring

/-- Exact division `Q / E` of coefficient lists, returning `k` coefficients: strip the factors
of `X` from `E` (and the matching zero coefficients of `Q`), then divide as power series. -/
def divStrip (k : ℕ) : List F → List F → Option (List F)
  | [], _ => none
  | c :: E, Q => if c = 0 then divStrip k E Q.tail else some (psdiv (c :: E) c⁻¹ k Q)

theorem divStrip_eq (pl : List F) :
    ∀ (E Q : List F), lpoly E ≠ 0 → lpoly Q = lpoly pl * lpoly E → divStrip pl.length E Q = some pl
  | [], _, hE, _ => by simp at hE
  | c :: E, Q, hE, h => by
    unfold divStrip
    split_ifs with hc
    · subst hc
      simp only [lpoly_cons, C_0, zero_add] at hE h
      apply divStrip_eq pl E Q.tail (right_ne_zero_of_mul hE)
      apply lpoly_tail_of_eq_X_mul
      rw [h]; ring
    · simp only [Option.some.injEq]
      exact psdiv_eq (c :: E) hc pl Q h

end Division

/-! ## The Berlekamp–Welch decoder -/

section BW

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- The Berlekamp–Welch linear system: unknowns `E₀,…,E_e, Q₀,…,Q_{e+k-1}`, one row per
position `i`, expressing `Q(αᵢ) - rᵢ E(αᵢ) = 0`. -/
def bwRows (α r : Fin n → F) (e k : ℕ) : List (List F) :=
  List.ofFn (fun i => (pows (α i) (e + 1)).map (-(r i) * ·) ++ pows (α i) (e + k))

/-- **Berlekamp–Welch decoder.** Find a nonzero `(E, Q)` in the kernel of the key-equation
system by Gaussian elimination, then return the `k` coefficients of `Q / E`. -/
def bwDecode (α r : Fin n → F) (e k : ℕ) : Option (List F) :=
  match kernel ((e + 1) + (e + k)) (bwRows α r e k) with
  | none => none
  | some x => divStrip k (x.take (e + 1)) (x.drop (e + 1))

omit [DecidableEq F] in
lemma length_bwRows {α r : Fin n → F} {e k : ℕ} :
    ∀ row ∈ bwRows α r e k, row.length = (e + 1) + (e + k) := by
  intro row h
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 h
  simp

omit [DecidableEq F] in
lemma dot_bwRow (α r : Fin n → F) (e k : ℕ) (i : Fin n) (x : List F)
    (hx : x.length = (e + 1) + (e + k)) :
    dot ((pows (α i) (e + 1)).map (-(r i) * ·) ++ pows (α i) (e + k)) x =
      (lpoly (x.drop (e + 1))).eval (α i) - r i * (lpoly (x.take (e + 1))).eval (α i) := by
  conv_lhs => rw [← List.take_append_drop (e + 1) x]
  rw [dot_append _ _ _ _ (by simp; omega), dot_map_mul, dot_pows _ _ _ (by simp; omega),
    dot_pows _ _ _ (by simp; omega)]
  ring

omit [DecidableEq F] in
lemma sol_bwRows_iff (α r : Fin n → F) (e k : ℕ) (x : List F)
    (hx : x.length = (e + 1) + (e + k)) :
    Sol (bwRows α r e k) x ↔ KeyEq α r (lpoly (x.take (e + 1))) (lpoly (x.drop (e + 1))) := by
  constructor
  · intro h i
    have := h _ (List.mem_ofFn.2 ⟨i, rfl⟩)
    rw [dot_bwRow α r e k i x hx, sub_eq_zero] at this
    exact this
  · intro h row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hrow
    rw [dot_bwRow α r e k i x hx, h i, sub_self]

omit [DecidableEq F] in
lemma lpoly_ofFn {k : ℕ} (m : Fin k → F) : lpoly (List.ofFn m) = msgPoly m := by
  ext j
  rw [coeff_lpoly]
  by_cases hj : j < k
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    exact (coeff_msgPoly m ⟨j, hj⟩).symm
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    exact (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (mem_degreeLT.1 (msgPoly_mem m))
      (by exact_mod_cast (by omega : k ≤ j)))).symm

omit [DecidableEq F] in
lemma nz_of_lpoly_ne_zero {l : List F} (h : lpoly l ≠ 0) : NZ l := by
  by_contra h'
  simp only [NZ, not_exists, not_and, not_not] at h'
  exact h ((lpoly_eq_zero_iff l).2 h')

/-- **Correctness of the Berlekamp–Welch decoder.** If the received word `r` is within Hamming
distance `e` of the codeword of the message `m` (`k` coefficients), the evaluation points are
distinct and `2e + k ≤ n`, then `bwDecode` returns exactly `m`. -/
theorem bwDecode_correct {α : Fin n → F} (hα : Function.Injective α) {e k : ℕ}
    (hn : 2 * e + k ≤ n) (m : Fin k → F) (r : Fin n → F)
    (he : hammingDist (encodeVec α m) r ≤ e) : bwDecode α r e k = some (List.ofFn m) := by
  rw [← encode_msgPoly] at he
  have hp := msgPoly_mem m
  -- a nonzero solution exists
  obtain ⟨E0, Q0, hE0m, hE0d, hQ0d, hkey0⟩ := bw_exists hp r he
  set x0 := coeffList E0 (e + 1) ++ coeffList Q0 (e + k) with hx0
  have hx0l : x0.length = (e + 1) + (e + k) := by simp [hx0]
  have htake : x0.take (e + 1) = coeffList E0 (e + 1) := by
    rw [hx0, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hdrop : x0.drop (e + 1) = coeffList Q0 (e + k) := by
    rw [hx0, List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp),
      List.nil_append]
  have hE0deg : E0.degree < (e + 1 : ℕ) := by
    rw [degree_eq_natDegree hE0m.ne_zero, hE0d]; exact_mod_cast Nat.lt_succ_self e
  have hsol0 : Sol (bwRows α r e k) x0 := by
    rw [sol_bwRows_iff α r e k x0 hx0l, htake, hdrop, lpoly_coeffList hE0deg,
      lpoly_coeffList hQ0d]
    exact hkey0
  have hnz0 : NZ x0 := by
    obtain ⟨a, ha, ha0⟩ := nz_of_lpoly_ne_zero (l := coeffList E0 (e + 1))
      (by rw [lpoly_coeffList hE0deg]; exact hE0m.ne_zero)
    exact ⟨a, by rw [hx0]; exact List.mem_append_left _ ha, ha0⟩
  -- so the solver finds one
  have hsome := kernel_complete _ _ x0 length_bwRows hx0l hnz0 hsol0
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hxl, hxnz, hxsol⟩ := kernel_sound _ _ x length_bwRows hx
  rw [sol_bwRows_iff α r e k x hxl] at hxsol
  have hEdeg : (lpoly (x.take (e + 1))).degree ≤ e := by
    have := degree_lpoly_lt (x.take (e + 1))
    rw [List.length_take, min_eq_left (by omega)] at this
    by_cases h0 : lpoly (x.take (e + 1)) = 0
    · rw [h0, degree_zero]; exact bot_le
    · rw [degree_eq_natDegree h0] at this ⊢
      have : (lpoly (x.take (e + 1))).natDegree < e + 1 := by exact_mod_cast this
      exact_mod_cast Nat.lt_succ_iff.1 this
  have hQdeg : (lpoly (x.drop (e + 1))).degree < (e + k : ℕ) := by
    have := degree_lpoly_lt (x.drop (e + 1))
    rwa [List.length_drop, hxl, Nat.add_sub_cancel_left] at this
  have hQE := bw_correct hα hp r he hn hEdeg hQdeg hxsol
  have hE0 : lpoly (x.take (e + 1)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQE
    obtain ⟨a, ha, ha0⟩ := hxnz
    rw [← List.take_append_drop (e + 1) x, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ha0 ((lpoly_eq_zero_iff _).1 h0 a ha)
    · exact ha0 ((lpoly_eq_zero_iff _).1 hQE a ha)
  unfold bwDecode
  rw [hx]
  dsimp only
  have := divStrip_eq (List.ofFn m) (x.take (e + 1)) (x.drop (e + 1)) hE0 (by rw [lpoly_ofFn]; exact hQE)
  simpa using this

end BW

/-! ## A computable, verified GF(256) for QR codes (`x⁸+x⁴+x³+x²+1`, bit pattern `0x11D`) -/

section GF256Impl

/-- Shift-and-add multiplication in GF(2)[x]/(0x11D) of a byte `a` by the `k`-bit number `b`
(Horner on the bits of `b`, high bits first via recursion, `mulX` = `xtime`). -/
def gmulAux (a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, b => mulX 0x11D (gmulAux a k (b / 2)) ^^^ (if b % 2 = 1 then a else 0)

/-- GF(256) multiplication of bytes. -/
def gmul (a b : ℕ) : ℕ := gmulAux a 8 b

/-- GF(256) inverse of a byte, `a⁻¹ = a^254` (and `0⁻¹ = 0`). -/
def ginv (a : ℕ) : ℕ :=
  let a2 := gmul a a
  let a4 := gmul a2 a2
  let a8 := gmul a4 a4
  let a16 := gmul a8 a8
  let a32 := gmul a16 a16
  let a64 := gmul a32 a32
  let a128 := gmul a64 a64
  gmul a2 (gmul a4 (gmul a8 (gmul a16 (gmul a32 (gmul a64 a128)))))

lemma xor_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

lemma mulX_lt : ∀ a < 256, mulX 0x11D a < 256 := by decide +kernel

lemma gmulAux_lt {a : ℕ} (ha : a < 256) : ∀ k b, gmulAux a k b < 256
  | 0, _ => by simp [gmulAux]
  | k + 1, b => by
    unfold gmulAux
    refine xor_lt_256 (mulX_lt _ (gmulAux_lt ha k _)) ?_
    split_ifs <;> omega

lemma gmul_lt {a : ℕ} (ha : a < 256) (b : ℕ) : gmul a b < 256 := gmulAux_lt ha 8 b

lemma ginv_lt {a : ℕ} (ha : a < 256) : ginv a < 256 := gmul_lt (gmul_lt ha a) _

/-- Verified by the kernel over all 255 nonzero bytes. -/
theorem gmul_ginv : ∀ a < 256, a ≠ 0 → gmul a (ginv a) = 1 := by decide +kernel

theorem ginv_zero : ginv 0 = 0 := by decide +kernel

/-- The abstract field `GF(2)[x]/(x⁸+x⁴+x³+x²+1)`. -/
abbrev QRField := AdjoinRoot (toPoly 0x11D)

/-- Interpretation of a bit pattern as an element of `QRField`. -/
noncomputable def interp (a : ℕ) : QRField := AdjoinRoot.mk (toPoly 0x11D) (toPoly a)

lemma interp_xor (a b : ℕ) : interp (a ^^^ b) = interp a + interp b := by
  simp [interp, toPoly_xor]

lemma interp_mulX (c : ℕ) : interp (mulX 0x11D c) = interp c * AdjoinRoot.root (toPoly 0x11D) := by
  have hX : AdjoinRoot.mk (toPoly 0x11D) X = AdjoinRoot.root (toPoly 0x11D) := AdjoinRoot.mk_X
  unfold interp mulX
  split_ifs
  · rw [toPoly_xor, toPoly_shiftLeft, map_add, AdjoinRoot.mk_self, add_zero, map_mul,
      pow_one, hX, mul_comm]
  · rw [toPoly_shiftLeft, map_mul, pow_one, hX, mul_comm]

lemma interp_gmulAux (a : ℕ) : ∀ k b, b < 2 ^ k → interp (gmulAux a k b) = interp a * interp b
  | 0, b, hb => by
    have : b = 0 := by simpa using hb
    subst this; simp [gmulAux, interp, toPoly_zero]
  | k + 1, b, hb => by
    have ih := interp_gmulAux a k (b / 2) (by rw [pow_succ] at hb; omega)
    have hb' : b = 2 * (b / 2) + (decide (b % 2 = 1)).toNat := by
      by_cases h : b % 2 = 1 <;> simp [h] <;> omega
    have hX : AdjoinRoot.mk (toPoly 0x11D) X = AdjoinRoot.root (toPoly 0x11D) := AdjoinRoot.mk_X
    rw [gmulAux, interp_xor, interp_mulX, ih]
    conv_rhs => rw [hb']; unfold interp; rw [toPoly_bit]
    by_cases h : b % 2 = 1
    · simp [h, interp, hX]; ring
    · simp [h, interp, hX, toPoly_zero]; ring

lemma interp_gmul {a b : ℕ} (hb : b < 256) : interp (gmul a b) = interp a * interp b :=
  interp_gmulAux a 8 b hb

lemma interp_add_self (a : ℕ) : interp a + interp a = 0 := by
  rw [← interp_xor, Nat.xor_self]; simp [interp, toPoly_zero]

lemma interp_injective {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : interp a = interp b) :
    a = b := by
  unfold interp at h
  rw [AdjoinRoot.mk_eq_mk, CharTwo.sub_eq_add, ← toPoly_xor] at h
  have hz := eq_zero_of_dvd_of_natDegree_lt h (by
    rw [toPoly_natDegree_eight (P := 0x11D) (by decide) (by norm_num)]
    have := toPoly_natDegree_lt (k := 7) (xor_lt_256 ha hb)
    omega)
  rw [← toPoly_zero] at hz
  exact Nat.eq_of_xor_eq_zero (toPoly_injective hz)

end GF256Impl

/-- **GF(256)** as used by QR codes: bytes with XOR addition and multiplication modulo
`x⁸+x⁴+x³+x²+1`. All operations are computable; the field structure is proven below by
transfer along the injective homomorphism into `AdjoinRoot (x⁸+x⁴+x³+x²+1)`. -/
@[ext] structure GF256 where
  val : Fin 256
  deriving DecidableEq

namespace GF256

/-- Byte literal (reduced mod 256). -/
def byte (n : ℕ) : GF256 := ⟨⟨n % 256, Nat.mod_lt _ (by norm_num)⟩⟩

instance : Repr GF256 := ⟨fun a _ => repr a.val.val⟩
instance : Inhabited GF256 := ⟨⟨0⟩⟩

instance : Zero GF256 := ⟨⟨0⟩⟩
instance : One GF256 := ⟨⟨1⟩⟩
instance : Add GF256 := ⟨fun a b => ⟨⟨a.val.val ^^^ b.val.val, xor_lt_256 a.val.2 b.val.2⟩⟩⟩
instance : Neg GF256 := ⟨fun a => a⟩
instance : Sub GF256 := ⟨fun a b => a + b⟩
/-- Full 64 KiB multiplication table, built once from the verified `gmul`. -/
def mulEntry (i : Fin 65536) : Fin 256 :=
  ⟨gmul (i.val / 256) (i.val % 256), gmul_lt (Nat.div_lt_of_lt_mul (by simp)) _⟩

@[irreducible] def mulTable : Array (Fin 256) := Array.ofFn mulEntry

lemma mulTable_eq : mulTable = Array.ofFn mulEntry := by unfold mulTable; rfl

/-- Inverse table, built once from the verified `ginv`. -/
def invEntry (i : Fin 256) : Fin 256 := ⟨ginv i.val, ginv_lt i.2⟩

@[irreducible] def invTable : Array (Fin 256) := Array.ofFn invEntry

lemma invTable_eq : invTable = Array.ofFn invEntry := by unfold invTable; rfl

lemma mulIdx_lt (a b : Fin 256) : a.val * 256 + b.val < mulTable.size := by
  rw [mulTable_eq, Array.size_ofFn]; omega

lemma invIdx_lt (a : Fin 256) : a.val < invTable.size := by
  rw [invTable_eq, Array.size_ofFn]; omega

instance : Mul GF256 := ⟨fun a b => ⟨mulTable[a.val.val * 256 + b.val.val]'(mulIdx_lt a.val b.val)⟩⟩
instance : Inv GF256 := ⟨fun a => ⟨invTable[a.val.val]'(invIdx_lt a.val)⟩⟩

lemma mul_val (a b : GF256) : (a * b).val.val = gmul a.val.val b.val.val := by
  show (mulTable[a.val.val * 256 + b.val.val]'(mulIdx_lt a.val b.val)).val = _
  simp only [mulTable_eq, Array.getElem_ofFn, mulEntry]
  have hb := b.val.2
  congr 1
  · omega
  · omega

lemma inv_val (a : GF256) : a⁻¹.val.val = ginv a.val.val := by
  show (invTable[a.val.val]'(invIdx_lt a.val)).val = _
  simp only [invTable_eq, Array.getElem_ofFn, invEntry]
instance : Div GF256 := ⟨fun a b => a * b⁻¹⟩
instance : SMul ℕ GF256 := ⟨nsmulRec⟩
instance : SMul ℤ GF256 := ⟨zsmulRec⟩
instance : Pow GF256 ℕ := ⟨fun a n => npowRec n a⟩

/-- `ℕ → GF256` by repeated addition of `1`. -/
def natCastRec : ℕ → GF256
  | 0 => 0
  | n + 1 => natCastRec n + 1

instance : NatCast GF256 := ⟨natCastRec⟩
instance : IntCast GF256 := ⟨fun z => match z with
  | Int.ofNat n => (n : GF256)
  | Int.negSucc n => -((n + 1 : ℕ) : GF256)⟩

/-- The embedding into the abstract field. -/
noncomputable def φ (a : GF256) : QRField := interp a.val.val

lemma φ_injective : Function.Injective φ := fun a b h =>
  GF256.ext (Fin.ext (interp_injective a.val.2 b.val.2 h))

lemma φ_zero : φ 0 = 0 := by show interp 0 = 0; simp [interp, toPoly_zero]
lemma φ_one : φ 1 = 1 := by
  show interp 1 = 1
  simp [interp, toPoly_one]
lemma φ_add (a b : GF256) : φ (a + b) = φ a + φ b := interp_xor _ _
lemma φ_mul (a b : GF256) : φ (a * b) = φ a * φ b := by
  unfold φ; rw [mul_val]; exact interp_gmul b.val.2
lemma φ_neg (a : GF256) : φ (-a) = -φ a := (neg_eq_of_add_eq_zero_right (interp_add_self _)).symm
lemma φ_sub (a b : GF256) : φ (a - b) = φ a - φ b := by
  rw [sub_eq_add_neg, ← φ_neg]; exact φ_add a b
lemma φ_nsmul (n : ℕ) (a : GF256) : φ (n • a) = n • φ a := by
  induction n with
  | zero => show φ 0 = _; rw [φ_zero, zero_smul]
  | succ n ih => show φ (n • a + a) = _; rw [φ_add, ih, succ_nsmul]
lemma φ_zsmul (n : ℤ) (a : GF256) : φ (n • a) = n • φ a := by
  cases n with
  | ofNat n => show φ (n • a) = _; rw [φ_nsmul]; simp
  | negSucc n => show φ (-((n + 1) • a)) = _; rw [φ_neg, φ_nsmul, negSucc_zsmul]
lemma φ_npow (a : GF256) (n : ℕ) : φ (a ^ n) = φ a ^ n := by
  induction n with
  | zero => show φ 1 = _; rw [φ_one, pow_zero]
  | succ n ih => show φ (a ^ n * a) = _; rw [φ_mul, ih, pow_succ]
lemma φ_natCast (n : ℕ) : φ n = n := by
  induction n with
  | zero => show φ 0 = _; rw [φ_zero, Nat.cast_zero]
  | succ n ih => show φ ((n : GF256) + 1) = _; rw [φ_add, ih, φ_one, Nat.cast_succ]
lemma φ_intCast (n : ℤ) : φ n = n := by
  cases n with
  | ofNat n => show φ (n : GF256) = _; rw [φ_natCast]; simp
  | negSucc n => show φ (-((n + 1 : ℕ) : GF256)) = _; rw [φ_neg, φ_natCast, Int.cast_negSucc]

/-- The ring axioms, transferred (noncomputably, but only the proofs are used). -/
@[instance_reducible] noncomputable def ringAux : CommRing GF256 :=
  φ_injective.commRing φ φ_zero φ_one φ_add φ_mul φ_neg φ_sub φ_nsmul φ_zsmul φ_npow
    φ_natCast φ_intCast

instance instCommRing : CommRing GF256 where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := fun n a => npowRec n a
  natCast := natCastRec
  intCast := IntCast.intCast
  add_assoc := ringAux.add_assoc
  zero_add := ringAux.zero_add
  add_zero := ringAux.add_zero
  nsmul_zero := ringAux.nsmul_zero
  nsmul_succ := ringAux.nsmul_succ
  add_comm := ringAux.add_comm
  left_distrib := ringAux.left_distrib
  right_distrib := ringAux.right_distrib
  zero_mul := ringAux.zero_mul
  mul_zero := ringAux.mul_zero
  mul_assoc := ringAux.mul_assoc
  one_mul := ringAux.one_mul
  mul_one := ringAux.mul_one
  npow_zero := ringAux.npow_zero
  npow_succ := ringAux.npow_succ
  natCast_zero := ringAux.natCast_zero
  natCast_succ := ringAux.natCast_succ
  sub_eq_add_neg := ringAux.sub_eq_add_neg
  zsmul_zero' := ringAux.zsmul_zero'
  zsmul_succ' := ringAux.zsmul_succ'
  zsmul_neg' := ringAux.zsmul_neg'
  neg_add_cancel := ringAux.neg_add_cancel
  intCast_ofNat := ringAux.intCast_ofNat
  intCast_negSucc := ringAux.intCast_negSucc
  mul_comm := ringAux.mul_comm

lemma mul_inv_cancel' (a : GF256) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  apply GF256.ext; apply Fin.ext
  rw [mul_val, inv_val]
  apply gmul_ginv _ a.val.2
  intro h; apply ha; apply GF256.ext; apply Fin.ext; exact h


lemma inv_zero' : (⟨0⟩ : GF256)⁻¹ = ⟨0⟩ := by
  have h : ginv (0 : Fin 256).val = (0 : Fin 256).val := by decide +kernel
  apply GF256.ext; apply Fin.ext
  rw [inv_val]; exact h

instance instField : Field GF256 where
  __ := instCommRing
  inv := Inv.inv
  div := (· / ·)
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  exists_pair_ne := ⟨⟨0⟩, ⟨1⟩, fun h => absurd (congrArg (fun a : GF256 => a.val.val) h) (by norm_num)⟩
  nnqsmul := _
  qsmul := _

end GF256

/-! ## QR evaluation points `αʲ = 2ʲ` and the QR-sized instance -/

namespace GF256

lemma φ_two : φ (byte 2) = AdjoinRoot.root (toPoly 0x11D) := by
  show interp 2 = _
  have h2 : toPoly 2 = X := by
    have := toPoly_shiftLeft 1 1
    rw [toPoly_one, pow_one, mul_one] at this
    exact this
  rw [interp, h2, AdjoinRoot.mk_X]

/-- Powers of `α = 2` are distinct below the multiplicative order 255. -/
lemma two_pow_injOn {i j : ℕ} (hi : i < 255) (hj : j < 255) (h : byte 2 ^ i = byte 2 ^ j) :
    i = j := by
  have hord : orderOf (AdjoinRoot.root (toPoly 0x11D)) = 255 := by
    have := qr_orderOf_root; rwa [← toPoly_0x11D] at this
  have h' := congrArg φ h
  rw [φ_npow, φ_npow, φ_two] at h'
  exact pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; exact hi)
    (by rw [Set.mem_Iio, hord]; exact hj) h'

end GF256

/-- Table of `2ʲ`, `j < 256`. -/
@[irreducible] def expTable : Array GF256 := Array.ofFn (fun j : Fin 256 => GF256.byte 2 ^ j.val)

lemma expTable_eq : expTable = Array.ofFn (fun j : Fin 256 => GF256.byte 2 ^ j.val) := by
  unfold expTable; rfl

lemma expTable_size : expTable.size = 256 := by rw [expTable_eq, Array.size_ofFn]

/-- The QR evaluation points `α⁰, α¹, …, α^(n-1)` (`α = 2`). -/
def qrα (n : ℕ) (j : Fin n) : GF256 :=
  if h : j.val < 256 then expTable[j.val]'(by rw [expTable_size]; exact h) else 0

lemma qrα_eq {n : ℕ} (j : Fin n) (h : j.val < 256) : qrα n j = GF256.byte 2 ^ j.val := by
  simp [qrα, h, expTable_eq]

/-- The QR evaluation points are distinct for every block length `n ≤ 255`. -/
theorem qrα_injective {n : ℕ} (hn : n ≤ 255) : Function.Injective (qrα n) := by
  intro i j h
  rw [qrα_eq i (by omega), qrα_eq j (by omega)] at h
  exact Fin.ext (GF256.two_pow_injOn (by omega) (by omega) h)

/-- **Verified decoding for a QR-sized block** (`n = 26, k = 19`, the size of a version 1-L
block; `e = 3 = ⌊(26-19)/2⌋` errors): whatever the message and whichever ≤ 3 symbols are
corrupted, `bwDecode` returns the message. -/
theorem qr_v1L_decode (m : Fin 19 → GF256) (r : Fin 26 → GF256)
    (h : hammingDist (encodeVec (qrα 26) m) r ≤ 3) :
    bwDecode (qrα 26) r 3 19 = some (List.ofFn m) :=
  bwDecode_correct (qrα_injective (by norm_num)) (by norm_num) m r h

/-- General version: any block length `n ≤ 255`, any `k`, `e` with `2e + k ≤ n`. -/
theorem qr_decode {n k e : ℕ} (hn255 : n ≤ 255) (hn : 2 * e + k ≤ n) (m : Fin k → GF256)
    (r : Fin n → GF256) (h : hammingDist (encodeVec (qrα n) m) r ≤ e) :
    bwDecode (qrα n) r e k = some (List.ofFn m) :=
  bwDecode_correct (qrα_injective hn255) hn m r h

/-! ## Decoding actual QR / ZXing codewords (generator-polynomial view, checked)

A QR block is the word `c` (`c j` = coefficient of `xʲ`, i.e. byte `n-1-j` of the block) with
vanishing syndromes `∑ⱼ c j (α^l)^j = 0`, `l < n - k` (generator base `b = 0`). This is the dual
of the evaluation code at the points `αʲ`, hence the evaluation code with column multipliers
`vⱼ = 1 / ∏_{i ≠ j} (αʲ - αⁱ)`. `qrDecodeWord` divides out these multipliers, runs the verified
`bwDecode`, re-multiplies, and **checks** the result (syndromes zero, distance ≤ ⌊(n-k)/2⌋)
before returning it. Soundness is `qrDecodeWord_sound` (no miscorrection is ever returned
unflagged); completeness within the radius, via the shortened-code duality, is
`RoboLean.Barcode.Duality.qrDecodeWord_complete`. -/

/-- Evaluate a coefficient list at `β` (Horner). -/
def evalList {F : Type*} [Field F] (l : List F) (β : F) : F := l.foldr (fun a acc => a + β * acc) 0

/-- Decode a QR word (indexed by polynomial degree). -/
def qrDecodeWord (n k : ℕ) (c : Fin n → GF256) : Option (Fin n → GF256) :=
  let e := (n - k) / 2
  let a := qrα n
  let wArr : Array GF256 := Array.ofFn (fun j : Fin n =>
    (List.finRange n).foldl (fun acc i => if i = j then acc else acc * (a j - a i)) 1)
  let w : Fin n → GF256 := fun j => wArr[j.val]'(by simp [wArr])
  match bwDecode a (fun j => c j * w j) e k with
  | none => none
  | some p =>
    let cArr : Array GF256 := Array.ofFn (fun j : Fin n => evalList p (a j) / w j)
    let c' : Fin n → GF256 := fun j => cArr[j.val]'(by simp [cArr])
    if syndrome (GF256.byte 2) 0 k c' = 0 ∧ hammingDist c' c ≤ e then some c' else none

/-- **Checked soundness**: anything `qrDecodeWord` returns is a QR codeword (all `n - k`
syndromes vanish) within the error radius `⌊(n-k)/2⌋` of the received word. -/
theorem qrDecodeWord_sound {n k : ℕ} {c c' : Fin n → GF256} (h : qrDecodeWord n k c = some c') :
    syndrome (GF256.byte 2) 0 k c' = 0 ∧ hammingDist c' c ≤ (n - k) / 2 := by
  unfold qrDecodeWord at h
  dsimp only at h
  split at h
  · simp at h
  · split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h; exact hc

/-- Decode a QR block given as bytes in transmission order (first byte = highest degree),
returning the corrected block. -/
def qrDecodeBlock (blk : List ℕ) (k : ℕ) : Option (List ℕ) :=
  let n := blk.length
  let arr := blk.toArray
  let c : Fin n → GF256 := fun j => GF256.byte (arr[n - 1 - j.val]?.getD 0)
  (qrDecodeWord n k c).map (fun c' => (List.ofFn c').reverse.map (fun b => b.val.val))

/-! ### Runs -/

/-- A 19-byte message, RS-encoded at the 26 QR points, with 3 corrupted symbols. -/
def demoMsg : Fin 19 → GF256 := fun i => GF256.byte ("HELLO, LEAN 4 QR!!!".toList.getD i ' ').toNat
def demoCodeword : Fin 26 → GF256 := encodeVec (qrα 26) demoMsg
def demoReceived : Fin 26 → GF256 := fun i =>
  if i.val = 1 then demoCodeword i + GF256.byte 0x55
  else if i.val = 7 then GF256.byte 0
  else if i.val = 20 then demoCodeword i * GF256.byte 3 else demoCodeword i

/-- info: 3 -/
#guard_msgs in #eval hammingDist demoCodeword demoReceived
/-- info: some "HELLO, LEAN 4 QR!!!" -/
#guard_msgs in
#eval (bwDecode (qrα 26) demoReceived 3 19).map (fun l => String.ofList (l.map (fun b => Char.ofNat b.val.val)))
/-- info: true -/
#guard_msgs in #eval bwDecode (qrα 26) demoReceived 3 19 == some (List.ofFn demoMsg)

/-- The "HELLO WORLD" version 1-M QR block (16 data + 10 EC codewords, from the standard
tutorial example), with 5 bytes corrupted; decoding restores it exactly. -/
def helloWorld1M : List ℕ :=
  [32, 91, 11, 120, 209, 114, 220, 77, 67, 64, 236, 17, 236, 17, 236, 17,
   196, 35, 39, 119, 235, 215, 231, 226, 93, 23]
def helloWorld1MCorrupt : List ℕ :=
  [32, 0, 11, 120, 209, 114, 1, 77, 67, 64, 236, 17, 99, 17, 236, 17,
   196, 35, 39, 119, 235, 0, 231, 226, 93, 23]

/-- info: true -/
#guard_msgs in #eval qrDecodeBlock helloWorld1MCorrupt 16 == some helloWorld1M

end RoboLean.Barcode.Decoder
