import Mathlib

/-!
# Imaging geometry of barcode reading

Sorry-free statements explaining why standard barcode decoders are robust to the imaging
process:

1. Uniform ink spread / print gain / threshold bias changes bar widths but leaves every
   edge-to-similar-edge measurement `eᵢ = wᵢ + wᵢ₊₁` exactly invariant (`eMeas_inkSpread`);
   raw bar widths are not invariant (`inkSpread_bar_ne`). Consequence: UPC digits 1/7 and 2/8
   are e-ambiguous (`upc_1_7_ambiguous`, `upc_2_8_ambiguous`).
2. Normalised e-measurements are invariant under magnification, translation and ink spread, so
   any decoder factoring through them is invariant (`decoder_invariant`).
3. Rounding recovers integer module counts when each edge is localised to `< 1/4` module
   (`round_eMeas_of_edge_error`), sharp (`quarter_module_sharp`); explicit budget with an
   estimated module (`round_of_estimated_module`, `module_estimate_error`).
4. QR finder pattern: run-length ratios are scale invariant (`finder_ratio_scale`); the
   cross-ratio is perspective invariant (`crossRatio_mobius`, `finder_crossRatio_mobius`),
   while simple ratios are not (`ratio_not_projective_invariant`).
5. Four-point homography: existence and uniqueness up to scale (`exists_unique_homography`).
6. Pixel corollary (`round_eMeas_pixels`).
-/

namespace RoboLean.Barcode.Geometry

open Finset

/-! ## 1. Scanline model and ink spread -/

/-- Edge positions of a scanline: `edge x₀ w j = x₀ + ∑_{i<j} w i`. Element `j` (a bar if `j`
is even, a space if `j` is odd) occupies `[edge j, edge (j+1)]`. -/
noncomputable def edge (x₀ : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ := x₀ + ∑ i ∈ range j, w i

theorem edge_succ (x₀ : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    edge x₀ w (j + 1) = edge x₀ w j + w j := by
  simp [edge, sum_range_succ]; ring

/-- Width of element `j` read off from the edges. -/
theorem edge_succ_sub (x₀ : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    edge x₀ w (j + 1) - edge x₀ w j = w j := by
  rw [edge_succ]; ring

/-- Uniform ink spread (print gain / blooming / threshold bias) by total amount `δ`: every bar
(even index) becomes `δ` wider and every space (odd index) `δ` narrower. -/
def inkSpread (δ : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ := if Even j then w j + δ else w j - δ

/-- Edge-to-similar-edge measurement `e_j = w_j + w_{j+1}` (bar+space or space+bar), i.e. the
distance between edge `j` and edge `j+2`, which are both leading or both trailing edges. -/
def eMeas (w : ℕ → ℝ) (j : ℕ) : ℝ := w j + w (j + 1)

theorem eMeas_eq_edge_sub (x₀ : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    eMeas w j = edge x₀ w (j + 2) - edge x₀ w j := by
  simp only [eMeas, edge, sum_range_succ]; ring

/-- **Edge-to-similar-edge invariance.** Every `e`-measurement is exactly unchanged by uniform
ink spread of any amount `δ`. -/
theorem eMeas_inkSpread (δ : ℝ) (w : ℕ → ℝ) (j : ℕ) : eMeas (inkSpread δ w) j = eMeas w j := by
  rcases Nat.even_or_odd j with h | h
  · have : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 h.add_one
    simp [eMeas, inkSpread, h, this]
  · have : Even (j + 1) := h.add_one
    have h' : ¬ Even j := Nat.not_even_iff_odd.2 h
    simp [eMeas, inkSpread, h', this]

/-- Raw bar widths are *not* ink-spread invariant: the first bar changes by exactly `δ`. -/
theorem inkSpread_bar_ne (δ : ℝ) (hδ : δ ≠ 0) (w : ℕ → ℝ) : inkSpread δ w 0 ≠ w 0 := by
  simp [inkSpread, hδ]

/-- Sum of an even number of consecutive elements (a "pitch", e.g. a UPC/EAN character width of
7 modules measured leading-edge to leading-edge) is ink-spread invariant. -/
theorem sum_inkSpread_even (δ : ℝ) (w : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (2 * k), inkSpread δ w i = ∑ i ∈ range (2 * k), w i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ, ih]
    have h1 : Even (2 * k) := even_two_mul k
    have h2 : ¬ Even (2 * k + 1) := by simp
    simp [inkSpread, h1, h2]; ring

/-- **Edge-level ink spread model.** Ink spread moves every bar's leading edge by `-δ/2` and
trailing edge by `+δ/2`. Any edge displacement `s` that is 2-periodic (`s (j+2) = s j`, the
same shift for all leading edges and the same for all trailing edges) leaves every
edge-to-similar-edge distance unchanged. -/
theorem similarEdge_invariant (x s : ℕ → ℝ) (hs : ∀ j, s (j + 2) = s j) (j : ℕ) :
    (x (j + 2) + s (j + 2)) - (x j + s j) = x (j + 2) - x j := by
  rw [hs]; ring

/-- The edge-level ink-spread displacement produces exactly the width model `inkSpread`. -/
theorem inkSpread_from_edges (x₀ δ : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    let s : ℕ → ℝ := fun i => if Even i then -δ / 2 else δ / 2
    (edge x₀ w (j + 1) + s (j + 1)) - (edge x₀ w j + s j) = inkSpread δ w j := by
  intro s
  rw [edge_succ]
  rcases Nat.even_or_odd j with h | h
  · have : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 h.add_one
    simp [s, inkSpread, h, this]; ring
  · have : Even (j + 1) := h.add_one
    have h' : ¬ Even j := Nat.not_even_iff_odd.2 h
    simp [s, inkSpread, h', this]; ring

/-! ### UPC-A / EAN-13: the 1/7 and 2/8 ambiguity

Left-hand odd-parity UPC digits are 4 elements (space, bar, space, bar) totalling 7 modules.
Decoding by the two `e`-measurements `T₁ = w₀+w₁`, `T₂ = w₁+w₂` is ink-spread immune, but it
cannot separate digit 1 (`2,2,2,1`) from 7 (`1,3,1,2`), nor 2 (`2,1,2,2`) from 8 (`1,2,1,3`);
ISO/IEC 15420 decoders resolve these with an (ink-spread *sensitive*) bar-width check. -/

/-- UPC left odd-parity widths of digits 1, 7, 2, 8 (as functions on indices `0..3`). -/
def upc1 : ℕ → ℝ := fun i => [2, 2, 2, 1].getD i 0
def upc7 : ℕ → ℝ := fun i => [1, 3, 1, 2].getD i 0
def upc2 : ℕ → ℝ := fun i => [2, 1, 2, 2].getD i 0
def upc8 : ℕ → ℝ := fun i => [1, 2, 1, 3].getD i 0

/-- Digits 1 and 7 have identical edge-to-similar-edge measurements yet differ. -/
theorem upc_1_7_ambiguous :
    eMeas upc1 0 = eMeas upc7 0 ∧ eMeas upc1 1 = eMeas upc7 1 ∧ eMeas upc1 2 = eMeas upc7 2 ∧
      upc1 0 ≠ upc7 0 := by
  simp [eMeas, upc1, upc7]; norm_num

/-- Digits 2 and 8 have identical edge-to-similar-edge measurements yet differ. -/
theorem upc_2_8_ambiguous :
    eMeas upc2 0 = eMeas upc8 0 ∧ eMeas upc2 1 = eMeas upc8 1 ∧ eMeas upc2 2 = eMeas upc8 2 ∧
      upc2 0 ≠ upc8 0 := by
  simp [eMeas, upc2, upc8]; norm_num

/-! ## 2. Scale / shift invariance and decoder invariance -/

/-- An affine change of scanline coordinate `x ↦ a x + b` (magnification `a`, offset `b`) maps
the edges of widths `w` to the edges of widths `a • w`. -/
theorem edge_affine (a b x₀ : ℝ) (w : ℕ → ℝ) (j : ℕ) :
    a * edge x₀ w j + b = edge (a * x₀ + b) (a • w) j := by
  simp only [edge, Pi.smul_apply, smul_eq_mul, ← mul_sum]; ring

theorem eMeas_smul (a : ℝ) (w : ℕ → ℝ) (j : ℕ) : eMeas (a • w) j = a * eMeas w j := by
  simp [eMeas]; ring

/-- Normalised `e`-measurement: `e_j` divided by the reference pitch `p = ∑_{i<2n} wᵢ`
(leading edge of element `0` to leading edge of element `2n`; for UPC/EAN a character with
`2n = 4` elements, pitch `7` modules). -/
noncomputable def normE (n : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  eMeas w j / ∑ i ∈ range (2 * n), w i

/-- Normalised `e`-measurements are invariant under any non-zero magnification. -/
theorem normE_smul (n : ℕ) {a : ℝ} (ha : a ≠ 0) (w : ℕ → ℝ) : normE n (a • w) = normE n w := by
  funext j
  simp only [normE, eMeas_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  exact mul_div_mul_left _ _ ha

/-- Normalised `e`-measurements are invariant under uniform ink spread. -/
theorem normE_inkSpread (n : ℕ) (δ : ℝ) (w : ℕ → ℝ) : normE n (inkSpread δ w) = normE n w := by
  funext j; simp only [normE, eMeas_inkSpread, sum_inkSpread_even]

/-- The imaging nuisance group acting on a width sequence: words in magnifications
(`a ≠ 0`; shifts act trivially on widths, see `edge_affine`) and uniform ink spreads. -/
inductive Nuisance (w : ℕ → ℝ) : (ℕ → ℝ) → Prop
  | refl : Nuisance w w
  | scale {v : ℕ → ℝ} (a : ℝ) (ha : a ≠ 0) : Nuisance w v → Nuisance w (a • v)
  | spread {v : ℕ → ℝ} (δ : ℝ) : Nuisance w v → Nuisance w (inkSpread δ v)

theorem normE_of_nuisance (n : ℕ) {w v : ℕ → ℝ} (h : Nuisance w v) : normE n v = normE n w := by
  induction h with
  | refl => rfl
  | scale a ha _ ih => rw [normE_smul n ha, ih]
  | spread δ _ ih => rw [normE_inkSpread, ih]

/-- **Decoder invariance.** Any decoder that factors through the normalised edge-to-similar-edge
measurements (`D ∘ normE n`) returns identical output on every image of the symbol obtained by
any combination of magnification, translation and uniform ink spread. -/
theorem decoder_invariant {α : Type*} (D : (ℕ → ℝ) → α) (n : ℕ) {w v : ℕ → ℝ}
    (h : Nuisance w v) : D (normE n v) = D (normE n w) := by
  rw [normE_of_nuisance n h]

/-- Concrete form: `δ`-ink-spread followed by magnification `a > 0`. -/
theorem decoder_invariant_scale_spread {α : Type*} (D : (ℕ → ℝ) → α) (n : ℕ) (w : ℕ → ℝ)
    {a : ℝ} (ha : 0 < a) (δ : ℝ) : D (normE n (a • inkSpread δ w)) = D (normE n w) :=
  decoder_invariant D n (.scale a ha.ne' (.spread δ .refl))

/-! ## 3. Rounding robustness and the edge-localisation budget -/

/-- Rounding recovers an integer from any perturbation of size `< 1/2`. -/
theorem round_eq_of_abs_sub_lt {y : ℝ} {k : ℤ} (h : |y - k| < 1 / 2) : round y = k := by
  rw [round_eq, Int.floor_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-- **Per-edge tolerance `< 1/4` module (known module size).** True edges `x`, measured edges
`y` with every error `≤ ε`, true module `u > 0`, and the true `e`-measurement equal to `k`
modules. If `ε < u/4` then rounding the measured `e` in module units returns `k` exactly. -/
theorem round_eMeas_of_edge_error {x y : ℕ → ℝ} {u ε : ℝ} {k : ℤ} {j : ℕ} (hu : 0 < u)
    (hx : ∀ i, |y i - x i| ≤ ε) (hk : x (j + 2) - x j = u * k) (hε : ε < u / 4) :
    round ((y (j + 2) - y j) / u) = k := by
  apply round_eq_of_abs_sub_lt
  have h1 := hx (j + 2); have h2 := hx j
  rw [abs_le] at h1 h2
  have : (y (j + 2) - y j) / u - k = ((y (j + 2) - x (j + 2)) - (y j - x j)) / u := by
    field_simp; linarith
  rw [this, abs_div, abs_of_pos hu, div_lt_iff₀ hu, abs_lt]
  constructor <;> linarith

/-- **Tolerance with an estimated module.** If the measured `e` is within `2ε` of `u·k`
(two edges, each within `ε`), and the module estimate `uh > 0` is within `η` of `u`, then
rounding `em/uh` returns `k` provided `2ε + |k|·η < uh/2`. -/
theorem round_of_estimated_module {em u uh ε η : ℝ} {k : ℤ} (huh : 0 < uh)
    (he : |em - u * k| ≤ 2 * ε) (hη : |uh - u| ≤ η) (hbudget : 2 * ε + |(k : ℝ)| * η < uh / 2) :
    round (em / uh) = k := by
  apply round_eq_of_abs_sub_lt
  have : em / uh - k = ((em - u * k) + k * (u - uh)) / uh := by field_simp; ring
  rw [this, abs_div, abs_of_pos huh, div_lt_iff₀ huh]
  calc |(em - u * k) + k * (u - uh)| ≤ |em - u * k| + |(k : ℝ)| * |u - uh| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 2 * ε + |(k : ℝ)| * η := by
        gcongr; rw [abs_sub_comm]; exact hη
    _ < uh / 2 := hbudget
    _ = 1 / 2 * uh := by ring

/-- Module estimate from a pitch of `N` modules (edge `0` to edge `2n`): with every edge
within `ε`, `uh = (y_{2n} - y_0)/N` is within `2ε/N` of the true module `u`. -/
theorem module_estimate_error {x y : ℕ → ℝ} {u ε N : ℝ} {n : ℕ} (hN : 0 < N)
    (hx : ∀ i, |y i - x i| ≤ ε) (hp : x (2 * n) - x 0 = u * N) :
    |(y (2 * n) - y 0) / N - u| ≤ 2 * ε / N := by
  have h1 := hx (2 * n); have h2 := hx 0
  rw [abs_le] at h1 h2
  have : (y (2 * n) - y 0) / N - u = ((y (2 * n) - x (2 * n)) - (y 0 - x 0)) / N := by
    field_simp; linarith
  rw [this, abs_div, abs_of_pos hN, div_le_div_iff_of_pos_right hN, abs_le]
  constructor <;> linarith

/-! ## 6. Sampling corollary -/

/-- **Pixel-level statement.** With module size `u ≥ 1` pixel and sub-pixel edge accuracy
`ε < 1/4` pixel, every edge-to-similar-edge measurement rounds to its true integer module count
(so `round_eMeas_of_edge_error` applies). More generally any `ε < u/4` suffices. -/
theorem round_eMeas_pixels {x y : ℕ → ℝ} {u ε : ℝ} {k : ℤ} {j : ℕ} (hu : 1 ≤ u)
    (hx : ∀ i, |y i - x i| ≤ ε) (hk : x (j + 2) - x j = u * k) (hε : ε < 1 / 4) :
    round ((y (j + 2) - y j) / u) = k :=
  round_eMeas_of_edge_error (by linarith) hx hk (by linarith)

/-- The `1/4`-module budget is sharp: an error of exactly `u/4` on each of the two edges, in
opposite directions, can push the measurement to a half-integer, where rounding fails. -/
theorem quarter_module_sharp (u : ℝ) (hu : 0 < u) :
    round ((u * 1 + u / 4 - (-(u / 4))) / u) ≠ (1 : ℤ) := by
  have : (u * 1 + u / 4 - (-(u / 4))) / u = 3 / 2 := by field_simp; ring
  rw [this, round_eq]; norm_num

/-! ## 4. QR finder pattern: scale vs. perspective -/

/-- Cross-ratio of four collinear points (as coordinates on the line). -/
noncomputable def crossRatio (a b c d : ℝ) : ℝ := ((c - a) * (d - b)) / ((c - b) * (d - a))

/-- 1D projective (Möbius) map `x ↦ (p x + q)/(r x + s)`. -/
noncomputable def mobius (p q r s x : ℝ) : ℝ := (p * x + q) / (r * x + s)

theorem mobius_sub (p q r s x y : ℝ) (hx : r * x + s ≠ 0) (hy : r * y + s ≠ 0) :
    mobius p q r s x - mobius p q r s y = (p * s - q * r) * (x - y) / ((r * x + s) * (r * y + s)) := by
  unfold mobius; rw [div_sub_div _ _ hx hy]; congr 1; ring

/-- **Cross-ratio invariance.** A non-degenerate 1D projective map (the restriction of a
camera homography to a scanline) preserves the cross-ratio of four collinear points (wherever
the map is defined). -/
theorem crossRatio_mobius (p q r s a b c d : ℝ) (hdet : p * s - q * r ≠ 0)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d) =
      crossRatio a b c d := by
  unfold crossRatio
  rw [mobius_sub _ _ _ _ _ _ hc ha, mobius_sub _ _ _ _ _ _ hd hb, mobius_sub _ _ _ _ _ _ hc hb,
    mobius_sub _ _ _ _ _ _ hd ha]
  rcases eq_or_ne (c - b) 0 with h1 | h1
  · simp [h1]
  rcases eq_or_ne (d - a) 0 with h2 | h2
  · simp [h2]
  field_simp

/-- Edges of a `1:1:3:1:1` finder-pattern scan with module `u` starting at `x₀`:
`x₀, x₀+u, x₀+2u, x₀+5u, x₀+6u, x₀+7u`. -/
def finderEdges (x₀ u : ℝ) : Fin 6 → ℝ := ![x₀, x₀ + u, x₀ + 2 * u, x₀ + 5 * u, x₀ + 6 * u, x₀ + 7 * u]

/-- The finder run-length ratios `1:1:3:1:1` are independent of module size and position
(scale/shift invariance, i.e. fronto-parallel viewing at any distance). -/
theorem finder_ratio_scale (x₀ u : ℝ) (hu : u ≠ 0) :
    (finderEdges x₀ u 3 - finderEdges x₀ u 2) / (finderEdges x₀ u 1 - finderEdges x₀ u 0) = 3 ∧
    (finderEdges x₀ u 2 - finderEdges x₀ u 1) / (finderEdges x₀ u 1 - finderEdges x₀ u 0) = 1 ∧
    (finderEdges x₀ u 4 - finderEdges x₀ u 3) / (finderEdges x₀ u 1 - finderEdges x₀ u 0) = 1 ∧
    (finderEdges x₀ u 5 - finderEdges x₀ u 4) / (finderEdges x₀ u 1 - finderEdges x₀ u 0) = 1 := by
  simp [finderEdges]; refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The finder pattern's outer-edge/centre-edge cross-ratio, edges at `0,2,5,7` (outer edges of
the dark ring and of the centre square), is `25/21`. -/
theorem finder_crossRatio (x₀ u : ℝ) (hu : u ≠ 0) :
    crossRatio (finderEdges x₀ u 0) (finderEdges x₀ u 2) (finderEdges x₀ u 3)
      (finderEdges x₀ u 5) = 25 / 21 := by
  simp [finderEdges, crossRatio]; field_simp; ring

/-- **Perspective-invariant finder test.** Under any non-degenerate 1D projective map defined
at the four edges, the imaged edges still have cross-ratio `25/21`. -/
theorem finder_crossRatio_mobius (x₀ u p q r s : ℝ) (hu : u ≠ 0) (hdet : p * s - q * r ≠ 0)
    (h : ∀ i, r * finderEdges x₀ u i + s ≠ 0) :
    crossRatio (mobius p q r s (finderEdges x₀ u 0)) (mobius p q r s (finderEdges x₀ u 2))
      (mobius p q r s (finderEdges x₀ u 3)) (mobius p q r s (finderEdges x₀ u 5)) = 25 / 21 := by
  rw [crossRatio_mobius p q r s _ _ _ _ hdet (h 0) (h 2) (h 3) (h 5), finder_crossRatio x₀ u hu]

/-- **Simple ratios are not perspective invariant.** For `f x = x/(x+1)`, the equal segments
`[0,1]`, `[1,2]` (ratio `1`) image to segments with ratio `3`. -/
theorem ratio_not_projective_invariant :
    (mobius 1 0 1 1 1 - mobius 1 0 1 1 0) / (mobius 1 0 1 1 2 - mobius 1 0 1 1 1) = 3 := by
  simp [mobius]; norm_num

/-! ## 5. Four-point homography (perspective rectification) -/

section Homography
open Matrix

/-- Standard projective frame `e₁, e₂, e₃, (1,1,1)` in homogeneous coordinates. -/
def stdFrame : Fin 4 → (Fin 3 → ℝ) := ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, fun _ => 1]

/-- Four points of the projective plane (homogeneous coordinates) are in *general position*
(no three collinear) iff every three of them are linearly independent in `ℝ³`. -/
def GeneralPosition (p : Fin 4 → (Fin 3 → ℝ)) : Prop :=
  ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℝ ![p i, p j, p k]

/-- The matrix whose columns are the first three points. -/
def basisMat (p : Fin 4 → (Fin 3 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun r c => p c.castSucc r

lemma basisMat_col (p : Fin 4 → (Fin 3 → ℝ)) (c : Fin 3) : (basisMat p).col c = p c.castSucc := by
  ext r; rfl

lemma isUnit_basisMat {p : Fin 4 → (Fin 3 → ℝ)} (hp : GeneralPosition p) : IsUnit (basisMat p) := by
  rw [← linearIndependent_cols_iff_isUnit]
  have := hp 0 1 2 (by decide) (by decide) (by decide)
  have e : (basisMat p).col = ![p 0, p 1, p 2] := by
    ext c r; fin_cases c <;> rfl
  rw [e]; exact this

lemma basisMat_mulVec (p : Fin 4 → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) :
    basisMat p *ᵥ v = v 0 • p 0 + v 1 • p 1 + v 2 • p 2 := by
  ext r; simp [basisMat, mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- In general position, the coordinates of `p 3` in the basis `p 0, p 1, p 2` are all
non-zero. -/
lemma coeffs_ne_zero {p : Fin 4 → (Fin 3 → ℝ)} (hp : GeneralPosition p) {l : Fin 3 → ℝ}
    (hl : l 0 • p 0 + l 1 • p 1 + l 2 • p 2 = p 3) (i : Fin 3) : l i ≠ 0 := by
  intro h0
  fin_cases i
  · have := Fintype.linearIndependent_iff.1 (hp 1 2 3 (by decide) (by decide) (by decide))
      ![l 1, l 2, -1] (by simp [Fin.sum_univ_three]; simp at h0; rw [← hl, h0]; simp)
    simpa using this 2
  · have := Fintype.linearIndependent_iff.1 (hp 0 2 3 (by decide) (by decide) (by decide))
      ![l 0, l 2, -1] (by simp [Fin.sum_univ_three]; simp at h0; rw [← hl, h0]; simp)
    simpa using this 2
  · have := Fintype.linearIndependent_iff.1 (hp 0 1 3 (by decide) (by decide) (by decide))
      ![l 0, l 1, -1] (by simp [Fin.sum_univ_three]; simp at h0; rw [← hl, h0]; simp)
    simpa using this 2

/-- `H` maps each `q i` to `p i` *up to a non-zero scale* (equality of projective points). -/
def MapsFrame (H : Matrix (Fin 3) (Fin 3) ℝ) (q p : Fin 4 → (Fin 3 → ℝ)) : Prop :=
  ∀ i, ∃ c : ℝ, c ≠ 0 ∧ H *ᵥ q i = c • p i

/-- `(1,1,1) = e₁+e₂+e₃`, pushed through any matrix. -/
lemma mulVec_one_eq (H : Matrix (Fin 3) (Fin 3) ℝ) :
    H *ᵥ stdFrame 3 = H *ᵥ stdFrame 0 + H *ᵥ stdFrame 1 + H *ᵥ stdFrame 2 := by
  rw [← mulVec_add, ← mulVec_add]; congr 1
  ext i; fin_cases i <;> simp [stdFrame]

/-- **Existence of the rectifying homography.** For four points in general position (e.g. the
four imaged corners of a QR / Data Matrix symbol) there is an invertible `3×3` matrix mapping
the standard frame `e₁, e₂, e₃, (1,1,1)` to them projectively. -/
theorem exists_homography_std {p : Fin 4 → (Fin 3 → ℝ)} (hp : GeneralPosition p) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℝ, IsUnit H ∧ MapsFrame H stdFrame p := by
  set M := basisMat p
  have hM := isUnit_basisMat hp
  set l := M⁻¹ *ᵥ p 3
  have hMl : M *ᵥ l = p 3 := by
    simp only [l, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM), one_mulVec]
  have hl : l 0 • p 0 + l 1 • p 1 + l 2 • p 2 = p 3 := by rw [← basisMat_mulVec]; exact hMl
  have hl0 := coeffs_ne_zero hp hl
  have hdiag : ∀ v, diagonal l *ᵥ v = fun x => l x * v x := fun v => funext (mulVec_diagonal l v)
  refine ⟨M * diagonal l, ?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_mul, det_diagonal]
    refine ((isUnit_iff_isUnit_det M).1 hM).mul ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]; exact fun i _ => hl0 i
  · intro i
    rw [← mulVec_mulVec, hdiag]
    fin_cases i
    · exact ⟨l 0, hl0 0, by rw [basisMat_mulVec]; simp [stdFrame]⟩
    · exact ⟨l 1, hl0 1, by rw [basisMat_mulVec]; simp [stdFrame]⟩
    · exact ⟨l 2, hl0 2, by rw [basisMat_mulVec]; simp [stdFrame]⟩
    · exact ⟨1, one_ne_zero, by simp [stdFrame]; exact hMl⟩

/-- **Uniqueness up to scale.** Any matrix `H'` sending the standard frame to multiples
(possibly zero) of the points `p` is a scalar multiple of a frame homography `H`. -/
theorem homography_std_unique {p : Fin 4 → (Fin 3 → ℝ)} (hp : GeneralPosition p)
    {H H' : Matrix (Fin 3) (Fin 3) ℝ} (hH : MapsFrame H stdFrame p)
    (hH' : ∀ i, ∃ c : ℝ, H' *ᵥ stdFrame i = c • p i) : ∃ s : ℝ, H' = s • H := by
  choose l hl0 hl using hH
  choose m hm using hH'
  have e1 := mulVec_one_eq H
  have e2 := mulVec_one_eq H'
  rw [hl, hl, hl, hl] at e1
  rw [hm, hm, hm, hm] at e2
  have hli := Fintype.linearIndependent_iff.1 (hp 0 1 2 (by decide) (by decide) (by decide))
    ![m 3 * l 0 - l 3 * m 0, m 3 * l 1 - l 3 * m 1, m 3 * l 2 - l 3 * m 2] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val]
      have : m 3 • (l 3 • p 3) = l 3 • (m 3 • p 3) := by rw [smul_smul, smul_smul, mul_comm]
      rw [e1, e2] at this
      simp only [smul_add, smul_smul, sub_smul] at this ⊢
      rw [← sub_eq_zero] at this
      rw [← this]; abel)
  refine ⟨m 3 / l 3, ext_of_mulVec_single fun i => ?_⟩
  have key : ∀ j : Fin 3, m j.castSucc = m 3 / l 3 * l j.castSucc := by
    intro j
    have := hli j
    fin_cases j <;> simp at this ⊢ <;> field_simp [hl0 3] <;> linarith
  have hs : Pi.single i (1 : ℝ) = stdFrame i.castSucc := by fin_cases i <;> rfl
  rw [smul_mulVec, hs, hm, hl, key, smul_smul]

/-- **Four-point homography theorem.** Between any two four-point configurations in general
position (e.g. ideal symbol corners and imaged corners) there is an invertible homography
`G` mapping one to the other projectively, and every matrix doing so is a scalar multiple of
`G`. This is the theorem behind perspective rectification of 2D symbols from four corners. -/
theorem exists_unique_homography {p q : Fin 4 → (Fin 3 → ℝ)} (hp : GeneralPosition p)
    (hq : GeneralPosition q) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, IsUnit G ∧ MapsFrame G p q ∧
      ∀ G' : Matrix (Fin 3) (Fin 3) ℝ, (∀ i, ∃ c : ℝ, G' *ᵥ p i = c • q i) → ∃ s : ℝ, G' = s • G := by
  obtain ⟨Hp, hHpU, hHp⟩ := exists_homography_std hp
  obtain ⟨Hq, hHqU, hHq⟩ := exists_homography_std hq
  have hdp := (isUnit_iff_isUnit_det Hp).1 hHpU
  have hinv : ∀ i, ∃ c : ℝ, c ≠ 0 ∧ Hp⁻¹ *ᵥ p i = c • stdFrame i := by
    intro i
    obtain ⟨c, hc, h⟩ := hHp i
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    have : p i = c⁻¹ • (Hp *ᵥ stdFrame i) := by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdp, one_mulVec]
  refine ⟨Hq * Hp⁻¹, ?_, ?_, ?_⟩
  · exact hHqU.mul ((isUnit_nonsing_inv_iff).2 hHpU)
  · intro i
    obtain ⟨c, hc, h⟩ := hinv i
    obtain ⟨d, hd, h'⟩ := hHq i
    exact ⟨c * d, mul_ne_zero hc hd, by rw [← mulVec_mulVec, h, mulVec_smul, h', smul_smul]⟩
  · intro G' hG'
    obtain ⟨s, hs⟩ := homography_std_unique hq hHq (H' := G' * Hp) (by
      intro i
      obtain ⟨c, hc, h⟩ := hHp i
      obtain ⟨d, h'⟩ := hG' i
      exact ⟨c * d, by rw [← mulVec_mulVec, h, mulVec_smul, h', smul_smul]⟩)
    refine ⟨s, ?_⟩
    have : G' = G' * Hp * Hp⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hdp, Matrix.mul_one]
    rw [this, hs, Matrix.smul_mul]

end Homography

end RoboLean.Barcode.Geometry
