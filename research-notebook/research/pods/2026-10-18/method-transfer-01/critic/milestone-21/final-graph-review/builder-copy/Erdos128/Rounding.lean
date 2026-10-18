import Erdos128.GraphBasics

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Two-coordinate rounding for fractional halves

This file formalizes the local rounding move used in the simplified proof.
Given two distinct coordinates strictly between zero and one, it transfers
mass between them until one reaches an endpoint.  The move preserves the
total mass, keeps every coordinate in `[0,1]`, and does not increase the
quadratic edge cost from `GraphBasics`.

The key fact is that the edge cost is concave in a transfer direction:
its quadratic coefficient is nonpositive because the two point masses have
zero self-cost and a nonnegative cross-term.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The symmetric contribution attached to one unordered pair. -/
def roundingPairBilin (x y : V → ℚ) : Sym2 V → ℚ :=
  Sym2.lift ⟨fun u v ↦ (x u * y v + x v * y u) / 2, by
    intro u v
    ring⟩

/-- The edge bilinear form used for pair rounding. -/
def roundingEdgeBilin (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℚ) : ℚ :=
  ∑ e ∈ G.edgeFinset, roundingPairBilin x y e

/-- Its associated quadratic edge cost. -/
def roundingEdgeCost (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℚ) : ℚ := roundingEdgeBilin G x x

/-- The public scratch definition agrees with the project's edge cost. -/
theorem roundingEdgeCost_eq_edgeCost
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    roundingEdgeCost G x = edgeCost G x := by
  unfold roundingEdgeCost roundingEdgeBilin edgeCost edgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b => rfl

private lemma roundingPairBilin_add_left (x y z : V → ℚ) (e : Sym2 V) :
    roundingPairBilin (x + y) z e =
      roundingPairBilin x z e + roundingPairBilin y z e := by
  induction e using Sym2.inductionOn with
  | _ a b => simp [roundingPairBilin]; ring

private lemma roundingPairBilin_add_right (x y z : V → ℚ) (e : Sym2 V) :
    roundingPairBilin x (y + z) e =
      roundingPairBilin x y e + roundingPairBilin x z e := by
  induction e using Sym2.inductionOn with
  | _ a b => simp [roundingPairBilin]; ring

private lemma roundingPairBilin_smul_left (a : ℚ) (x y : V → ℚ) (e : Sym2 V) :
    roundingPairBilin (a • x) y e = a * roundingPairBilin x y e := by
  induction e using Sym2.inductionOn with
  | _ p q => simp [roundingPairBilin]; ring

private lemma roundingPairBilin_smul_right (a : ℚ) (x y : V → ℚ) (e : Sym2 V) :
    roundingPairBilin x (a • y) e = a * roundingPairBilin x y e := by
  induction e using Sym2.inductionOn with
  | _ p q => simp [roundingPairBilin]; ring

lemma edgeBilin_add_left' (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℚ) :
    roundingEdgeBilin G (x + y) z =
      roundingEdgeBilin G x z + roundingEdgeBilin G y z := by
  unfold roundingEdgeBilin
  simp_rw [roundingPairBilin_add_left]
  exact Finset.sum_add_distrib

lemma edgeBilin_add_right' (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℚ) :
    roundingEdgeBilin G x (y + z) =
      roundingEdgeBilin G x y + roundingEdgeBilin G x z := by
  unfold roundingEdgeBilin
  simp_rw [roundingPairBilin_add_right]
  exact Finset.sum_add_distrib

lemma edgeBilin_smul_left' (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℚ) (x y : V → ℚ) :
    roundingEdgeBilin G (a • x) y = a * roundingEdgeBilin G x y := by
  unfold roundingEdgeBilin
  simp_rw [roundingPairBilin_smul_left, Finset.mul_sum]

lemma edgeBilin_smul_right' (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℚ) (x y : V → ℚ) :
    roundingEdgeBilin G x (a • y) = a * roundingEdgeBilin G x y := by
  unfold roundingEdgeBilin
  simp_rw [roundingPairBilin_smul_right, Finset.mul_sum]

lemma edgeBilin_symm' (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℚ) :
    roundingEdgeBilin G x y = roundingEdgeBilin G y x := by
  unfold roundingEdgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [roundingPairBilin, Sym2.lift_mk]
      ring

lemma edgeCost_add_smul (G : SimpleGraph V) [DecidableRel G.Adj]
    (x d : V → ℚ) (t : ℚ) :
    roundingEdgeCost G (x + t • d) = roundingEdgeCost G x +
      2 * t * roundingEdgeBilin G x d + t ^ 2 * roundingEdgeCost G d := by
  rw [roundingEdgeCost, edgeBilin_add_left', edgeBilin_add_right',
    edgeBilin_smul_right']
  rw [edgeBilin_smul_left', edgeBilin_add_right' G d x (t • d),
    edgeBilin_smul_right', edgeBilin_symm' G d x]
  unfold roundingEdgeCost
  ring

/-- Point mass at `u`. -/
def ratDelta (u : V) : V → ℚ := fun w ↦ if w = u then 1 else 0

lemma ratDelta_eq_indicator (u : V) :
    ratDelta u = finsetIndicator {u} := by
  funext w
  simp [ratDelta, finsetIndicator, eq_comm]

lemma roundingEdgeCost_ratDelta (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    roundingEdgeCost G (ratDelta u) = 0 := by
  unfold roundingEdgeCost roundingEdgeBilin
  apply Finset.sum_eq_zero
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hadj : G.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset] using he
      have hab : a ≠ b := hadj.ne
      simp [roundingPairBilin, ratDelta]
      by_cases hau : a = u <;> by_cases hbu : b = u <;> simp_all

/-- The direction transferring mass from `v` to `u`. -/
def pairDirection (u v : V) : V → ℚ := ratDelta u - ratDelta v

lemma edgeCost_pairDirection_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    roundingEdgeCost G (pairDirection u v) ≤ 0 := by
  rw [pairDirection, sub_eq_add_neg]
  have hneg : -(ratDelta v) = (-1 : ℚ) • ratDelta v := by
    ext w
    simp
  rw [hneg]
  rw [edgeCost_add_smul, roundingEdgeCost_ratDelta, roundingEdgeCost_ratDelta]
  have hnonneg : 0 ≤ roundingEdgeBilin G (ratDelta u) (ratDelta v) := by
    unfold roundingEdgeBilin
    apply Finset.sum_nonneg
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        simp only [roundingPairBilin, Sym2.lift_mk, ratDelta]
        positivity
  linarith

lemma pairDirection_at_left {u v : V} (huv : u ≠ v) :
    pairDirection u v u = 1 := by
  simp [pairDirection, ratDelta, huv, Ne.symm huv]

lemma pairDirection_at_right {u v : V} (huv : u ≠ v) :
    pairDirection u v v = -1 := by
  simp [pairDirection, ratDelta, huv, Ne.symm huv]

lemma pairDirection_at_other {u v w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    pairDirection u v w = 0 := by
  simp [pairDirection, ratDelta, hwu, hwv, Ne.symm hwu, Ne.symm hwv]

lemma sum_pairDirection (u v : V) :
    ∑ w, pairDirection u v w = 0 := by
  simp [pairDirection, ratDelta, Finset.sum_sub_distrib]

lemma sum_add_pairDirection (x : V → ℚ) (t : ℚ) (u v : V) :
    ∑ w, (x + t • pairDirection u v) w = ∑ w, x w := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, sum_pairDirection, mul_zero, add_zero]

/-- A rational coordinate is integral precisely when it is zero or one. -/
def IsZeroOrOne (a : ℚ) : Prop := a = 0 ∨ a = 1

/--
Pair-rounding step.  If `u` and `v` are two distinct strictly fractional
coordinates, one can push mass between them until one becomes integral,
without changing the total mass or increasing the graph edge cost.
-/
theorem exists_pair_rounding
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℚ) {u v : V} (huv : u ≠ v)
    (hx : ∀ w, 0 ≤ x w ∧ x w ≤ 1)
    (hu : 0 < x u ∧ x u < 1) (hv : 0 < x v ∧ x v < 1) :
    ∃ y : V → ℚ,
      (∀ w, 0 ≤ y w ∧ y w ≤ 1) ∧
      (∑ w, y w) = ∑ w, x w ∧
      edgeCost G y ≤ edgeCost G x ∧
      (IsZeroOrOne (y u) ∨ IsZeroOrOne (y v)) ∧
      (∀ w, w ≠ u → w ≠ v → y w = x w) := by
  let d := pairDirection u v
  let p := min (1 - x u) (x v)
  let q := min (x u) (1 - x v)
  let xp := x + p • d
  let xm := x + (-q) • d
  have hp0 : 0 < p := by
    dsimp [p]
    exact lt_min (sub_pos.mpr hu.2) hv.1
  have hq0 : 0 < q := by
    dsimp [q]
    exact lt_min hu.1 (sub_pos.mpr hv.2)
  have hpleft : p ≤ 1 - x u := by exact min_le_left _ _
  have hpright : p ≤ x v := by exact min_le_right _ _
  have hqleft : q ≤ x u := by exact min_le_left _ _
  have hqright : q ≤ 1 - x v := by exact min_le_right _ _
  have hxp_bounds : ∀ w, 0 ≤ xp w ∧ xp w ≤ 1 := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [xp, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_left huv]
      constructor <;> linarith [hx u |>.1]
    · by_cases hwv : w = v
      · subst w
        simp only [xp, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          pairDirection_at_right huv]
        constructor <;> linarith [hx v |>.2]
      · rw [show xp w = x w by
            simp [xp, d, pairDirection_at_other hwu hwv]]
        exact hx w
  have hxm_bounds : ∀ w, 0 ≤ xm w ∧ xm w ≤ 1 := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [xm, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_left huv]
      constructor <;> linarith [hx u |>.2]
    · by_cases hwv : w = v
      · subst w
        simp only [xm, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          pairDirection_at_right huv]
        constructor <;> linarith [hx v |>.1]
      · rw [show xm w = x w by
            simp [xm, d, pairDirection_at_other hwu hwv]]
        exact hx w
  have hxp_sum : (∑ w, xp w) = ∑ w, x w := by
    exact sum_add_pairDirection x p u v
  have hxm_sum : (∑ w, xm w) = ∑ w, x w := by
    exact sum_add_pairDirection x (-q) u v
  have hxp_integral : IsZeroOrOne (xp u) ∨ IsZeroOrOne (xp v) := by
    by_cases hmin : 1 - x u ≤ x v
    · left
      right
      simp only [xp, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_left huv]
      rw [show p = 1 - x u by exact min_eq_left hmin]
      ring
    · right
      left
      simp only [xp, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_right huv]
      rw [show p = x v by exact min_eq_right (le_of_not_ge hmin)]
      ring
  have hxm_integral : IsZeroOrOne (xm u) ∨ IsZeroOrOne (xm v) := by
    by_cases hmin : x u ≤ 1 - x v
    · left
      left
      simp only [xm, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_left huv]
      rw [show q = x u by exact min_eq_left hmin]
      ring
    · right
      right
      simp only [xm, d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        pairDirection_at_right huv]
      rw [show q = 1 - x v by exact min_eq_right (le_of_not_ge hmin)]
      ring
  have hxp_other : ∀ w, w ≠ u → w ≠ v → xp w = x w := by
    intro w hwu hwv
    simp [xp, d, pairDirection_at_other hwu hwv]
  have hxm_other : ∀ w, w ≠ u → w ≠ v → xm w = x w := by
    intro w hwu hwv
    simp [xm, d, pairDirection_at_other hwu hwv]
  have hd_nonpos : roundingEdgeCost G d ≤ 0 := by
    exact edgeCost_pairDirection_nonpos G u v
  by_cases hlin : roundingEdgeBilin G x d ≤ 0
  · refine ⟨xp, hxp_bounds, hxp_sum, ?_, hxp_integral, hxp_other⟩
    rw [← roundingEdgeCost_eq_edgeCost G xp,
      ← roundingEdgeCost_eq_edgeCost G x]
    rw [show xp = x + p • d by rfl, edgeCost_add_smul]
    nlinarith [le_of_lt hp0]
  · refine ⟨xm, hxm_bounds, hxm_sum, ?_, hxm_integral, hxm_other⟩
    rw [← roundingEdgeCost_eq_edgeCost G xm,
      ← roundingEdgeCost_eq_edgeCost G x]
    rw [show xm = x + (-q) • d by rfl, edgeCost_add_smul]
    have hlin' : 0 < roundingEdgeBilin G x d := lt_of_not_ge hlin
    nlinarith [le_of_lt hq0]

end

end Erdos128
