import Mathlib

/-! Neural-network activations as Lur'e sector / slope-restricted nonlinearities. -/

namespace ClassicsFalse

open Real

/-- `φ` lies in the sector `[k₁, k₂]`: `k₁ y² ≤ φ(y) y ≤ k₂ y²`. -/
def InSector (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y, k₁ * y ^ 2 ≤ φ y * y ∧ φ y * y ≤ k₂ * y ^ 2

/-- `φ` is slope-restricted to `[k₁, k₂]` (the Kalman-conjecture class). -/
def SlopeRestricted (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x y, k₁ * (x - y) ^ 2 ≤ (φ x - φ y) * (x - y) ∧ (φ x - φ y) * (x - y) ≤ k₂ * (x - y) ^ 2

theorem SlopeRestricted.inSector {k₁ k₂ : ℝ} {φ : ℝ → ℝ} (h : SlopeRestricted k₁ k₂ φ)
    (h0 : φ 0 = 0) : InSector k₁ k₂ φ := by
  intro y; simpa [h0] using h y 0

def relu (y : ℝ) : ℝ := max y 0

theorem relu_sector : InSector 0 1 relu := by
  intro y; unfold relu
  rcases le_total y 0 with h | h
  · rw [max_eq_right h]; constructor <;> nlinarith
  · rw [max_eq_left h]; constructor <;> nlinarith

theorem relu_slope : SlopeRestricted 0 1 relu := by
  intro x y; unfold relu
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;>
    simp only [max_eq_right, max_eq_left, hx, hy] <;> constructor <;> nlinarith

/-- Leaky ReLU with slope `α ∈ [0,1]` on the negative axis lies in `[α, 1]`. -/
def leakyRelu (α y : ℝ) : ℝ := max y (α * y)

theorem leakyRelu_sector {α : ℝ} (_h0 : 0 ≤ α) (h1 : α ≤ 1) : InSector α 1 (leakyRelu α) := by
  intro y; unfold leakyRelu
  rcases le_total y 0 with h | h
  · rw [max_eq_right (by nlinarith)]; constructor <;> nlinarith
  · rw [max_eq_left (by nlinarith)]; constructor <;> nlinarith

/-- `sinh x ≤ x cosh x` for `x ≥ 0`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : sinh x ≤ x * cosh x := by
  let f : ℝ → ℝ := fun t => t * cosh t - sinh t
  have hd : ∀ t, HasDerivAt f (t * sinh t) t := by
    intro t
    have := ((hasDerivAt_id t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)
    have h2 : HasDerivAt f (1 * cosh t + id t * sinh t - cosh t) t := this
    exact h2.congr_deriv (by simp only [id_eq]; ring)
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      exact mul_nonneg (le_of_lt ht) (sinh_nonneg_iff.mpr (le_of_lt ht))
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp [f] at this; linarith

theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  rw [tanh_eq_sinh_div_cosh, div_le_iff₀ (cosh_pos x)]
  exact sinh_le_mul_cosh hx

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]; exact div_nonneg (sinh_nonneg_iff.mpr hx) (cosh_pos x).le

/-- **tanh is a Lur'e sector-[0,1] nonlinearity.** -/
theorem tanh_sector : InSector 0 1 tanh := by
  intro y
  rcases le_total 0 y with h | h
  · have a := tanh_le_self h; have b := tanh_nonneg h
    constructor <;> nlinarith
  · have a := tanh_le_self (neg_nonneg.mpr h); have b := tanh_nonneg (neg_nonneg.mpr h)
    rw [tanh_neg] at a b
    constructor <;> nlinarith

/-- Hard saturation `clamp(y, -U, U)` lies in sector `[0,1]` (any `U ≥ 0`). -/
theorem sat_sector {U : ℝ} (hU : 0 ≤ U) : InSector 0 1 (fun y => max (-U) (min y U)) := by
  intro y; dsimp only
  rcases le_total y U with h1 | h1 <;> rcases le_total (-U) y with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2]; constructor <;> nlinarith
  · rw [min_eq_left h1, max_eq_left h2]; constructor <;> nlinarith
  · rw [min_eq_right h1, max_eq_right (by linarith)]; constructor <;> nlinarith
  · have : y = 0 := by linarith
    have : U = 0 := by linarith
    subst_vars; simp

/-- Sector membership is preserved by positive scaling and convex combination,
so a single hidden layer `∑ wᵢ σ(y)` with `wᵢ ≥ 0` stays in `[0, ∑ wᵢ]`. -/
theorem InSector.add {a₁ b₁ a₂ b₂ : ℝ} {φ ψ : ℝ → ℝ} (h : InSector a₁ b₁ φ)
    (g : InSector a₂ b₂ ψ) : InSector (a₁ + a₂) (b₁ + b₂) (fun y => φ y + ψ y) := by
  intro y; have := h y; have := g y; constructor <;> nlinarith

theorem InSector.smul {a b w : ℝ} {φ : ℝ → ℝ} (hw : 0 ≤ w) (h : InSector a b φ) :
    InSector (w * a) (w * b) (fun y => w * φ y) := by
  intro y; have := h y; constructor <;> nlinarith [mul_le_mul_of_nonneg_left (h y).1 hw,
    mul_le_mul_of_nonneg_left (h y).2 hw]

/-- Sector nonlinearity ⇒ pointwise linear gain in `[k₁,k₂]`. This is the bridge
from "sector" to "some linear system": the Aizerman intuition. -/
theorem InSector.exists_gain {k₁ k₂ : ℝ} {φ : ℝ → ℝ} (h : InSector k₁ k₂ φ) {y : ℝ}
    (hy : y ≠ 0) : ∃ k, k₁ ≤ k ∧ k ≤ k₂ ∧ φ y = k * y := by
  have h1 := (h y).1; have h2 := (h y).2
  refine ⟨φ y / y, ?_, ?_, by field_simp⟩
  · rcases lt_or_gt_of_ne hy with hn | hp
    · rw [le_div_iff_of_neg hn]; nlinarith
    · rw [le_div_iff₀ hp]; nlinarith
  · rcases lt_or_gt_of_ne hy with hn | hp
    · rw [div_le_iff_of_neg hn]; nlinarith
    · rw [div_le_iff₀ hp]; nlinarith

end ClassicsFalse

#print axioms ClassicsFalse.tanh_sector
#print axioms ClassicsFalse.relu_slope
