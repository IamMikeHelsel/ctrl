import Mathlib

/-! Labelled statements (NOT proved here; `sorry` marks known literature results). -/

namespace ClassicsFalse

open Matrix Filter

def InSector (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y, k₁ * y ^ 2 ≤ φ y * y ∧ φ y * y ≤ k₂ * y ^ 2

def SlopeRestricted (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x y, k₁ * (x - y) ^ 2 ≤ (φ x - φ y) * (x - y) ∧ (φ x - φ y) * (x - y) ≤ k₂ * (x - y) ^ 2

/-- Global attractivity of the Lur'e loop `ẋ = A x + b φ(cᵀx)`. -/
def LureGAS {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ → (Fin n → ℝ), (∀ t, HasDerivAt x (A *ᵥ x t + φ (c ⬝ᵥ x t) • b) t) →
    Tendsto x atTop (nhds 0)

/-- Every linear gain in `[k₁,k₂]` is GAS (i.e. Hurwitz). -/
def HurwitzSector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (k₁ k₂ : ℝ) : Prop :=
  ∀ k ∈ Set.Icc k₁ k₂, LureGAS A b c (fun y => k * y)

/-- Aizerman property in dimension `n` (Aizerman 1949). -/
def AizermanHolds (n : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℝ) b c k₁ k₂ (φ : ℝ → ℝ),
    HurwitzSector A b c k₁ k₂ → Continuous φ → InSector k₁ k₂ φ → LureGAS A b c φ

/-- Kalman property (Kalman 1957): slope restriction instead of sector. -/
def KalmanHolds (n : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℝ) b c k₁ k₂ (φ : ℝ → ℝ),
    HurwitzSector A b c k₁ k₂ → SlopeRestricted k₁ k₂ φ → φ 0 = 0 → LureGAS A b c φ

/-- Known TRUE: Erugin / Malkin / Krasovskii (1950–52) for n = 2 (with the
usual caveats on the boundary of the Hurwitz sector). Not formalized. -/
theorem aizerman_two : AizermanHolds 2 := sorry

/-- Known FALSE: Pliss (1958) third-order counterexample; modern hidden-
oscillation counterexamples: Leonov–Kuznetsov (2011–13). Not formalized. -/
theorem aizerman_three_false : ¬ AizermanHolds 3 := sorry

/-- Known TRUE for n ≤ 3 (Barabanov 1988 for n = 3; Leonov et al.). -/
theorem kalman_three : KalmanHolds 3 := sorry

/-- Known FALSE for n ≥ 4: Fitts (1966) numerical, Barabanov (1988),
rigorous hidden-oscillation examples Leonov–Kuznetsov (2013). -/
theorem kalman_four_false : ¬ KalmanHolds 4 := sorry

end ClassicsFalse
