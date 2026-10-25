import ControlsLean.Vision.EightPoint

/-!
# Five-point relative pose (Kruppa 1913; Demazure 1988; Nistér 2004)

E. Kruppa, "Zur Ermittlung eines Objektes aus zwei Perspektiven mit innerer Orientierung",
Sitz.-Ber. Akad. Wiss., Wien, Math.-Naturw. Kl., Abt. IIa 122 (1913), 1939–1948.
(Kruppa: ≤ 11 solutions; Demazure 1988 / Faugeras–Maybank 1990: exactly 10 complex.)
The cubic "trace constraint" `2 E Eᵀ E - tr(E Eᵀ) E = 0` is from Demazure (1988) and is the
workhorse of Nistér's 2004 five-point solver (used in every modern VO/SLAM front end).

* `essential_mul_transpose`: `E Eᵀ = [t]ₓ [t]ₓᵀ` whenever `R Rᵀ = 1`.
* `essential_cubic`: the nine cubic constraints hold for `E = [t]ₓ R` with `R` orthogonal.
* `FivePointSolutions`: the problem statement (5 linear + 1 det + 9 cubic equations);
  the true essential matrix and all its scalar multiples lie in it.
-/

open Matrix

namespace ControlsLean.Vision.FivePoint

variable {K : Type*} [Field K]

theorem skew_mul_transpose_mul_skew (t : Fin 3 → K) :
    skew t * (skew t)ᵀ * skew t = (t ⬝ᵥ t) • skew t := by
  rw [skew_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

theorem trace_skew_mul_transpose (t : Fin 3 → K) :
    trace (skew t * (skew t)ᵀ) = 2 * (t ⬝ᵥ t) := by
  rw [skew_transpose]
  simp [skew, trace, Fin.sum_univ_three, dotProduct]; ring

theorem essential_mul_transpose (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    (hR : R * Rᵀ = 1) : essential R t * (essential R t)ᵀ = skew t * (skew t)ᵀ := by
  rw [essential, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul]

/-- **Demazure's cubic constraints** (nine scalar cubics in the entries of `E`). -/
def cubic (E : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (2 : K) • (E * Eᵀ * E) - trace (E * Eᵀ) • E

/-- Every true essential matrix `[t]ₓ R` (with `R` orthogonal) satisfies the nine cubics. -/
theorem essential_cubic (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) (hR : R * Rᵀ = 1) :
    cubic (essential R t) = 0 := by
  rw [cubic, essential_mul_transpose R t hR, trace_skew_mul_transpose]
  conv_lhs => rw [essential, ← Matrix.mul_assoc, skew_mul_transpose_mul_skew]
  rw [smul_mul, ← essential, smul_smul, sub_self]

theorem cubic_smul (c : K) (E : Matrix (Fin 3) (Fin 3) K) : cubic (c • E) = c ^ 3 • cubic E := by
  simp only [cubic, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul]
  module

/-- **The five-point problem.** Solutions are the `E` satisfying the epipolar constraint of
each of the `5` correspondences, `det E = 0`, and the nine cubic constraints. -/
def FivePointSolutions (x₁ x₂ : Fin 5 → Fin 3 → K) : Set (Matrix (Fin 3) (Fin 3) K) :=
  {E | (∀ i, x₂ i ⬝ᵥ (E *ᵥ x₁ i) = 0) ∧ E.det = 0 ∧ cubic E = 0}

/-- The true essential matrix (and its whole projective class) solves the five-point system. -/
theorem smul_essential_mem (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) (hR : R * Rᵀ = 1)
    {x₁ x₂ : Fin 5 → Fin 3 → K} {d₁ d₂ : Fin 5 → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t) (c : K) :
    c • essential R t ∈ FivePointSolutions x₁ x₂ := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [smul_mulVec, dotProduct_smul, essential_satisfies_constraints R t hd₂ hscene i,
      smul_zero]
  · rw [det_smul, det_essential, mul_zero]
  · rw [cubic_smul, essential_cubic R t hR, smul_zero]

end ControlsLean.Vision.FivePoint
