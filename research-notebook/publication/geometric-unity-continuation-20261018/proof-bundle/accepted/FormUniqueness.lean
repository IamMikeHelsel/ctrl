import RealAdjoint
import Mathlib.Data.Matrix.Basis

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- Compatibility with every vector, without assuming symmetry or nondegeneracy. -/
def VectorCompatible (H : SpinMatrix) : Prop :=
  ∀ v : V, (splitMatrix (CliffordAlgebra.ι Q v)).transpose * H =
    -(H * splitMatrix (CliffordAlgebra.ι Q v))

theorem compatible_intertwines (H : SpinMatrix) (h : VectorCompatible H) (x : Cl) :
    (splitMatrix x).transpose * H = H * splitMatrix (star x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    simpa only [CliffordAlgebra.star_ι, map_neg, mul_neg] using h v
  | mul a b ha hb =>
    simp only [map_mul, Matrix.transpose_mul, star_mul]
    calc
      ((splitMatrix b).transpose * (splitMatrix a).transpose) * H =
          (splitMatrix b).transpose * (H * splitMatrix (star a)) := by rw [mul_assoc, ha]
      _ = H * (splitMatrix (star b) * splitMatrix (star a)) := by rw [← mul_assoc, hb, mul_assoc]
  | add a b ha hb =>
    simp only [map_add, Matrix.transpose_add, add_mul, star_add, mul_add, ha, hb]

theorem compatible_centralizer (H : SpinMatrix) (h : VectorCompatible H) (A : SpinMatrix) :
    A * (H*K) = (H*K) * A := by
  obtain ⟨x, hx⟩ := splitMatrix_surjective A.transpose
  have hi := compatible_intertwines H h x
  rw [splitMatrix_star, realAdjoint_apply, hx, Matrix.transpose_transpose] at hi
  have hh := congrArg (fun M : SpinMatrix => M * K) hi
  simpa only [mul_assoc, K_square, mul_one] using hh

theorem vectorCompatible_scalar (H : SpinMatrix) (h : VectorCompatible H) :
    ∃ c : ℝ, H = c • K := by
  have hc : H*K ∈ Set.range (Matrix.scalar (Finset (Fin 7))) :=
    Matrix.mem_range_scalar_of_commute_single (fun i j _ =>
      compatible_centralizer H h (Matrix.single i j 1))
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  have hh := congrArg (fun M : SpinMatrix => M*K) hc
  have hs : Matrix.scalar (Finset (Fin 7)) c = c • (1 : SpinMatrix) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  rw [hs] at hh
  simpa [mul_assoc, K_square] using hh.symm

theorem scalar_vectorCompatible (c : ℝ) : VectorCompatible (c • K) := by
  intro v
  have h := realAdjoint_vector v
  rw [realAdjoint_apply] at h
  have hh := congrArg (fun M : SpinMatrix => K * M) h
  have hk : (splitMatrix (CliffordAlgebra.ι Q v)).transpose * K =
      -(K * splitMatrix (CliffordAlgebra.ι Q v)) := by
    simpa only [← mul_assoc, K_square, one_mul, mul_neg] using hh
  simpa only [Matrix.mul_smul, Matrix.smul_mul, ← smul_neg] using congrArg (fun M : SpinMatrix => c • M) hk

theorem vectorCompatible_iff (H : SpinMatrix) :
    VectorCompatible H ↔ ∃ c : ℝ, H = c • K := by
  constructor
  · exact vectorCompatible_scalar H
  · rintro ⟨c, rfl⟩
    exact scalar_vectorCompatible c

/-- Equal normalization at any nonzero entry fixes the remaining scale. -/
theorem normalized_vectorCompatible_unique (H : SpinMatrix) (h : VectorCompatible H)
    (i j : Finset (Fin 7)) (hk : K i j ≠ 0) (hn : H i j = K i j) : H = K := by
  obtain ⟨c, rfl⟩ := vectorCompatible_scalar H h
  have hc : c = 1 := by
    have hentry : c * K i j = 1 * K i j := by simpa using hn
    exact mul_right_cancel₀ hk hentry
  simp [hc]

end HyperbolicSpinor
