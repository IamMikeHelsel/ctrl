import Mathlib

/-!
# Denavit–Hartenberg (1955) link transforms

`A = Rot_z(θ) · Trans_z(d) · Trans_x(a) · Rot_x(α)` as a 4×4 homogeneous matrix.

* `dh_eq_hom`: the product equals `hom (Rz θ * Rx α) (a cos θ, a sin θ, d)`.
* `dhRot_mem_SO3`: its rotation block is in `SO(3)`; hence `A ∈ SE(3)` (`dh_mem_SE3`).
* `hom_mul`: homogeneous matrices compose as `SE(3)` (so DH chains stay in `SE(3)`).
* `exists_dh_of_SO3` (**the "4 parameters suffice" lemma**, Spong–Hutchinson–Vidyasagar
  Lemma 3.1, rotation part): any `R ∈ SO(3)` with `R₂₀ = 0` (DH1: `x₁ ⊥ z₀`) is
  `Rz θ * Rx α` for some `θ, α`.
-/

namespace Classics.DH

open Matrix Real

noncomputable def Rz (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1]

noncomputable def Rx (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, cos α, -sin α; 0, sin α, cos α]

/-- Homogeneous 4×4 matrix of a rigid transform `(R, p)`. -/
def hom (R : Matrix (Fin 3) (Fin 3) ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![R 0 0, R 0 1, R 0 2, p 0;
     R 1 0, R 1 1, R 1 2, p 1;
     R 2 0, R 2 1, R 2 2, p 2;
     0, 0, 0, 1]

/-- `SE(3)` as homogeneous matrices. -/
def SE3 : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {T | ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ p, T = hom R p}

noncomputable def rotZ4 (θ : ℝ) := hom (Rz θ) 0
def transZ4 (d : ℝ) := hom 1 ![0, 0, d]
def transX4 (a : ℝ) := hom 1 ![a, 0, 0]
noncomputable def rotX4 (α : ℝ) := hom (Rx α) 0

/-- The DH link transform. -/
noncomputable def dh (θ d a α : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  rotZ4 θ * transZ4 d * transX4 a * rotX4 α

theorem hom_mul (R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ) (p₁ p₂ : Fin 3 → ℝ) :
    hom R₁ p₁ * hom R₂ p₂ = hom (R₁ * R₂) (R₁ *ᵥ p₂ + p₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hom, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.mulVec,
      dotProduct]

theorem dh_eq_hom (θ d a α : ℝ) :
    dh θ d a α = hom (Rz θ * Rx α) ![a * cos θ, a * sin θ, d] := by
  simp only [dh, rotZ4, transZ4, transX4, rotX4, hom_mul]
  congr 1
  · simp
  · ext i; fin_cases i <;> simp [Rz]

theorem Rz_mem_SO3 (θ : ℝ) : Rz θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Rz, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sin_sq_add_cos_sq θ]
  · simp [Rz, Matrix.det_fin_three]; nlinarith [sin_sq_add_cos_sq θ]

theorem Rx_mem_SO3 (α : ℝ) : Rx α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Rx, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sin_sq_add_cos_sq α]
  · simp [Rx, Matrix.det_fin_three]; nlinarith [sin_sq_add_cos_sq α]

theorem dhRot_mem_SO3 (θ α : ℝ) : Rz θ * Rx α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  mul_mem (Rz_mem_SO3 θ) (Rx_mem_SO3 α)

/-- **Every DH link transform is in `SE(3)`.** -/
theorem dh_mem_SE3 (θ d a α : ℝ) : dh θ d a α ∈ SE3 :=
  ⟨_, dhRot_mem_SO3 θ α, _, dh_eq_hom θ d a α⟩

/-- `SE(3)` is closed under products, so a DH chain `A₁ A₂ ⋯ Aₙ` lies in `SE(3)`. -/
theorem SE3_mul {T₁ T₂} (h₁ : T₁ ∈ SE3) (h₂ : T₂ ∈ SE3) : T₁ * T₂ ∈ SE3 := by
  obtain ⟨R₁, hR₁, p₁, rfl⟩ := h₁
  obtain ⟨R₂, hR₂, p₂, rfl⟩ := h₂
  exact ⟨_, mul_mem hR₁ hR₂, _, hom_mul _ _ _ _⟩

theorem dh_chain_mem_SE3 (l : List (ℝ × ℝ × ℝ × ℝ)) :
    (l.map fun q => dh q.1 q.2.1 q.2.2.1 q.2.2.2).prod ∈ SE3 := by
  induction l with
  | nil => exact ⟨1, one_mem _, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [hom]⟩
  | cons q l ih => simpa using SE3_mul (dh_mem_SE3 _ _ _ _) ih

lemma exists_angle {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) : ∃ θ, cos θ = x ∧ sin θ = y := by
  set z : ℂ := ⟨x, y⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [z]; nlinarith
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg (by intro h0; simp [h0] at hz), hz, div_one]
  · rw [Complex.sin_arg, hz, div_one]

/-- For `R ∈ SO(3)`, `adjugate R = Rᵀ`, so each entry is its own cofactor. -/
lemma adjugate_eq_transpose {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) : R.adjugate = Rᵀ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff'] at hR
  obtain ⟨horth, hdet⟩ := hR
  have hinv : R⁻¹ = Rᵀ := Matrix.inv_eq_left_inv (by simpa using horth)
  rw [Matrix.inv_def, hdet] at hinv
  simpa using hinv

/-- **Four parameters suffice (rotation part).** If `R ∈ SO(3)` and `R₂₀ = 0`
(the new `x`-axis is perpendicular to the old `z`-axis), then `R = Rz θ * Rx α`. -/
theorem exists_dh_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h20 : R 2 0 = 0) :
    ∃ θ α, R = Rz θ * Rx α := by
  have hadj := adjugate_eq_transpose hR
  obtain ⟨hO, -⟩ := Matrix.mem_specialOrthogonalGroup_iff.1 hR
  have horth : R * Rᵀ = 1 := by simpa using (Matrix.mem_orthogonalGroup_iff _ _).1 hO
  have hcol := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff' _ _).1 hO) 0) 0
  have hrow := congrFun (congrFun horth 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20] at hcol hrow
  obtain ⟨θ, hc, hs⟩ := exists_angle (x := R 0 0) (y := R 1 0) (by nlinarith)
  obtain ⟨α, hca, hsa⟩ := exists_angle (x := R 2 2) (y := R 2 1) (by nlinarith)
  refine ⟨θ, α, ?_⟩
  have e : ∀ i j, R i j = R.adjugate j i := fun i j => by rw [hadj]; rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Rx, Matrix.mul_apply, Fin.sum_univ_three, hc, hs, hca, hsa, h20] <;>
    first
    | rfl
    | (rw [e]; simp [Matrix.adjugate_fin_three, h20])

end Classics.DH
