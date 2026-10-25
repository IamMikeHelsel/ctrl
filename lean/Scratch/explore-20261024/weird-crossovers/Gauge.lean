import Mathlib

/-! Gauge symmetries / invariances across SLAM, bundle adjustment, plane homographies. -/

open Matrix

namespace WeirdCrossovers

/-! ## 1D SLAM: robot + one landmark, relative measurements, odometry inputs -/

/-- State: (robot position, landmark position). Dynamics: robot moves by input `u k`. -/
def slamStep (u : ℝ) (s : ℝ × ℝ) : ℝ × ℝ := (s.1 + u, s.2)

def slamTraj (u : ℕ → ℝ) (s₀ : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => s₀
  | k + 1 => slamStep (u k) (slamTraj u s₀ k)

/-- Measurement: landmark relative to robot. -/
def slamMeas (s : ℝ × ℝ) : ℝ := s.2 - s.1

theorem slamTraj_shift (u : ℕ → ℝ) (s₀ : ℝ × ℝ) (c : ℝ) (k : ℕ) :
    slamTraj u (s₀.1 + c, s₀.2 + c) k = ((slamTraj u s₀ k).1 + c, (slamTraj u s₀ k).2 + c) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [slamTraj, slamStep, ih]; ext <;> simp; ring

/-- Global translation is unobservable: two distinct initial states give identical outputs
for every input sequence. -/
theorem slam_unobservable :
    ∃ s₀ s₀' : ℝ × ℝ, s₀ ≠ s₀' ∧ ∀ u : ℕ → ℝ, ∀ k,
      slamMeas (slamTraj u s₀ k) = slamMeas (slamTraj u s₀' k) := by
  refine ⟨(0, 0), (1, 1), by simp, fun u k => ?_⟩
  have := slamTraj_shift u (0, 0) 1 k
  simp only [zero_add] at this
  rw [this, slamMeas, slamMeas]; ring

/-- …and that is the *only* ambiguity: equal output sequences force a common translation. -/
theorem slam_ambiguity_is_translation (u : ℕ → ℝ) (s₀ s₀' : ℝ × ℝ)
    (h : slamMeas (slamTraj u s₀ 0) = slamMeas (slamTraj u s₀' 0)) :
    ∃ c, s₀' = (s₀.1 + c, s₀.2 + c) := by
  refine ⟨s₀'.1 - s₀.1, ?_⟩
  simp [slamTraj, slamMeas] at h
  ext <;> simp; linarith

/-! ## Bundle adjustment scale gauge -/

/-- Pinhole projection of camera-frame point (normalized coords; depth `X 2`). -/
noncomputable def proj (X : Fin 3 → ℝ) : Fin 2 → ℝ := ![X 0 / X 2, X 1 / X 2]

/-- Reprojection of world point `P` in a camera with pose `(R, t)`. -/
noncomputable def reproj (R : Matrix (Fin 3) (Fin 3) ℝ) (t P : Fin 3 → ℝ) : Fin 2 → ℝ :=
  proj (R *ᵥ P + t)

/-- Scaling all translations and points by `s ≠ 0` leaves every reprojection invariant
(no positivity needed; `s < 0` additionally flips cheirality). -/
theorem reproj_scale_gauge (R : Matrix (Fin 3) (Fin 3) ℝ) (t P : Fin 3 → ℝ) {s : ℝ}
    (hs : s ≠ 0) : reproj R (s • t) (s • P) = reproj R t P := by
  unfold reproj proj
  rw [mulVec_smul, ← smul_add]
  ext i; fin_cases i <;> simp [mul_div_mul_left _ _ hs]

/-- Rigid gauge: applying a world motion `(Q, c)` to all points and compensating each camera
pose leaves reprojections invariant. -/
theorem reproj_rigid_gauge (R Q Qinv : Matrix (Fin 3) (Fin 3) ℝ) (t c P : Fin 3 → ℝ)
    (hQ : Qinv * Q = 1) :
    reproj (R * Qinv) (t - (R * Qinv) *ᵥ c) (Q *ᵥ P + c) = reproj R t P := by
  unfold reproj
  congr 1
  rw [mulVec_add, mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]
  abel

/-! ## Plane-induced homographies compose exactly (as matrices, not just up to scale) -/

def outer (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => u i * v j

/-- `H = R + t nᵀ / d`. -/
noncomputable def planeH (R : Matrix (Fin 3) (Fin 3) ℝ) (t n : Fin 3 → ℝ) (d : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := R + d⁻¹ • outer t n

/-- If frame 2's plane parameters are the transport of frame 1's (`n₂ᵀ R₁ = nᵀ`,
`d₂ = d + n₂·t₁`), then `H₂₃ H₁₂ = H₁₃` with the composed motion `(R₂R₁, R₂t₁ + t₂)`.
No orthogonality of `R₁` is needed. -/
theorem planeH_comp (R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ) (t₁ t₂ n n₂ : Fin 3 → ℝ) (d d₂ : ℝ)
    (hd : d ≠ 0) (hd₂ : d₂ ≠ 0) (hn : n₂ ᵥ* R₁ = n) (hdd : d₂ = d + n₂ ⬝ᵥ t₁) :
    planeH R₂ t₂ n₂ d₂ * planeH R₁ t₁ n d = planeH (R₂ * R₁) (R₂ *ᵥ t₁ + t₂) n d := by
  have hn' : ∀ j, ∑ k, n₂ k * R₁ k j = n j := fun j => by
    rw [← hn]; simp [vecMul, dotProduct]
  ext i j
  simp only [planeH, outer, add_mul, mul_add, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.of_apply, smul_eq_mul, mulVec, dotProduct, Pi.add_apply,
    Finset.sum_add_distrib]
  have e1 : ∑ k, R₂ i k * (d⁻¹ * (t₁ k * n j)) = d⁻¹ * (∑ k, R₂ i k * t₁ k) * n j := by
    rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, d₂⁻¹ * (t₂ i * n₂ k) * R₁ k j = d₂⁻¹ * t₂ i * n j := by
    rw [← hn' j, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  have e3 : ∑ k, d₂⁻¹ * (t₂ i * n₂ k) * (d⁻¹ * (t₁ k * n j))
      = d₂⁻¹ * d⁻¹ * t₂ i * n j * ∑ k, n₂ k * t₁ k := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, e3]
  have : ∑ k, n₂ k * t₁ k = d₂ - d := by rw [hdd]; simp [dotProduct]
  rw [this]
  field_simp
  ring

/-- Without the transport hypothesis the composition can fail: a counterexample with
`R₁ = R₂ = 1`, `t₁ = t₂ = e₀`, `n = n₂ = e₀`, `d = d₂ = 1` (here `d₂` should be `2`). -/
theorem planeH_comp_fails :
    planeH 1 ![1, 0, 0] ![1, 0, 0] 1 * planeH 1 ![1, 0, 0] ![1, 0, 0] 1 ≠
      planeH (1 * 1) ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![1, 0, 0] + ![1, 0, 0]) ![1, 0, 0] 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [planeH, outer, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at this
  norm_num at this

end WeirdCrossovers
