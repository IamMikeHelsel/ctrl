module

public import LeanControls.Generated.LagLower
public import LeanControls.Generated.LagUpper
public import LeanControls.VertexCertificate
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# An exact held-input actuator-lag model enclosed by polynomial vertices

The normalized plant is x'=v, v'=a, a'=-a+u, with lag time constant tau=1.
It is not a calibrated motor-hardware model. The command u is computed once from
the initial sample state and held constant. Its exact trajectory contains
exp(-t). The polynomial vertices are enclosing models, not the actual plant.
All claims here concern nominal exact-real dynamics.
-/

@[expose] public section
noncomputable section
namespace LeanControls.ActuatorLag
open Matrix BernsteinCertificate

abbrev State := Fin 3 → ℝ

/-- State order is position, velocity, acceleration; the command is held. -/
def input (z : State) : ℝ := -z 0 - 3 * z 1 - 2 * z 2

def acceleration (t : ℝ) (z : State) : ℝ :=
  input z + (z 2 - input z) * Real.exp (-t)

def velocity (t : ℝ) (z : State) : ℝ :=
  z 1 + input z * t + (z 2 - input z) * (1 - Real.exp (-t))

def position (t : ℝ) (z : State) : ℝ :=
  z 0 + t * z 1 + input z * t ^ 2 / 2 +
    (z 2 - input z) * (t - 1 + Real.exp (-t))

def segment (t : ℝ) (z : State) : State :=
  ![position t z, velocity t z, acceleration t z]

def vectorField (u : ℝ) (current : State) : State :=
  ![current 1, current 2, -current 2 + u]

theorem segment_initial (z : State) : segment 0 z = z := by
  ext i
  fin_cases i <;> simp [segment, position, velocity, acceleration]

theorem exp_neg_derivative (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  simpa using ((hasDerivAt_id t).neg).exp

theorem acceleration_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => acceleration s z) (-acceleration t z + input z) t := by
  convert ((exp_neg_derivative t).const_mul (z 2 - input z)).const_add (input z) using 1
  · rfl
  · dsimp [acceleration]
    ring

theorem velocity_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => velocity s z) (acceleration t z) t := by
  convert (((hasDerivAt_id t).const_mul (input z)).const_add (z 1)).add
    (((exp_neg_derivative t).const_sub 1).const_mul (z 2 - input z)) using 1
  · rfl
  · dsimp [acceleration]
    ring

theorem position_derivative (t : ℝ) (z : State) :
    HasDerivAt (fun s => position s z) (velocity t z) t := by
  convert ((((hasDerivAt_id t).mul_const (z 1)).const_add (z 0)).add
    ((((hasDerivAt_id t).pow 2).const_mul (input z)).div_const 2)).add
    ((((hasDerivAt_id t).sub_const 1).add (exp_neg_derivative t)).const_mul
      (z 2 - input z)) using 1
  · rfl
  · dsimp [velocity]
    ring

/-- The right-hand side uses the held initial command, not resampled feedback. -/
theorem segment_ode (t : ℝ) (z : State) (i : Fin 3) :
    HasDerivAt (fun s => segment s z i)
      (vectorField (input z) (segment t z) i) t := by
  fin_cases i
  · simpa [segment, vectorField] using position_derivative t z
  · simpa [segment, vectorField] using velocity_derivative t z
  · simpa [segment, vectorField] using acceleration_derivative t z

/-- Replace the exponential by one scalar parameter; this dependence is affine. -/
def segmentInExp (h e : ℝ) (z : State) : State :=
  ![z 0 + h * z 1 + input z * h ^ 2 / 2 + (z 2 - input z) * (h - 1 + e),
    z 1 + input z * h + (z 2 - input z) * (1 - e),
    input z + (z 2 - input z) * e]

theorem segment_eq_segmentInExp (h : ℝ) (z : State) :
    segment h z = segmentInExp h (Real.exp (-h)) z := rfl

theorem lower_vertex (h : ℝ) (z : State) :
    segmentInExp h (1 - h) z = Generated.LagLower.transition h *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.LagLower.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem upper_vertex (h : ℝ) (z : State) :
    segmentInExp h (1 - h + h ^ 2) z = Generated.LagUpper.transition h *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.LagUpper.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem segmentInExp_affine (h lo hi theta : ℝ) (z : State) :
    segmentInExp h ((1 - theta) * lo + theta * hi) z =
      (1 - theta) • segmentInExp h lo z + theta • segmentInExp h hi z := by
  ext i
  fin_cases i <;> simp [segmentInExp, Pi.add_apply] <;> ring

/-- The exponential remainder is retained as an enclosing interval. -/
theorem exp_enclosure {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    1 - h ≤ Real.exp (-h) ∧ Real.exp (-h) ≤ 1 - h + h ^ 2 := by
  have hl := Real.add_one_le_exp (-h)
  have habs : |(-h)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have hu := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
  constructor <;> nlinarith

/-- Convex interpolation includes h=0 explicitly, with no division by zero. -/
theorem exp_interpolation {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      Real.exp (-h) = (1 - theta) * (1 - h) + theta * (1 - h + h ^ 2) := by
  obtain ⟨hl, hu⟩ := exp_enclosure h0 h1
  by_cases hz : h = 0
  · subst h
    exact ⟨0, by norm_num, by norm_num, by norm_num⟩
  · have hp : 0 < h ^ 2 := sq_pos_of_ne_zero hz
    refine ⟨(Real.exp (-h) - (1 - h)) / h ^ 2, ?_, ?_, ?_⟩
    · exact div_nonneg (by linarith) hp.le
    · apply (div_le_one hp).mpr
      linarith
    · field_simp
      ring

/-- The exact exponential state lies in the segment joining the polynomial vertices. -/
theorem segment_enclosed {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (z : State) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      segment h z = (1 - theta) • (Generated.LagLower.transition h *ᵥ z) +
        theta • (Generated.LagUpper.transition h *ᵥ z) := by
  obtain ⟨theta, ht0, ht1, he⟩ := exp_interpolation h0 h1
  refine ⟨theta, ht0, ht1, ?_⟩
  rw [segment_eq_segmentInExp, he, segmentInExp_affine, lower_vertex, upper_vertex]

/-- Both enclosing polynomial vertices share the same checked energy. -/
theorem vertex_energy_eq : Generated.LagUpper.P = Generated.LagLower.P := rfl

/-- The vertex certificates bound the actual exponential plant, including its
exponential remainder, throughout the certified sampling interval. -/
theorem segment_energy_decrease {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 5) (z : State) :
    energy Generated.LagLower.P (segment h z) ≤
      energy Generated.LagLower.P z - h * squaredNorm z := by
  obtain ⟨theta, ht0, ht1, he⟩ := segment_enclosed h0 (by linarith) z
  rw [he]
  apply VertexCertificate.shared_bound Generated.LagLower.P Generated.LagLower.P_psd
    _ _ ht0 ht1
  · simpa using Generated.LagLower.certified_decrease h0 hhi z
  · have hu := Generated.LagUpper.certified_decrease h0 hhi z
    rw [vertex_energy_eq] at hu
    simpa using hu

/-- Every permitted elapsed time stays below the energy at the initial sample. -/
theorem intersample_energy {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) (z : State) :
    energy Generated.LagLower.P (segment t z) ≤ energy Generated.LagLower.P z := by
  have hd := segment_energy_decrease ht0 hthi z
  have hn : 0 ≤ squaredNorm z := Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  exact hd.trans (sub_le_self _ (mul_nonneg ht0 hn))

/-- The generated upper energy bound gives an explicit nominal contraction. -/
theorem segment_contraction {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 5) (z : State) :
    energy Generated.LagLower.P (segment h z) ≤
      (1 - h / 24) * energy Generated.LagLower.P z := by
  have hd := segment_energy_decrease h0 hhi z
  have hu := (Generated.LagLower.certified_energy_bounds z).2
  norm_num [Generated.LagLower.upperBound] at hu
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ h / 24 by positivity)
  nlinarith only [hd, hm]

/-- Arbitrary nominal sampling jitter composes the actual exponential steps. -/
theorem jitter_energy_bound (h : ℕ → ℝ) (z : ℕ → State) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 5)
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ 1 / 5)
    (hdyn : ∀ k, z (k + 1) = segment (h k) (z k)) (n : ℕ) :
    energy Generated.LagLower.P (z n) ≤
      (1 - hmin / 24) ^ n * energy Generated.LagLower.P (z 0) := by
  apply geometric_bound (V := fun k => energy Generated.LagLower.P (z k)) (by linarith)
  intro k
  rw [hdyn k]
  have hc := segment_contraction (hmin0.trans (hlo k)) (hhi k) (z k)
  have hn : 0 ≤ energy Generated.LagLower.P (z k) :=
    Generated.LagLower.P_psd.dotProduct_mulVec_nonneg (z k)
  exact hc.trans (mul_le_mul_of_nonneg_right (by linarith [hlo k]) hn)

/-- The sample-index envelope also bounds every intermediate point of each
actual held interval; no disturbed or quantized lag model is asserted. -/
theorem sampled_segment_bound (h : ℕ → ℝ) (z : ℕ → State) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 5)
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ 1 / 5)
    (hdyn : ∀ k, z (k + 1) = segment (h k) (z k)) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h n) :
    energy Generated.LagLower.P (segment t (z n)) ≤
      (1 - hmin / 24) ^ n * energy Generated.LagLower.P (z 0) := by
  exact (intersample_energy ht0 (hth.trans (hhi n)) (z n)).trans
    (jitter_energy_bound h z hmin0 hminhi hlo hhi hdyn n)

end LeanControls.ActuatorLag
