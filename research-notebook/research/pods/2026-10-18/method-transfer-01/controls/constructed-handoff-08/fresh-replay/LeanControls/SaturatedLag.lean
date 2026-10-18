module

public import LeanControls.ActuatorLag
public import LeanControls.SaturationSector
public import LeanControls.Generated.TravelQuarterLower
public import LeanControls.Generated.TravelQuarterUpper
public import LeanControls.Generated.TravelFullLower
public import LeanControls.Generated.TravelFullUpper

/-! Exact held-input dynamics for x'=v, v'=a, a'=-a+u, with normalized lag
time constant one. The actual held command is the saturated sampled request
plus a held additive disturbance. Intermediate-time statements concern this
exact exponential plant, not a polynomial approximation. -/

@[expose] public section
noncomputable section
namespace LeanControls.SaturatedLag
open Matrix

abbrev State := Fin 3 → ℝ

abbrev P := Generated.TravelQuarterLower.P

def energy (z : State) : ℝ := BernsteinCertificate.energy P z

def input (z : State) : ℝ := -z 0 - 3 * z 1 - 2 * z 2

def heldAcceleration (t : ℝ) (z : State) (u : ℝ) : ℝ :=
  u + (z 2 - u) * Real.exp (-t)

def heldVelocity (t : ℝ) (z : State) (u : ℝ) : ℝ :=
  z 1 + u * t + (z 2 - u) * (1 - Real.exp (-t))

def heldPosition (t : ℝ) (z : State) (u : ℝ) : ℝ :=
  z 0 + t * z 1 + u * t ^ 2 / 2 + (z 2 - u) * (t - 1 + Real.exp (-t))

def heldSegment (t : ℝ) (z : State) (u : ℝ) : State :=
  ![heldPosition t z u, heldVelocity t z u, heldAcceleration t z u]

def nominalSegment (t : ℝ) (z : State) (alpha : ℝ) : State :=
  heldSegment t z (alpha * input z)

def segment (t : ℝ) (z : State) (w : ℝ) : State :=
  heldSegment t z (RobustPD.saturate 1 (input z) + w)

/-- Exact state response to a constant additive input, starting from zero. -/
def response (t : ℝ) : State :=
  ![t ^ 2 / 2 - t + 1 - Real.exp (-t),
    t - 1 + Real.exp (-t), 1 - Real.exp (-t)]

theorem heldSegment_zero (z : State) (u : ℝ) : heldSegment 0 z u = z := by
  ext i
  fin_cases i <;> simp [heldSegment, heldPosition, heldVelocity, heldAcceleration]

theorem segment_zero (z : State) (w : ℝ) : segment 0 z w = z :=
  heldSegment_zero z _

theorem nominalSegment_zero (z : State) (alpha : ℝ) : nominalSegment 0 z alpha = z :=
  heldSegment_zero z _

theorem heldAcceleration_derivative (t : ℝ) (z : State) (u : ℝ) :
    HasDerivAt (fun s => heldAcceleration s z u) (-heldAcceleration t z u + u) t := by
  convert ((ActuatorLag.exp_neg_derivative t).const_mul (z 2 - u)).const_add u using 1
  · rfl
  · dsimp [heldAcceleration]
    ring

theorem heldVelocity_derivative (t : ℝ) (z : State) (u : ℝ) :
    HasDerivAt (fun s => heldVelocity s z u) (heldAcceleration t z u) t := by
  convert (((hasDerivAt_id t).const_mul u).const_add (z 1)).add
    (((ActuatorLag.exp_neg_derivative t).const_sub 1).const_mul (z 2 - u)) using 1
  · rfl
  · dsimp [heldAcceleration]
    ring

theorem heldPosition_derivative (t : ℝ) (z : State) (u : ℝ) :
    HasDerivAt (fun s => heldPosition s z u) (heldVelocity t z u) t := by
  convert ((((hasDerivAt_id t).mul_const (z 1)).const_add (z 0)).add
    ((((hasDerivAt_id t).pow 2).const_mul u).div_const 2)).add
    ((((hasDerivAt_id t).sub_const 1).add (ActuatorLag.exp_neg_derivative t)).const_mul
      (z 2 - u)) using 1
  · rfl
  · dsimp [heldVelocity]
    ring

theorem heldSegment_ode (t : ℝ) (z : State) (u : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => heldSegment s z u i)
      (ActuatorLag.vectorField u (heldSegment t z u) i) t := by
  fin_cases i
  · simpa [heldSegment, ActuatorLag.vectorField] using heldPosition_derivative t z u
  · simpa [heldSegment, ActuatorLag.vectorField] using heldVelocity_derivative t z u
  · simpa [heldSegment, ActuatorLag.vectorField] using heldAcceleration_derivative t z u

/-- The command uses the initial sample, and the disturbance is held too. -/
theorem segment_ode (t : ℝ) (z : State) (w : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => segment s z w i)
      (ActuatorLag.vectorField (RobustPD.saturate 1 (input z) + w) (segment t z w) i) t :=
  heldSegment_ode t z _ i

theorem heldSegment_add_input (t : ℝ) (z : State) (u w : ℝ) :
    heldSegment t z (u + w) = heldSegment t z u + w • response t := by
  ext i
  fin_cases i <;>
    simp [heldSegment, heldPosition, heldVelocity, heldAcceleration, response,
      Pi.add_apply] <;> ring

theorem segment_eq_nominal_add_response (t : ℝ) (z : State) (w alpha : ℝ)
    (ha : RobustPD.saturate 1 (input z) = alpha * input z) :
    segment t z w = nominalSegment t z alpha + w • response t := by
  unfold segment nominalSegment
  rw [ha, heldSegment_add_input]

/-- A request of magnitude at most four admits a gain in [1/4,1], including
genuinely clipped requests. The same gain is held throughout this interval. -/
theorem segment_sector_decomposition (z : State) (hrequest : |input z| ≤ 4) :
    ∃ alpha : ℝ, 1 / 4 ≤ alpha ∧ alpha ≤ 1 ∧
      ∀ t w, segment t z w = nominalSegment t z alpha + w • response t := by
  obtain ⟨alpha, ha0, ha1, ha⟩ := SaturationSector.exists_sector_gain
    (U := 1) (kappa := 1 / 4) (u := input z)
    (by norm_num) (by norm_num) (by norm_num) (by linarith)
  exact ⟨alpha, ha0, ha1, fun t w => segment_eq_nominal_add_response t z w alpha ha⟩

/-- Keep one common exponential parameter across all three coordinates. -/
def segmentInExp (t e : ℝ) (z : State) (alpha : ℝ) : State :=
  ![z 0 + t * z 1 + (alpha * input z) * t ^ 2 / 2 +
      (z 2 - alpha * input z) * (t - 1 + e),
    z 1 + (alpha * input z) * t + (z 2 - alpha * input z) * (1 - e),
    alpha * input z + (z 2 - alpha * input z) * e]

theorem nominal_eq_segmentInExp (t : ℝ) (z : State) (alpha : ℝ) :
    nominalSegment t z alpha = segmentInExp t (Real.exp (-t)) z alpha := rfl

theorem segmentInExp_affine_exp (t lo hi theta : ℝ) (z : State) (alpha : ℝ) :
    segmentInExp t ((1 - theta) * lo + theta * hi) z alpha =
      (1 - theta) • segmentInExp t lo z alpha + theta • segmentInExp t hi z alpha := by
  ext i
  fin_cases i <;> simp [segmentInExp, Pi.add_apply] <;> ring

theorem segmentInExp_affine_gain (t e lo hi beta : ℝ) (z : State) :
    segmentInExp t e z ((1 - beta) * lo + beta * hi) =
      (1 - beta) • segmentInExp t e z lo + beta • segmentInExp t e z hi := by
  ext i
  fin_cases i <;> simp [segmentInExp, Pi.add_apply] <;> ring

theorem quarter_lower_vertex (t : ℝ) (z : State) :
    segmentInExp t (1 - t) z (1 / 4) =
      Generated.TravelQuarterLower.transition t *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.TravelQuarterLower.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem quarter_upper_vertex (t : ℝ) (z : State) :
    segmentInExp t (1 - t + t ^ 2) z (1 / 4) =
      Generated.TravelQuarterUpper.transition t *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.TravelQuarterUpper.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem full_lower_vertex (t : ℝ) (z : State) :
    segmentInExp t (1 - t) z 1 = Generated.TravelFullLower.transition t *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.TravelFullLower.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem full_upper_vertex (t : ℝ) (z : State) :
    segmentInExp t (1 - t + t ^ 2) z 1 =
      Generated.TravelFullUpper.transition t *ᵥ z := by
  ext i
  fin_cases i <;>
    simp [segmentInExp, input, Generated.TravelFullUpper.transition, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

/-- The exact exponential state is a nested convex combination of four checked
polynomial vertices. This includes elapsed time zero and both sector endpoints. -/
theorem nominal_enclosed {t alpha : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha0 : 1 / 4 ≤ alpha) (ha1 : alpha ≤ 1) (z : State) :
    ∃ theta beta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧ 0 ≤ beta ∧ beta ≤ 1 ∧
      nominalSegment t z alpha =
        (1 - beta) •
          ((1 - theta) • (Generated.TravelQuarterLower.transition t *ᵥ z) +
            theta • (Generated.TravelQuarterUpper.transition t *ᵥ z)) +
        beta •
          ((1 - theta) • (Generated.TravelFullLower.transition t *ᵥ z) +
            theta • (Generated.TravelFullUpper.transition t *ᵥ z)) := by
  obtain ⟨theta, htlo, hthi, he⟩ := ActuatorLag.exp_interpolation ht0 ht1
  let beta := (4 * alpha - 1) / 3
  have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
  have hb1 : beta ≤ 1 := by dsimp [beta]; linarith
  have ha : alpha = (1 - beta) * (1 / 4) + beta * 1 := by dsimp [beta]; ring
  refine ⟨theta, beta, htlo, hthi, hb0, hb1, ?_⟩
  rw [nominal_eq_segmentInExp, ha, segmentInExp_affine_gain, he,
    segmentInExp_affine_exp, segmentInExp_affine_exp,
    quarter_lower_vertex, quarter_upper_vertex, full_lower_vertex, full_upper_vertex]

/-- One common positive quadratic energy certifies every allowed sector gain,
for every elapsed time up to one fifth, for the exact exponential plant. -/
theorem nominal_energy_decrease {t alpha : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5)
    (ha0 : 1 / 4 ≤ alpha) (ha1 : alpha ≤ 1) (z : State) :
    energy (nominalSegment t z alpha) ≤
      energy z - t * BernsteinCertificate.squaredNorm z := by
  obtain ⟨theta, beta, htlo, hthi', hb0, hb1, he⟩ :=
    nominal_enclosed ht0 (by linarith) ha0 ha1 z
  unfold energy
  rw [he]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ hb0 hb1
  · apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ htlo hthi'
    · simpa using Generated.TravelQuarterLower.certified_decrease ht0 hthi z
    · simpa [P, Generated.TravelQuarterUpper.P, Generated.TravelQuarterLower.P] using
        Generated.TravelQuarterUpper.certified_decrease ht0 hthi z
  · apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ htlo hthi'
    · simpa [P, Generated.TravelFullLower.P, Generated.TravelQuarterLower.P] using
        Generated.TravelFullLower.certified_decrease ht0 hthi z
    · simpa [P, Generated.TravelFullUpper.P, Generated.TravelQuarterLower.P] using
        Generated.TravelFullUpper.certified_decrease ht0 hthi z

theorem nominal_energy_nonexpansion {t alpha : ℝ}
    (ht0 : 0 ≤ t) (hthi : t ≤ 1 / 5) (ha0 : 1 / 4 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : State) : energy (nominalSegment t z alpha) ≤ energy z := by
  have hn : 0 ≤ BernsteinCertificate.squaredNorm z :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  exact (nominal_energy_decrease ht0 hthi ha0 ha1 z).trans
    (sub_le_self _ (mul_nonneg ht0 hn))

end LeanControls.SaturatedLag
