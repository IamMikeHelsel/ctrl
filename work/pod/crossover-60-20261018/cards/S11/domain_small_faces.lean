module
public import ClearancePolicy
@[expose] public section
noncomputable section
namespace S11SmallFaces
open LeanControls.DigitalHold LeanControls.WeightedEntry

/-- All six actual faces are strictly inward for the proposed small terminal
box. This assumes the independently specified refined residual bound. -/
theorem small_faces {r w : ℝ} {z : State}
    (hrlo : 8 ≤ r) (hrhi : r ≤ 12) (hw : |w| ≤ (3/10000 : ℝ))
    (hz : ∀ i, |z i| ≤ weight i*(1/8120)) (i : Fin 3) :
    (z i = weight i*(1/8120) → transformedRHS r w z i < 0) ∧
    (z i = -weight i*(1/8120) → 0 < transformedRHS r w z i) := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hw' := abs_le.mp hw
  norm_num [weight] at h0 h1 h2
  fin_cases i
  · norm_num [weight,transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight,transformedRHS]
    have p0 := mul_nonneg (show 0 ≤ r-8 by linarith)
      (show 0 ≤ z 0+(51/50)*(1/8120) by linarith)
    have p1 := mul_nonneg (show 0 ≤ r-8 by linarith)
      (show 0 ≤ (101/100)*(1/8120)-z 1 by linarith)
    have p2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ 3/10000-w by linarith)
    have n0 := mul_nonneg (show 0 ≤ r-8 by linarith)
      (show 0 ≤ (51/50)*(1/8120)-z 0 by linarith)
    have n1 := mul_nonneg (show 0 ≤ r-8 by linarith)
      (show 0 ≤ z 1+(101/100)*(1/8120) by linarith)
    have n2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ w+3/10000 by linarith)
    constructor <;> intro he <;> rw [he] <;> nlinarith

#print axioms small_faces
end S11SmallFaces
