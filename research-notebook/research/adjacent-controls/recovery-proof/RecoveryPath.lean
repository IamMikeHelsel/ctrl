import LeanControls.UncertainLag
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option maxHeartbeats 1000000
noncomputable section
namespace LeanControls.RecoveryPath
open UncertainLag
abbrev State := UncertainLag.State

def InitialBox (z : State) : Prop :=
  99/100 ≤ z 0 ∧ z 0 ≤ 101/100 ∧
  49/100 ≤ z 1 ∧ z 1 ≤ 51/100 ∧
  -1/100 ≤ z 2 ∧ z 2 ≤ 1/100

/-- Derivative bounds imply finite-interval displacement bounds. -/
theorem growth_bounds {f df : ℝ → ℝ} {t lo hi : ℝ}
    (ht : 0 ≤ t) (hd : ∀ s, HasDerivAt f (df s) s)
    (hb : ∀ s, 0 ≤ s → s ≤ t → lo ≤ df s ∧ df s ≤ hi) :
    lo*t ≤ f t-f 0 ∧ f t-f 0 ≤ hi*t := by
  have hc : ContinuousOn f (Set.Icc 0 t) :=
    fun s _ => (hd s).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 t)) :=
    fun s _ => (hd s).differentiableAt.differentiableWithinAt
  constructor
  · simpa using (convex_Icc (0:ℝ) t).mul_sub_le_image_sub_of_le_deriv hc hdiff
      (fun s hs => by
        rw [(hd s).deriv]
        exact (hb s (interior_subset hs).1 (interior_subset hs).2).1)
      0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  · simpa using (convex_Icc (0:ℝ) t).image_sub_le_mul_sub_of_deriv_le hc hdiff
      (fun s hs => by
        rw [(hd s).deriv]
        exact (hb s (interior_subset hs).1 (interior_subset hs).2).2)
      0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht

theorem backup_acceleration {r t : ℝ} {z : State}
    (hr : 0 < r) (hzlo : -1 ≤ z 2) (hzhi : z 2 ≤ 1/100) (ht : 0 ≤ t) :
    -1 ≤ heldSegment r t z (-1) 2 ∧ heldSegment r t z (-1) 2 ≤ 1/100 := by
  have he0 := Real.exp_nonneg (-r*t)
  have he1 : Real.exp (-r*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm0 := mul_nonneg (show 0 ≤ z 2+1 by linarith) he0
  have hm1 := mul_le_mul_of_nonneg_left he1 (show 0 ≤ z 2+1 by linarith)
  dsimp [heldSegment, heldSolution]
  constructor <;> nlinarith

theorem backup_velocity {r t : ℝ} {z : State}
    (hr : 0 < r) (hzlo : -1 ≤ z 2) (hzhi : z 2 ≤ 1/100) (ht : 0 ≤ t) :
    z 1-t ≤ heldSegment r t z (-1) 1 ∧
    heldSegment r t z (-1) 1 ≤ z 1+t/100 := by
  have hd (s : ℝ) : HasDerivAt (fun q => heldSegment r q z (-1) 1)
      (heldSegment r s z (-1) 2) s := by
    simpa [vectorField] using heldSegment_ode (ne_of_gt hr) s z (-1) (1:Fin 3)
  have h := growth_bounds ht hd (fun s hs _ => backup_acceleration hr hzlo hzhi hs)
  rw [heldSegment_zero] at h
  constructor <;> linarith

/-- Full elapsed-time quadratic bounds; no restriction r*t<=1 is needed. -/
theorem backup_position_polynomial {r t : ℝ} {z : State}
    (hr : 0 < r) (hzlo : -1 ≤ z 2) (hzhi : z 2 ≤ 1/100) (ht : 0 ≤ t) :
    z 0+z 1*t-t^2/2 ≤ heldSegment r t z (-1) 0 ∧
    heldSegment r t z (-1) 0 ≤ z 0+z 1*t+t^2/200 := by
  have hx (s : ℝ) : HasDerivAt (fun q => heldSegment r q z (-1) 0)
      (heldSegment r s z (-1) 1) s := by
    simpa [vectorField] using heldSegment_ode (ne_of_gt hr) s z (-1) (0:Fin 3)
  have hlow (s : ℝ) : HasDerivAt
      (fun q => heldSegment r q z (-1) 0-(z 0+z 1*q-q^2/2))
      (heldSegment r s z (-1) 1-(z 1-s)) s := by
    convert (hx s).sub (((((hasDerivAt_id s).const_mul (z 1)).const_add (z 0))).sub
      (((hasDerivAt_id s).pow 2).div_const 2)) using 1
    · rfl
    · dsimp; ring
  have hupp (s : ℝ) : HasDerivAt
      (fun q => heldSegment r q z (-1) 0-(z 0+z 1*q+q^2/200))
      (heldSegment r s z (-1) 1-(z 1+s/100)) s := by
    convert (hx s).sub (((((hasDerivAt_id s).const_mul (z 1)).const_add (z 0))).add
      (((hasDerivAt_id s).pow 2).div_const 200)) using 1
    · rfl
    · dsimp; ring
  have hl := (convex_Icc (0:ℝ) t).mul_sub_le_image_sub_of_le_deriv
    (fun s _ => (hlow s).continuousAt.continuousWithinAt)
    (fun s _ => (hlow s).differentiableAt.differentiableWithinAt)
    (C := 0) (fun s hs => by
      rw [(hlow s).deriv]
      have hv := (backup_velocity hr hzlo hzhi (interior_subset hs).1).1
      linarith)
    0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  have hu := (convex_Icc (0:ℝ) t).image_sub_le_mul_sub_of_deriv_le
    (fun s _ => (hupp s).continuousAt.continuousWithinAt)
    (fun s _ => (hupp s).differentiableAt.differentiableWithinAt)
    (C := 0) (fun s hs => by
      rw [(hupp s).deriv]
      have hv := (backup_velocity hr hzlo hzhi (interior_subset hs).1).2
      linarith)
    0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  simp only [heldSegment_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    add_zero, sub_zero, sub_self] at hl hu
  constructor <;> linarith

theorem backup_position_bounds {r t : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (hz : InitialBox z)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 5/4) :
    657/800 ≤ heldSegment r t z (-1) 0 ∧
    heldSegment r t z (-1) 0 ≤ 5297/3200 := by
  obtain ⟨hx0,hx1,hv0,hv1,ha0,ha1⟩ := hz
  have hb := backup_position_polynomial (by linarith : 0 < r)
    (by linarith : -1 ≤ z 2) ha1 ht0
  have hl := mul_le_mul_of_nonneg_right hv0 ht0
  have hu := mul_le_mul_of_nonneg_right hv1 ht0
  have htprod := mul_nonneg ht0 (show 0 ≤ 5/4-t by linarith)
  have htsq := sq_nonneg t
  constructor <;> nlinarith

theorem backup_travel {r t : ℝ} {z : State}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (hz : InitialBox z)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 5/4) :
    |heldSegment r t z (-1) 0| ≤ 2 := by
  have hb := backup_position_bounds hrlo hrhi hz ht0 ht1
  rw [abs_le]
  constructor <;> linarith

/-- The entire starting box lies strictly outside the previously certified ellipsoid. -/
theorem initial_energy_lower {z : State} (hz : InitialBox z) :
    (11749189/500000:ℝ) ≤ BernsteinCertificate.energy UncertainLag.P z := by
  obtain ⟨hx0,hx1,hv0,hv1,ha0,ha1⟩ := hz
  have hxpos : 0 ≤ z 0 := by linarith
  have hvpos : 0 ≤ z 1 := by linarith
  have hxx : (99/100:ℝ)^2 ≤ (z 0)^2 := by nlinarith
  have hvv : (49/100:ℝ)^2 ≤ (z 1)^2 := by nlinarith
  have hxv : (99/100:ℝ)*(49/100) ≤ z 0*z 1 := by
    nlinarith [mul_nonneg (show 0 ≤ z 0-99/100 by linarith)
      (show 0 ≤ z 1-49/100 by linarith)]
  have hxa : (-101/10000:ℝ) ≤ z 0*z 2 := by
    nlinarith [mul_nonneg hxpos (show 0 ≤ z 2+1/100 by linarith)]
  have hva : (-51/10000:ℝ) ≤ z 1*z 2 := by
    nlinarith [mul_nonneg hvpos (show 0 ≤ z 2+1/100 by linarith)]
  simp [BernsteinCertificate.energy, UncertainLag.P, Generated.TravelQuarterLower.P,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (z 2)]

theorem initial_outside {z : State} (hz : InitialBox z) :
    12 < BernsteinCertificate.energy UncertainLag.P z := by
  have h := initial_energy_lower hz
  linarith

end LeanControls.RecoveryPath
#print axioms LeanControls.RecoveryPath.growth_bounds
#print axioms LeanControls.RecoveryPath.backup_acceleration
#print axioms LeanControls.RecoveryPath.backup_velocity
#print axioms LeanControls.RecoveryPath.backup_position_polynomial
#print axioms LeanControls.RecoveryPath.backup_position_bounds
#print axioms LeanControls.RecoveryPath.backup_travel

#print axioms LeanControls.RecoveryPath.initial_energy_lower
#print axioms LeanControls.RecoveryPath.initial_outside
