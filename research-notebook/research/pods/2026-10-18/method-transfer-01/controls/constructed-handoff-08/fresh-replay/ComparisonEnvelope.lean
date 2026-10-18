module
public import LeanControls.UncertainLag
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite-horizon envelopes for an actual classical trajectory whose actuator
rate and effective acceleration target can change during a held-command period.
The bounds below do not assume that either signal is constant. -/
@[expose] public section
noncomputable section
namespace LeanControls.VariableResponse
open Set MeasureTheory
open UncertainLag (State heldSolution)

/-- Continuity includes both endpoints. The differential equations are required
only in the interior. No equality with an analytic flow is assumed. -/
structure IsTrajectory (H : ℝ) (r b : ℝ → ℝ) (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Icc 0 H)
  ode : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
    HasDerivAt (fun s => f s i) (![f t 1, f t 2, r t * (b t - f t 2)] i) t

/-- A scalar differential inequality with a variable continuous coefficient.
This integrating-factor argument requires no derivative bound on the rate. -/
theorem linear_comparison {H : ℝ} (hH : 0 ≤ H) {r f g df dg : ℝ → ℝ}
    (hr : ContinuousOn r (Icc 0 H))
    (hf : ContinuousOn f (Icc 0 H)) (hg : ContinuousOn g (Icc 0 H))
    (hdf : ∀ t ∈ Ioo 0 H, HasDerivAt f (df t) t)
    (hdg : ∀ t ∈ Ioo 0 H, HasDerivAt g (dg t) t)
    (hi : f 0 ≤ g 0)
    (hineq : ∀ t ∈ Ioo 0 H, df t - dg t + r t * (f t - g t) ≤ 0) :
    ∀ t ∈ Icc 0 H, f t ≤ g t := by
  let R : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, r s
  have hRc : ContinuousOn R (Icc 0 H) :=
    by
    simpa only [uIcc_of_le hH] using
      intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn r (uIcc 0 H) from by
          simpa only [uIcc_of_le hH] using hr.integrableOn_Icc)
  have hRd (t : ℝ) (ht : t ∈ Ioo 0 H) : HasDerivAt R (r t) t := by
    have hrt : ContinuousAt r t := hr.continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact intervalIntegral.integral_hasDerivAt_right
      ((hr.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hr.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht) hrt
  let w : ℝ → ℝ := fun t => (f t - g t) * Real.exp (R t)
  have hwc : ContinuousOn w (Icc 0 H) := (hf.sub hg).mul (Real.continuous_exp.comp_continuousOn hRc)
  have hwd (t : ℝ) (ht : t ∈ Ioo 0 H) : HasDerivAt w
      ((df t - dg t + r t * (f t - g t)) * Real.exp (R t)) t := by
    convert ((hdf t ht).sub (hdg t ht)).mul ((hRd t ht).exp) using 1 <;> dsimp [w] <;> ring
  have hwmono : AntitoneOn w (Icc 0 H) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hwc
    · intro t ht
      exact (hwd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hwd t (by simpa only [interior_Icc] using ht)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (hineq t (by simpa only [interior_Icc] using ht))
        (Real.exp_pos _).le
  intro t ht
  have hwle : w t ≤ 0 := (hwmono ⟨le_rfl, hH⟩ ht ht.1).trans (by
    dsimp [w, R]
    simpa using sub_nonpos.mpr hi)
  dsimp only [w] at hwle
  nlinarith [Real.exp_pos (R t)]

/-- Ordinary derivative order transfers initial order over a closed interval. -/
theorem derivative_comparison {H : ℝ} (hH : 0 ≤ H) {f g df dg : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 H)) (hg : ContinuousOn g (Icc 0 H))
    (hdf : ∀ t ∈ Ioo 0 H, HasDerivAt f (df t) t)
    (hdg : ∀ t ∈ Ioo 0 H, HasDerivAt g (dg t) t)
    (hi : f 0 ≤ g 0) (hineq : ∀ t ∈ Ioo 0 H, df t ≤ dg t) :
    ∀ t ∈ Icc 0 H, f t ≤ g t :=
  linear_comparison hH (r := fun _ => 0) continuousOn_const hf hg hdf hdg hi
    (fun t ht => by simpa using sub_nonpos.mpr (hineq t ht))


/-- Upper response uses the slow rate above its target and the fast rate below. -/
def upperRate (rlo rhi aHi bHi : ℝ) : ℝ := if bHi ≤ aHi then rlo else rhi

/-- The lower comparison uses the opposite endpoint choices. -/
def lowerRate (rlo rhi aLo bLo : ℝ) : ℝ := if bLo ≤ aLo then rhi else rlo

private theorem flow_continuous {R : ℝ} (hR : R ≠ 0) (b : ℝ) (z : State) (i : Fin 3) :
    Continuous (fun t => heldSolution R t b z i) :=
  continuous_iff_continuousAt.mpr fun t => (UncertainLag.exact_ode hR b t z i).continuousAt

private theorem upper_supersolution {rlo rhi q b : ℝ} {z : State}
    (hqlo : rlo ≤ q) (hqhi : q ≤ rhi) (t : ℝ) :
    q * (b - heldSolution (upperRate rlo rhi (z 2) b) t b z 2) ≤
      upperRate rlo rhi (z 2) b *
        (b - heldSolution (upperRate rlo rhi (z 2) b) t b z 2) := by
  by_cases h : b ≤ z 2
  · simp only [upperRate, ite_eq_left h]
    dsimp only [heldSolution, Matrix.cons_val, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail]
    have he : 0 ≤ (z 2 - b) * Real.exp (-rlo*t) := mul_nonneg (sub_nonneg.mpr h) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonpos_right hqlo (show b-(b+(z 2-b)*Real.exp (-rlo*t)) ≤ 0 by linarith)]
  · simp only [upperRate, ite_eq_right h]
    dsimp only [heldSolution, Matrix.cons_val, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail]
    have he : (z 2 - b) * Real.exp (-rhi*t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right hqhi (show 0 ≤ b-(b+(z 2-b)*Real.exp (-rhi*t)) by linarith)]

private theorem lower_subsolution {rlo rhi q b : ℝ} {z : State}
    (hqlo : rlo ≤ q) (hqhi : q ≤ rhi) (t : ℝ) :
    lowerRate rlo rhi (z 2) b *
        (b - heldSolution (lowerRate rlo rhi (z 2) b) t b z 2) ≤
      q * (b - heldSolution (lowerRate rlo rhi (z 2) b) t b z 2) := by
  by_cases h : b ≤ z 2
  · simp only [lowerRate, ite_eq_left h]
    dsimp only [heldSolution, Matrix.cons_val, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail]
    have he : 0 ≤ (z 2 - b) * Real.exp (-rhi*t) := mul_nonneg (sub_nonneg.mpr h) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonpos_right hqhi (show b-(b+(z 2-b)*Real.exp (-rhi*t)) ≤ 0 by linarith)]
  · simp only [lowerRate, ite_eq_right h]
    dsimp only [heldSolution, Matrix.cons_val, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail]
    have he : (z 2 - b) * Real.exp (-rlo*t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right hqlo (show 0 ≤ b-(b+(z 2-b)*Real.exp (-rlo*t)) by linarith)]

/-- Every actual classical execution lies below this explicit flow at every time.
Both rate and effective target may vary inside the interval. -/
theorem upper_flow_bound {H rlo rhi bHi : ℝ} (hH : 0 ≤ H)
    {r b : ℝ → ℝ} {f : ℝ → State} {zHi : State}
    (hrc : ContinuousOn r (Icc 0 H)) (hrlo0 : 0 < rlo)
    (hrlo : ∀ t ∈ Icc 0 H, rlo ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ rhi)
    (hb : ∀ t ∈ Icc 0 H, b t ≤ bHi) (hf : IsTrajectory H r b f)
    (hi : ∀ i : Fin 3, f 0 i ≤ zHi i) :
    ∀ t ∈ Icc 0 H, ∀ i : Fin 3,
      f t i ≤ heldSolution (upperRate rlo rhi (zHi 2) bHi) t bHi zHi i := by
  let R := upperRate rlo rhi (zHi 2) bHi
  have hR : R ≠ 0 := by
    have hh : 0 < rhi := hrlo0.trans_le ((hrlo 0 ⟨le_rfl,hH⟩).trans (hrhi 0 ⟨le_rfl,hH⟩))
    dsimp [R, upperRate]
    split_ifs <;> positivity
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc (i : Fin 3) := (flow_continuous hR bHi zHi i).continuousOn (s := Icc 0 H)
  have hd (i : Fin 3) (t : ℝ) := UncertainLag.exact_ode hR bHi t zHi i
  have hinit (i : Fin 3) : f 0 i ≤ heldSolution R 0 bHi zHi i := by
    simpa only [UncertainLag.exact_initial] using hi i
  have ha : ∀ t ∈ Icc 0 H, f t 2 ≤ heldSolution R t bHi zHi 2 := by
    apply linear_comparison hH hrc (hfc 2) (hc 2)
      (fun t ht => hf.ode t ht 2) (fun t _ => hd 2 t) (hinit 2)
    intro t ht
    have htc : t ∈ Icc 0 H := ⟨ht.1.le, ht.2.le⟩
    have hq : 0 ≤ r t := (hrlo0.trans_le (hrlo t htc)).le
    have hb' := mul_le_mul_of_nonneg_left (hb t htc) hq
    have hs := upper_supersolution (z := zHi) (b := bHi) (hrlo t htc) (hrhi t htc) t
    change r t*(b t-f t 2) - R*(bHi-heldSolution R t bHi zHi 2) +
      r t*(f t 2-heldSolution R t bHi zHi 2) ≤ 0
    change r t*(bHi-heldSolution R t bHi zHi 2) ≤ R*(bHi-heldSolution R t bHi zHi 2) at hs
    nlinarith
  have hv : ∀ t ∈ Icc 0 H, f t 1 ≤ heldSolution R t bHi zHi 1 := by
    exact derivative_comparison hH (hfc 1) (hc 1)
      (fun t ht => hf.ode t ht 1) (fun t _ => hd 1 t) (hinit 1)
      (fun t ht => ha t ⟨ht.1.le, ht.2.le⟩)
  have hx : ∀ t ∈ Icc 0 H, f t 0 ≤ heldSolution R t bHi zHi 0 := by
    exact derivative_comparison hH (hfc 0) (hc 0)
      (fun t ht => hf.ode t ht 0) (fun t _ => hd 0 t) (hinit 0)
      (fun t ht => hv t ⟨ht.1.le, ht.2.le⟩)
  intro t ht i
  fin_cases i
  · exact hx t ht
  · exact hv t ht
  · exact ha t ht


/-- Coordinatewise lower envelope, with the fast rate when above the lower target
and the slow rate when below it. -/
theorem lower_flow_bound {H rlo rhi bLo : ℝ} (hH : 0 ≤ H)
    {r b : ℝ → ℝ} {f : ℝ → State} {zLo : State}
    (hrc : ContinuousOn r (Icc 0 H)) (hrlo0 : 0 < rlo)
    (hrlo : ∀ t ∈ Icc 0 H, rlo ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ rhi)
    (hb : ∀ t ∈ Icc 0 H, bLo ≤ b t) (hf : IsTrajectory H r b f)
    (hi : ∀ i : Fin 3, zLo i ≤ f 0 i) :
    ∀ t ∈ Icc 0 H, ∀ i : Fin 3,
      heldSolution (lowerRate rlo rhi (zLo 2) bLo) t bLo zLo i ≤ f t i := by
  let R := lowerRate rlo rhi (zLo 2) bLo
  have hR : R ≠ 0 := by
    have hh : 0 < rhi := hrlo0.trans_le ((hrlo 0 ⟨le_rfl,hH⟩).trans (hrhi 0 ⟨le_rfl,hH⟩))
    dsimp [R, lowerRate]
    split_ifs <;> positivity
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc (i : Fin 3) := (flow_continuous hR bLo zLo i).continuousOn (s := Icc 0 H)
  have hd (i : Fin 3) (t : ℝ) := UncertainLag.exact_ode hR bLo t zLo i
  have hinit (i : Fin 3) : heldSolution R 0 bLo zLo i ≤ f 0 i := by
    simpa only [UncertainLag.exact_initial] using hi i
  have ha : ∀ t ∈ Icc 0 H, heldSolution R t bLo zLo 2 ≤ f t 2 := by
    apply linear_comparison hH hrc (hc 2) (hfc 2)
      (fun t _ => hd 2 t) (fun t ht => hf.ode t ht 2) (hinit 2)
    intro t ht
    have htc : t ∈ Icc 0 H := ⟨ht.1.le, ht.2.le⟩
    have hq : 0 ≤ r t := (hrlo0.trans_le (hrlo t htc)).le
    have hb' := mul_le_mul_of_nonneg_left (hb t htc) hq
    have hs := lower_subsolution (z := zLo) (b := bLo) (hrlo t htc) (hrhi t htc) t
    change R*(bLo-heldSolution R t bLo zLo 2) - r t*(b t-f t 2) +
      r t*(heldSolution R t bLo zLo 2-f t 2) ≤ 0
    change R*(bLo-heldSolution R t bLo zLo 2) ≤ r t*(bLo-heldSolution R t bLo zLo 2) at hs
    nlinarith
  have hv : ∀ t ∈ Icc 0 H, heldSolution R t bLo zLo 1 ≤ f t 1 := by
    exact derivative_comparison hH (hc 1) (hfc 1)
      (fun t _ => hd 1 t) (fun t ht => hf.ode t ht 1) (hinit 1)
      (fun t ht => ha t ⟨ht.1.le, ht.2.le⟩)
  have hx : ∀ t ∈ Icc 0 H, heldSolution R t bLo zLo 0 ≤ f t 0 := by
    exact derivative_comparison hH (hc 0) (hfc 0)
      (fun t _ => hd 0 t) (fun t ht => hf.ode t ht 0) (hinit 0)
      (fun t ht => hv t ⟨ht.1.le, ht.2.le⟩)
  intro t ht i
  fin_cases i
  · exact hx t ht
  · exact hv t ht
  · exact ha t ht

/-- Both closed-interval envelopes hold for every coordinate, including all
intermediate real times and both endpoints. -/
theorem coordinate_enclosure {H rlo rhi bLo bHi : ℝ} (hH : 0 ≤ H)
    {r b : ℝ → ℝ} {f : ℝ → State} {zLo zHi : State}
    (hrc : ContinuousOn r (Icc 0 H)) (hrlo0 : 0 < rlo)
    (hrlo : ∀ t ∈ Icc 0 H, rlo ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ rhi)
    (hblo : ∀ t ∈ Icc 0 H, bLo ≤ b t) (hbhi : ∀ t ∈ Icc 0 H, b t ≤ bHi)
    (hf : IsTrajectory H r b f)
    (hilo : ∀ i : Fin 3, zLo i ≤ f 0 i) (hihi : ∀ i : Fin 3, f 0 i ≤ zHi i) :
    ∀ t ∈ Icc 0 H, ∀ i : Fin 3,
      heldSolution (lowerRate rlo rhi (zLo 2) bLo) t bLo zLo i ≤ f t i ∧
      f t i ≤ heldSolution (upperRate rlo rhi (zHi 2) bHi) t bHi zHi i := by
  intro t ht i
  exact ⟨lower_flow_bound hH hrc hrlo0 hrlo hrhi hblo hf hilo t ht i,
    upper_flow_bound hH hrc hrlo0 hrlo hrhi hbhi hf hihi t ht i⟩

end LeanControls.VariableResponse
#print axioms LeanControls.VariableResponse.linear_comparison
#print axioms LeanControls.VariableResponse.derivative_comparison
#print axioms LeanControls.VariableResponse.upper_flow_bound
#print axioms LeanControls.VariableResponse.lower_flow_bound
#print axioms LeanControls.VariableResponse.coordinate_enclosure
