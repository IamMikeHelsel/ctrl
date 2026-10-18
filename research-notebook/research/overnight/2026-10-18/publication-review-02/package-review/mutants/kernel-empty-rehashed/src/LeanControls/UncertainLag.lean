module
public import LeanControls.SaturatedLag
public import LeanControls.TravelGeometry
public import LeanControls.UncertainResponse
public import LeanControls.Generated.UncertainA0L0R0
public import LeanControls.Generated.UncertainA0L0R1
public import LeanControls.Generated.UncertainA0L0R2
public import LeanControls.Generated.UncertainA0L1R0
public import LeanControls.Generated.UncertainA0L1R1
public import LeanControls.Generated.UncertainA0L1R2
public import LeanControls.Generated.UncertainA1L0R0
public import LeanControls.Generated.UncertainA1L0R1
public import LeanControls.Generated.UncertainA1L0R2
public import LeanControls.Generated.UncertainA1L1R0
public import LeanControls.Generated.UncertainA1L1R1
public import LeanControls.Generated.UncertainA1L1R2
@[expose] public section
noncomputable section
namespace LeanControls.UncertainLag
abbrev State := Fin 3 → ℝ

/-- Exact held-command solution for x'=v, v'=a, a'=r*(u-a).
The controller command u and rate r are fixed for this segment.
The exact_ode theorem below checks the actual differential equations.
The rate is not used in the fixed feedback gains. -/
def heldSolution (r h u : ℝ) (z : State) : State :=
  ![z 0 + h*z 1 + u*h^2/2 + (z 2-u)*(h/r-(1-Real.exp (-r*h))/r^2),
    z 1 + u*h + (z 2-u)*(1-Real.exp (-r*h))/r,
    u + (z 2-u)*Real.exp (-r*h)]

def polynomialHeld (r h u theta : ℝ) (z : State) : State :=
  ![z 0 + h*z 1 + u*h^2/2 + (z 2-u)*theta*h^2,
    z 1 + u*h + (z 2-u)*(h-theta*r*h^2),
    u + (z 2-u)*(1-r*h+theta*r^2*h^2)]

theorem exact_initial (r u : ℝ) (z : State) : heldSolution r 0 u z = z := by
  ext i
  fin_cases i <;> simp [heldSolution]

theorem held_eq_polynomial {r h theta : ℝ} (hr : r ≠ 0)
    (he : Real.exp (-r*h) = 1-r*h+theta*r^2*h^2) (u : ℝ) (z : State) :
    heldSolution r h u z = polynomialHeld r h u theta z := by
  ext i
  fin_cases i <;> dsimp [heldSolution, polynomialHeld] <;> rw [he] <;> field_simp <;> ring

/-- A single remainder parameter works for all state components and held commands.
This is an exact enclosure for the entire real parameter interval, not a grid. -/
theorem held_polynomial_enclosure {r h : ℝ} (hr0 : 0 < r) (hh0 : 0 ≤ h)
    (hrh : r*h ≤ 1) : ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      ∀ u z, heldSolution r h u z = polynomialHeld r h u theta z := by
  obtain ⟨theta, ht0, ht1, he⟩ := LeanControls.ActuatorLag.exp_interpolation
    (mul_nonneg hr0.le hh0) hrh
  refine ⟨theta, ht0, ht1, ?_⟩
  intro u z
  apply held_eq_polynomial (ne_of_gt hr0)
  convert he using 1 <;> ring

/-- Degree-two Bernstein interpolation: the middle coefficient need not equal
an actual plant at the midpoint. Keeping that distinction is essential. -/
theorem rate_bernstein_identity (lo hi q h u theta : ℝ) (z : State) :
    polynomialHeld ((1-q)*lo+q*hi) h u theta z =
      (1-q)^2 • polynomialHeld lo h u theta z +
      (2*q*(1-q)) • (2 • polynomialHeld ((lo+hi)/2) h u theta z -
        (1/2:ℝ) • (polynomialHeld lo h u theta z + polynomialHeld hi h u theta z)) +
      q^2 • polynomialHeld hi h u theta z := by
  ext i
  fin_cases i <;> simp [polynomialHeld, Pi.add_apply] <;> ring

theorem rate_weights {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (1-q)^2 ∧ 0 ≤ 2*q*(1-q) ∧ 0 ≤ q^2 ∧
    (1-q)^2 + 2*q*(1-q) + q^2 = 1 := by
  refine ⟨sq_nonneg _, mul_nonneg (by positivity) (by linarith), sq_nonneg _, ?_⟩
  ring

/-- The proposed rate/time box satisfies the exponential-enclosure side condition. -/
theorem held_box_enclosure {r h : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hh0 : 0 ≤ h) (hhhi : h ≤ 1/5) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      ∀ u z, heldSolution r h u z = polynomialHeld r h u theta z := by
  apply held_polynomial_enclosure (by linarith) hh0
  nlinarith [mul_nonneg (show 0 ≤ 11/10-r by linarith) hh0]

/-- Checked derivative of the exact rate-dependent exponential. -/
theorem exp_rate_derivative (r t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-r*s)) (-r*Real.exp (-r*t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-r)).exp

/-- This derivative check establishes the actual held-input ODE, not only
an algebraic enclosure. The uncertainty rate is constant within the segment. -/
theorem exact_ode {r : ℝ} (hr : r ≠ 0) (u t : ℝ) (z : State) (i : Fin 3) :
    HasDerivAt (fun s => heldSolution r s u z i)
      (![heldSolution r t u z 1, heldSolution r t u z 2,
        r*(u-heldSolution r t u z 2)] i) t := by
  fin_cases i
  · convert ((((hasDerivAt_id t).mul_const (z 1)).const_add (z 0)).add
      ((((hasDerivAt_id t).pow 2).const_mul u).div_const 2)).add
      ((((hasDerivAt_id t).div_const r).sub
        (((exp_rate_derivative r t).const_sub 1).div_const (r^2))).const_mul
        (z 2-u)) using 1
    · rfl
    · dsimp [heldSolution]
      field_simp
  · convert (((hasDerivAt_id t).const_mul u).const_add (z 1)).add
      ((((exp_rate_derivative r t).const_sub 1).const_mul (z 2-u)).div_const r) using 1
    · rfl
    · dsimp [heldSolution]
      field_simp
  · convert ((exp_rate_derivative r t).const_mul (z 2-u)).const_add u using 1
    · rfl
    · dsimp [heldSolution]
      ring


open Matrix BernsteinCertificate
abbrev P := Generated.TravelQuarterLower.P
abbrev input := SaturatedLag.input

/-- Actual exact response with one held command and a constant actuator rate. -/
def heldSegment (r t : ℝ) (z : State) (u : ℝ) : State := heldSolution r t u z

def vectorField (r u : ℝ) (current : State) : State :=
  ![current 1, current 2, r * (u-current 2)]

def nominalSegment (r t : ℝ) (z : State) (alpha : ℝ) : State :=
  heldSegment r t z (alpha * input z)

/-- w is a held command-equivalent disturbance INSIDE the rate multiplier.
This is not an external jerk or a force applied directly to velocity. -/
def segment (r t : ℝ) (z : State) (w : ℝ) : State :=
  heldSegment r t z (RobustPD.saturate 1 (input z) + w)

def response (r t : ℝ) : State :=
  ![t^2/2-t/r+(1-Real.exp (-r*t))/r^2,
    t-(1-Real.exp (-r*t))/r, 1-Real.exp (-r*t)]

theorem heldSegment_zero (r : ℝ) (z : State) (u : ℝ) : heldSegment r 0 z u = z :=
  exact_initial r u z

theorem segment_zero (r : ℝ) (z : State) (w : ℝ) : segment r 0 z w = z :=
  heldSegment_zero r z _

theorem response_zero (r : ℝ) : response r 0 = 0 := by
  ext i
  fin_cases i <;> simp [response]

theorem heldSegment_ode {r : ℝ} (hr : r ≠ 0) (t : ℝ) (z : State) (u : ℝ)
    (i : Fin 3) : HasDerivAt (fun s => heldSegment r s z u i)
      (vectorField r u (heldSegment r t z u) i) t :=
  exact_ode hr u t z i

theorem segment_ode {r : ℝ} (hr : r ≠ 0) (t : ℝ) (z : State) (w : ℝ)
    (i : Fin 3) : HasDerivAt (fun s => segment r s z w i)
      (vectorField r (RobustPD.saturate 1 (input z)+w) (segment r t z w) i) t :=
  heldSegment_ode hr t z _ i

theorem heldSegment_add_input (r t : ℝ) (z : State) (u w : ℝ) :
    heldSegment r t z (u+w) = heldSegment r t z u + w • response r t := by
  ext i
  fin_cases i <;> simp [heldSegment, heldSolution, response, Pi.add_apply] <;> ring

theorem segment_eq_nominal_add_response (r t : ℝ) (z : State) (w alpha : ℝ)
    (ha : RobustPD.saturate 1 (input z) = alpha * input z) :
    segment r t z w = nominalSegment r t z alpha + w • response r t := by
  unfold segment nominalSegment
  rw [ha, heldSegment_add_input]

/-- The same original ellipsoid admits the tighter sector; it still contains
actively clipped states. No controller retuning or region shrink is used. -/
theorem region_sector_bound (z : State) (hz : energy P z ≤ 12) :
    (2/5:ℝ) * |input z| ≤ 1 := by
  have hb := TravelGeometry.request_energy z
  change (input z)^2 ≤ _ at hb
  have ha := sq_abs (input z)
  have hn := abs_nonneg (input z)
  nlinarith [sq_nonneg (|input z| - 5/2)]

theorem tighter_sector (z : State) (hz : energy P z ≤ 12) :
    (2/5:ℝ) * |input z| ≤ 1 := region_sector_bound z hz

theorem segment_sector_decomposition (r : ℝ) (z : State)
    (hrequest : (2/5:ℝ) * |input z| ≤ 1) :
    ∃ alpha : ℝ, 2/5 ≤ alpha ∧ alpha ≤ 1 ∧
      ∀ t w, segment r t z w = nominalSegment r t z alpha + w • response r t := by
  obtain ⟨alpha, ha0, ha1, ha⟩ := SaturationSector.exists_sector_gain
    (U := 1) (kappa := 2/5) (u := input z)
    (by norm_num) (by norm_num) (by norm_num) hrequest
  exact ⟨alpha, ha0, ha1, fun t w => segment_eq_nominal_add_response r t z w alpha ha⟩

/-- One common Taylor remainder gives the exact elapsed-time-scaled response. -/
theorem response_polynomial_enclosure {r t : ℝ} (hrlo : 9/10 ≤ r)
    (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      response r t = t • ![(1/2-theta)*t, theta*r*t, r-theta*r^2*t] := by
  obtain ⟨theta, htlo, hthi', he⟩ := ActuatorLag.exp_interpolation
    (mul_nonneg (by linarith) ht0)
    (show r*t ≤ 1 by nlinarith [mul_nonneg (show 0 ≤ 11/10-r by linarith) ht0])
  have hr : r ≠ 0 := ne_of_gt (show 0 < r by linarith)
  have he' : Real.exp (-r*t) = 1-r*t+theta*r^2*t^2 := by
    convert he using 1 <;> ring
  refine ⟨theta, htlo, hthi', ?_⟩
  ext i
  fin_cases i <;> dsimp [response] <;> rw [he'] <;> field_simp <;> ring

/-- Polynomial nominal enclosure, preserving the same held gain in all coordinates. -/
def polynomialNominal (r t : ℝ) (z : State) (alpha theta : ℝ) : State :=
  polynomialHeld r t (alpha * input z) theta z

/-- Three Bernstein coefficients in rate: the middle coefficient is not an
actual midpoint plant. -/
def rateVertex (j : Fin 3) (t : ℝ) (z : State) (alpha theta : ℝ) : State :=
  ![polynomialNominal (9/10) t z alpha theta,
    2 • polynomialNominal 1 t z alpha theta - (1/2:ℝ) •
      (polynomialNominal (9/10) t z alpha theta + polynomialNominal (11/10) t z alpha theta),
    polynomialNominal (11/10) t z alpha theta] j

def sectorEndpoint (a : Fin 2) : ℝ := ![2/5,1] a

def remainderEndpoint (l : Fin 2) : ℝ := ![0,1] l

def certificateTransition (a l : Fin 2) (j : Fin 3) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![![Generated.UncertainA0L0R0.transition t, Generated.UncertainA0L0R1.transition t, Generated.UncertainA0L0R2.transition t], ![Generated.UncertainA0L1R0.transition t, Generated.UncertainA0L1R1.transition t, Generated.UncertainA0L1R2.transition t]], ![![Generated.UncertainA1L0R0.transition t, Generated.UncertainA1L0R1.transition t, Generated.UncertainA1L0R2.transition t], ![Generated.UncertainA1L1R0.transition t, Generated.UncertainA1L1R1.transition t, Generated.UncertainA1L1R2.transition t]]] a l j

set_option maxHeartbeats 2000000 in
/-- All twelve prepared polynomial matrices match the exact enclosure
coefficients. This identity is independent of the search script. -/
theorem vertex_identity (a l : Fin 2) (j : Fin 3) (t : ℝ) (z : State) :
    rateVertex j t z (sectorEndpoint a) (remainderEndpoint l) =
      certificateTransition a l j t *ᵥ z := by
  ext i
  fin_cases a <;> fin_cases l <;> fin_cases j <;> fin_cases i <;>
    simp [rateVertex, polynomialNominal, polynomialHeld, input, SaturatedLag.input,
      sectorEndpoint, remainderEndpoint, certificateTransition,
      Generated.UncertainA0L0R0.transition, Generated.UncertainA0L0R1.transition, Generated.UncertainA0L0R2.transition, Generated.UncertainA0L1R0.transition, Generated.UncertainA0L1R1.transition, Generated.UncertainA0L1R2.transition, Generated.UncertainA1L0R0.transition, Generated.UncertainA1L0R1.transition, Generated.UncertainA1L0R2.transition, Generated.UncertainA1L1R0.transition, Generated.UncertainA1L1R1.transition, Generated.UncertainA1L1R2.transition,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply] <;> ring

theorem vertex_energy_decrease (a l : Fin 2) (j : Fin 3) {t : ℝ}
    (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) (z : State) :
    energy P (rateVertex j t z (sectorEndpoint a) (remainderEndpoint l)) ≤
      energy P z - (3/2)*t*squaredNorm z := by
  rw [vertex_identity]
  fin_cases a <;> fin_cases l <;> fin_cases j
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L0R0.P, mul_comm] using
      Generated.UncertainA0L0R0.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L0R1.P, mul_comm] using
      Generated.UncertainA0L0R1.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L0R2.P, mul_comm] using
      Generated.UncertainA0L0R2.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L1R0.P, mul_comm] using
      Generated.UncertainA0L1R0.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L1R1.P, mul_comm] using
      Generated.UncertainA0L1R1.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA0L1R2.P, mul_comm] using
      Generated.UncertainA0L1R2.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L0R0.P, mul_comm] using
      Generated.UncertainA1L0R0.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L0R1.P, mul_comm] using
      Generated.UncertainA1L0R1.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L0R2.P, mul_comm] using
      Generated.UncertainA1L0R2.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L1R0.P, mul_comm] using
      Generated.UncertainA1L1R0.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L1R1.P, mul_comm] using
      Generated.UncertainA1L1R1.certified_decrease ht0 hthi z
  · simpa [certificateTransition, P, Generated.TravelQuarterLower.P, Generated.UncertainA1L1R2.P, mul_comm] using
      Generated.UncertainA1L1R2.certified_decrease ht0 hthi z

/-- Convex response enclosure transferred to the exact exponential response. -/
theorem response_energy_bound {r t : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) : energy P (response r t) ≤ 16*t^2 := by
  obtain ⟨theta, htlo, hthi', he⟩ := response_polynomial_enclosure hrlo hrhi ht0 hthi
  rw [he]
  exact UncertainResponse.scaled_response_energy_bound hrlo hrhi htlo hthi' ht0 hthi

theorem disturbance_energy_of_abs_le {r t w W : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (hw : |w| ≤ W) : energy P (w • response r t) ≤ 16*t^2*W^2 := by
  obtain ⟨theta, htlo, hthi', he⟩ := response_polynomial_enclosure hrlo hrhi ht0 hthi
  rw [he]
  exact UncertainResponse.disturbance_energy_of_abs_le hrlo hrhi htlo hthi' ht0 hthi hw

/-- The polynomial state is a nested convex combination of its three rate
coefficients. The identity holds for every real rate; interval bounds are used
only when establishing nonnegativity of the mixing weights. -/
theorem polynomial_rate_interpolation (r t : ℝ) (z : State) (alpha theta : ℝ) :
    polynomialNominal r t z alpha theta =
      (1-(5*r-9/2)) • ((1-(5*r-9/2)) • rateVertex 0 t z alpha theta +
        (5*r-9/2) • rateVertex 1 t z alpha theta) +
      (5*r-9/2) • ((1-(5*r-9/2)) • rateVertex 1 t z alpha theta +
        (5*r-9/2) • rateVertex 2 t z alpha theta) := by
  ext i
  fin_cases i <;> simp [polynomialNominal, polynomialHeld, rateVertex, Pi.add_apply] <;> ring

/-- Both remainder endpoints and both gain endpoints are uniformly certified
for every rate in the box and every elapsed time in the sampling interval. -/
theorem polynomial_endpoint_energy_decrease (a l : Fin 2) {r t : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (z : State) :
    energy P (polynomialNominal r t z (sectorEndpoint a) (remainderEndpoint l)) ≤
      energy P z - (3/2)*t*squaredNorm z := by
  have hq0 : 0 ≤ 5*r-9/2 := by linarith
  have hq1 : 5*r-9/2 ≤ 1 := by linarith
  have hv := fun j => vertex_energy_decrease a l j ht0 hthi z
  rw [polynomial_rate_interpolation]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ hq0 hq1
  · exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ hq0 hq1 (hv 0) (hv 1)
  · exact VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ hq0 hq1 (hv 1) (hv 2)

theorem polynomial_remainder_interpolation (r t : ℝ) (z : State) (alpha theta : ℝ) :
    polynomialNominal r t z alpha theta =
      (1-theta) • polynomialNominal r t z alpha 0 +
      theta • polynomialNominal r t z alpha 1 := by
  ext i
  fin_cases i <;> simp [polynomialNominal, polynomialHeld, Pi.add_apply] <;> ring

theorem polynomial_gain_interpolation (r t : ℝ) (z : State) (alpha theta : ℝ) :
    polynomialNominal r t z alpha theta =
      (1-(5*alpha-2)/3) • polynomialNominal r t z (2/5) theta +
      ((5*alpha-2)/3) • polynomialNominal r t z 1 theta := by
  ext i
  fin_cases i <;> simp [polynomialNominal, polynomialHeld, Pi.add_apply] <;> ring

/-- Three nested convexity arguments combine all twelve certified vertices. -/
theorem polynomial_energy_decrease {r t alpha theta : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (ha0 : 2/5 ≤ alpha) (ha1 : alpha ≤ 1) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (z : State) : energy P (polynomialNominal r t z alpha theta) ≤
      energy P z - (3/2)*t*squaredNorm z := by
  have hb0 : 0 ≤ (5*alpha-2)/3 := by linarith
  have hb1 : (5*alpha-2)/3 ≤ 1 := by linarith
  rw [polynomial_gain_interpolation]
  apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd _ _ hb0 hb1
  · rw [polynomial_remainder_interpolation]
    apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ htheta0 htheta1
    · simpa [sectorEndpoint, remainderEndpoint] using
        polynomial_endpoint_energy_decrease 0 0 hrlo hrhi ht0 hthi z
    · simpa [sectorEndpoint, remainderEndpoint] using
        polynomial_endpoint_energy_decrease 0 1 hrlo hrhi ht0 hthi z
  · rw [polynomial_remainder_interpolation]
    apply VertexCertificate.shared_bound P Generated.TravelQuarterLower.P_psd
      _ _ htheta0 htheta1
    · simpa [sectorEndpoint, remainderEndpoint] using
        polynomial_endpoint_energy_decrease 1 0 hrlo hrhi ht0 hthi z
    · simpa [sectorEndpoint, remainderEndpoint] using
        polynomial_endpoint_energy_decrease 1 1 hrlo hrhi ht0 hthi z

/-- Exact exponential plant, all allowed rates and held sector gains, and every
elapsed time including zero. The feedback gains do not depend on the rate. -/
theorem nominal_energy_decrease {r t alpha : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (ha0 : 2/5 ≤ alpha) (ha1 : alpha ≤ 1) (z : State) :
    energy P (nominalSegment r t z alpha) ≤ energy P z - (3/2)*t*squaredNorm z := by
  obtain ⟨theta, htlo, hthi', he⟩ := held_box_enclosure hrlo hrhi ht0 hthi
  have he' : nominalSegment r t z alpha = polynomialNominal r t z alpha theta :=
    he (alpha*input z) z
  rw [he']
  exact polynomial_energy_decrease hrlo hrhi ht0 hthi ha0 ha1 htlo hthi' z

/-- Uniform contraction in the common energy, ready for elapsed-time-scaled
perturbation composition. No disturbance is included in this nominal statement. -/
theorem nominal_contraction {r t alpha : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (ha0 : 2/5 ≤ alpha) (ha1 : alpha ≤ 1) (z : State) :
    energy P (nominalSegment r t z alpha) ≤ (1-2*t*(15/902))*energy P z := by
  have hd := nominal_energy_decrease hrlo hrhi ht0 hthi ha0 ha1 z
  have hu := (Generated.TravelQuarterLower.certified_energy_bounds z).2
  norm_num [Generated.TravelQuarterLower.upperBound] at hu
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ t*(15/451) by positivity)
  nlinarith only [hd, hm]

end LeanControls.UncertainLag
