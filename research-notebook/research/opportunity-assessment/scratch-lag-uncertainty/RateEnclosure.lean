module
public import LeanControls.SaturatedLag
public import LeanControls.TravelGeometry
@[expose] public section
noncomputable section
namespace LagUncertaintySpike
abbrev State := Fin 3 → ℝ

/-- Exact held-command solution candidate for x'=v, v'=a, a'=r*(u-a).
The controller command u and rate r are fixed for this segment.
The exact_ode theorem below checks the actual differential equations. -/
def exactHeld (r h u : ℝ) (z : State) : State :=
  ![z 0 + h*z 1 + u*h^2/2 + (z 2-u)*(h/r-(1-Real.exp (-r*h))/r^2),
    z 1 + u*h + (z 2-u)*(1-Real.exp (-r*h))/r,
    u + (z 2-u)*Real.exp (-r*h)]

def polynomialHeld (r h u theta : ℝ) (z : State) : State :=
  ![z 0 + h*z 1 + u*h^2/2 + (z 2-u)*theta*h^2,
    z 1 + u*h + (z 2-u)*(h-theta*r*h^2),
    u + (z 2-u)*(1-r*h+theta*r^2*h^2)]

theorem exact_initial (r u : ℝ) (z : State) : exactHeld r 0 u z = z := by
  ext i
  fin_cases i <;> simp [exactHeld]

theorem held_eq_polynomial {r h theta : ℝ} (hr : r ≠ 0)
    (he : Real.exp (-r*h) = 1-r*h+theta*r^2*h^2) (u : ℝ) (z : State) :
    exactHeld r h u z = polynomialHeld r h u theta z := by
  ext i
  fin_cases i <;> dsimp [exactHeld, polynomialHeld] <;> rw [he] <;> field_simp <;> ring

/-- A single remainder parameter works for all state components and held commands.
This is an exact enclosure for the entire real parameter interval, not a grid. -/
theorem held_polynomial_enclosure {r h : ℝ} (hr0 : 0 < r) (hh0 : 0 ≤ h)
    (hrh : r*h ≤ 1) : ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      ∀ u z, exactHeld r h u z = polynomialHeld r h u theta z := by
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
theorem proposed_box_enclosure {r h : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hh0 : 0 ≤ h) (hhhi : h ≤ 1/5) :
    ∃ theta : ℝ, 0 ≤ theta ∧ theta ≤ 1 ∧
      ∀ u z, exactHeld r h u z = polynomialHeld r h u theta z := by
  apply held_polynomial_enclosure (by linarith) hh0
  nlinarith [mul_nonneg (show 0 ≤ 11/10-r by linarith) hh0]

/-- Checked derivative of the exact rate-dependent exponential. -/
theorem exp_rate_derivative (r t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-r*s)) (-r*Real.exp (-r*t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-r)).exp

/-- This derivative check establishes the actual held-input ODE, not only
an algebraic enclosure. The uncertainty rate is constant within the segment. -/
theorem exact_ode {r : ℝ} (hr : r ≠ 0) (u t : ℝ) (z : State) (i : Fin 3) :
    HasDerivAt (fun s => exactHeld r s u z i)
      (![exactHeld r t u z 1, exactHeld r t u z 2,
        r*(u-exactHeld r t u z 2)] i) t := by
  fin_cases i
  · convert ((((hasDerivAt_id t).mul_const (z 1)).const_add (z 0)).add
      ((((hasDerivAt_id t).pow 2).const_mul u).div_const 2)).add
      ((((hasDerivAt_id t).div_const r).sub
        (((exp_rate_derivative r t).const_sub 1).div_const (r^2))).const_mul
        (z 2-u)) using 1
    · rfl
    · dsimp [exactHeld]
      field_simp
  · convert (((hasDerivAt_id t).const_mul u).const_add (z 1)).add
      ((((exp_rate_derivative r t).const_sub 1).const_mul (z 2-u)).div_const r) using 1
    · rfl
    · dsimp [exactHeld]
      field_simp
  · convert ((exp_rate_derivative r t).const_mul (z 2-u)).const_add u using 1
    · rfl
    · dsimp [exactHeld]
      ring

/-- A tighter sector is valid on the SAME region; no gain or set changes. -/
theorem tighter_sector (z : State)
    (hz : LeanControls.BernsteinCertificate.energy
      LeanControls.Generated.TravelQuarterLower.P z ≤ 12) :
    (2/5:ℝ) * |LeanControls.SaturatedLag.input z| ≤ 1 := by
  have hb := LeanControls.TravelGeometry.request_energy z
  change (LeanControls.SaturatedLag.input z)^2 ≤ _ at hb
  have ha := sq_abs (LeanControls.SaturatedLag.input z)
  have hn := abs_nonneg (LeanControls.SaturatedLag.input z)
  nlinarith [sq_nonneg (|LeanControls.SaturatedLag.input z| - 5/2)]

/-- Exact final-budget arithmetic, conditional on the proposed decay and
response hypotheses. This does not assert those hypotheses for the plant. -/
theorem proposed_disturbance_budget :
    ((1/5:ℝ) + 1/(15/902)) * 16 * (1/100)^2 ≤ (15/902)*12 := by
  norm_num

/-- For an external jerk d OUTSIDE r*(u-a), rewrite it as command error d/r.
This is a distinct physical model and a distinct effective budget. -/
theorem outside_rate_error_budget {r e d : ℝ} (hr : 9/10 ≤ r)
    (hbudget : |e| + |d| ≤ 1/100) : |e| + |d| / r ≤ 1/90 := by
  have hd := div_le_div_of_nonneg_left (abs_nonneg d) (show (0:ℝ) < 9/10 by norm_num) hr
  calc
    |e| + |d| / r ≤ |e| + |d| / (9/10) := by linarith
    _ ≤ 1/90 := by nlinarith [abs_nonneg e]

theorem proposed_outside_rate_budget :
    ((1/5:ℝ) + 1/(15/902)) * 16 * (1/90)^2 ≤ (15/902)*12 := by
  norm_num

end LagUncertaintySpike
#print axioms LagUncertaintySpike.exact_initial
#print axioms LagUncertaintySpike.held_eq_polynomial
#print axioms LagUncertaintySpike.held_polynomial_enclosure
#print axioms LagUncertaintySpike.rate_bernstein_identity
#print axioms LagUncertaintySpike.rate_weights
#print axioms LagUncertaintySpike.proposed_box_enclosure

#print axioms LagUncertaintySpike.tighter_sector
#print axioms LagUncertaintySpike.proposed_disturbance_budget

#print axioms LagUncertaintySpike.exp_rate_derivative
#print axioms LagUncertaintySpike.exact_ode

#print axioms LagUncertaintySpike.outside_rate_error_budget
#print axioms LagUncertaintySpike.proposed_outside_rate_budget
