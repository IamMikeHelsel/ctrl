module
public import ScaledTracking
public import FrozenReference
@[expose] public section
noncomputable section
namespace LeanControls.DirectReference
open Set Polynomial
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking

/-- Position, velocity and acceleration are exact derivatives of the frozen
position polynomial. Local time starts at zero in each phase. -/
def reference (k : ℕ) (t : ℝ) : State :=
  ![(position k).eval t, (position k).derivative.eval t,
    (position k).derivative.derivative.eval t]

def jerk (k : ℕ) (t : ℝ) : ℝ :=
  (position k).derivative.derivative.derivative.eval t

theorem duration_positive (k : ℕ) (hk : k < 8) : 0 < duration k := by
  interval_cases k <;> norm_num [duration]

theorem phase_times_match (k : ℕ) (hk : k+1 < 8) :
    phaseStart (k+1) = phaseStart k + duration k := by
  have : k ≤ 6 := by omega
  interval_cases k <;> norm_num [phaseStart, duration]

theorem final_time : phaseStart 7 + duration 7 = (3/2 : ℝ) := by
  norm_num [phaseStart, duration]

theorem reference_continuous (k : ℕ) : Continuous (reference k) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [reference] using (position k).continuous
  · simpa [reference] using (position k).derivative.continuous
  · simpa [reference] using (position k).derivative.derivative.continuous

/-- These are the actual polynomial derivative identities, not extra
assumptions on an opaque reference. They hold even beyond a phase's interval. -/
theorem reference_derivatives (k : ℕ) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => reference k s i)
      (![reference k t 1,reference k t 2,jerk k t] i) t := by
  fin_cases i
  · simpa [reference] using (position k).hasDerivAt t
  · simpa [reference] using (position k).derivative.hasDerivAt t
  · simpa [reference, jerk] using (position k).derivative.derivative.hasDerivAt t

theorem reference_initial : reference 0 0 = ![0,0,0] := by
  ext i
  fin_cases i <;> norm_num [reference, position, derivative_C_mul_X_pow]

theorem initial_jerk : jerk 0 0 = 10 := by
  norm_num [jerk, position, derivative_C_mul_X_pow]

theorem reference_matches (k : ℕ) (hk : k+1 < 8) :
    reference (k+1) 0 = reference k (duration k) := by
  have : k ≤ 6 := by omega
  interval_cases k <;> ext i <;> fin_cases i <;>
    norm_num [reference, position, duration, derivative_C_mul_X_pow]

theorem jerk_matches (k : ℕ) (hk : k+1 < 8) :
    jerk (k+1) 0 = jerk k (duration k) := by
  have : k ≤ 6 := by omega
  interval_cases k <;> norm_num [jerk, position, duration, derivative_C_mul_X_pow]

theorem reference_endpoint : reference 7 (duration 7) = ![3/5,0,0] := by
  ext i
  fin_cases i <;> norm_num [reference, position, duration]

/-- The standard scalar identity used to bound the brake's jerk. -/
theorem brake_shape_bound {z : ℝ} (hz : 0 ≤ z) :
    z^2*(1-4*z) ≤ (1/108 : ℝ) := by
  have hp := mul_nonneg (sq_nonneg (z-1/6)) (by linarith : 0 ≤ 4*z+1/3)
  nlinarith

theorem brake_jerk_bound {t : ℝ} (ht : t ∈ Icc 0 (7/10 : ℝ)) :
    |jerk 6 t| ≤ 10 := by
  let y : ℝ := t/(7/10)
  let z : ℝ := y*(1-y)
  have hy0 : 0 ≤ y := div_nonneg ht.1 (by norm_num)
  have hy1 : y ≤ 1 := by dsimp [y]; linarith [ht.2]
  have hz : 0 ≤ z := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  have hb := brake_shape_bound hz
  have heq : (jerk 6 t)^2 = (115068529/12544 : ℝ)*z^2*(1-4*z) := by
    norm_num [jerk, position, derivative_C_mul_X_pow]
    dsimp [z, y]
    ring
  have hs : (jerk 6 t)^2 ≤ (115068529/1354752 : ℝ) := by
    rw [heq]
    nlinarith
  have habs : |jerk 6 t|^2 ≤ (115068529/1354752 : ℝ) := by simpa using hs
  nlinarith [abs_nonneg (jerk 6 t)]

theorem jerk_bound (k : ℕ) (hk : k < 8) (t : ℝ) (ht : t ∈ Icc 0 (duration k)) :
    |jerk k t| ≤ 10 := by
  interval_cases k
  all_goals try { exact brake_jerk_bound (by simpa [duration] using ht) }
  all_goals norm_num [jerk, position, duration, derivative_C_mul_X_pow] at ht ⊢
  all_goals apply abs_le.mpr; constructor <;> linarith

/-- Supplied physical trajectories. The ODE holds on each open phase; state
continuity holds on its closed interval and at every join. Existence is not
asserted for arbitrary rate or disturbance functions. -/
structure DirectPlant (f : ℕ → ℝ → State) (r w : ℕ → ℝ → ℝ) : Prop where
  trajectory : ∀ k < 8, IsTrajectory (duration k) (r k)
    (fun t => physicalInput 10 (f k) (reference k) (jerk k) t + w k t) (f k)
  rate_lower : ∀ k < 8, ∀ t ∈ Icc 0 (duration k), 80 ≤ r k t
  rate_upper : ∀ k < 8, ∀ t ∈ Icc 0 (duration k), r k t ≤ 120
  disturbance : ∀ k < 8, ∀ t ∈ Icc 0 (duration k), |w k t| ≤ 1/100
  matched : ∀ k, k+1 < 8 → f (k+1) 0 = f k (duration k)
  initial : f 0 0 = ![0,0,0]

/-- The concrete reference facts discharge every reference hypothesis in the
finite-replan tracking theorem. Only the physical trajectories are supplied. -/
theorem direct_cube {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (h : DirectPlant f r w) :
    ∀ k < 8, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (scaledError 10 (f k) (reference k) t) i| ≤ 1/5000 := by
  apply finite_replans_scaled (σ := 10) (W := 1/100) (J := 10)
    (by norm_num) (by norm_num)
    (fun k hk => (duration_positive k hk).le) h.trajectory
    (fun k _ => (reference_continuous k).continuousOn)
    (fun k _ t _ i => reference_derivatives k t i)
    (by convert h.rate_lower using 1; norm_num)
    (by convert h.rate_upper using 1; norm_num)
    h.disturbance jerk_bound illustrative_budget h.matched reference_matches
  intro i
  fin_cases i <;> norm_num [coordinates, scaledError, scaleState, error,
    h.initial, reference_initial]

theorem direct_tracking {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (h : DirectPlant f r w) (k : ℕ) (hk : k < 8)
    (t : ℝ) (ht : t ∈ Icc 0 (duration k)) :
    |f k t 0-reference k t 0| ≤ 1/5000 ∧
    |f k t 1-reference k t 1| ≤ 2/125 ∧
    |f k t 2-reference k t 2| ≤ 32/25 := by
  obtain ⟨hx,hv,ha,_⟩ := scaled_cube_physical_bounds (by norm_num : (0 : ℝ) < 10)
    (direct_cube h k hk t ht)
  norm_num [error] at hx hv ha
  exact ⟨hx,hv,ha⟩

/-- At a join the left phase is selected. Proved matching makes either side
the same state. This convention also fixes the supplied trajectory evaluation. -/
def phaseIndex (t : ℝ) : ℕ :=
  if t ≤ 1/4 then 0 else if t ≤ 51/200 then 1 else
  if t ≤ 61/200 then 2 else if t ≤ 219/400 then 3 else
  if t ≤ 229/400 then 4 else if t ≤ 5235077/7508900 then 5 else
  if t ≤ 10491307/7508900 then 6 else 7

def atTime (f : ℕ → ℝ → State) (t : ℝ) : State :=
  f (phaseIndex t) (t-phaseStart (phaseIndex t))

theorem phaseIndex_valid (t : ℝ) : phaseIndex t < 8 := by
  unfold phaseIndex
  split_ifs <;> norm_num

theorem phaseIndex_local {t : ℝ} (ht : t ∈ Icc 0 (3/2 : ℝ)) :
    t-phaseStart (phaseIndex t) ∈ Icc 0 (duration (phaseIndex t)) := by
  unfold phaseIndex
  split_ifs <;> norm_num [phaseStart, duration, mem_Icc] <;> constructor <;> linarith [ht.1,ht.2]

/-- The local intervals cover every physical time through the fixed deadline. -/
theorem all_time_tracking {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (h : DirectPlant f r w) {t : ℝ} (ht : t ∈ Icc 0 (3/2 : ℝ)) :
    |atTime f t 0-atTime reference t 0| ≤ 1/5000 ∧
    |atTime f t 1-atTime reference t 1| ≤ 2/125 ∧
    |atTime f t 2-atTime reference t 2| ≤ 32/25 :=
  direct_tracking h (phaseIndex t) (phaseIndex_valid t)
    (t-phaseStart (phaseIndex t)) (phaseIndex_local ht)

theorem final_reference : atTime reference (3/2) = ![3/5,0,0] := by
  ext i
  fin_cases i <;> norm_num [atTime, phaseIndex, phaseStart, reference, position]

/-- The actual endpoint has a position tolerance and coarse residual bounds.
The nonzero velocity/acceleration bounds are not a physical stopping claim. -/
theorem actual_endpoint {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (h : DirectPlant f r w) :
    |atTime f (3/2) 0-3/5| ≤ 1/5000 ∧
    |atTime f (3/2) 1| ≤ 2/125 ∧ |atTime f (3/2) 2| ≤ 32/25 := by
  have ht := all_time_tracking h (t := 3/2) ⟨by norm_num,le_rfl⟩
  simpa [final_reference] using ht

theorem brake_velocity_nonnegative {t : ℝ} (ht : t ∈ Icc 0 (7/10 : ℝ)) :
    0 ≤ reference 6 t 1 := by
  let y : ℝ := t/(7/10)
  have hy0 : 0 ≤ y := div_nonneg ht.1 (by norm_num)
  have hy1 : y ≤ 1 := by dsimp [y]; linarith [ht.2]
  have heq : reference 6 t 1 = (75089/96000 : ℝ)*(1-y)^3*(1+3*y+6*y^2) := by
    norm_num [reference, position, derivative_C_mul_X_pow]
    dsimp [y]
    ring
  rw [heq]
  have : 0 ≤ 1-y := by linarith
  positivity

theorem reference_velocity_nonnegative (k : ℕ) (hk : k < 8) (t : ℝ)
    (ht : t ∈ Icc 0 (duration k)) : 0 ≤ reference k t 1 := by
  interval_cases k
  all_goals try { exact brake_velocity_nonnegative (by simpa [duration] using ht) }
  all_goals norm_num [reference, position, duration, derivative_C_mul_X_pow] at ht ⊢
  all_goals nlinarith [sq_nonneg t, mul_nonneg ht.1 (sq_nonneg t),
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2),
    mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

theorem phase_position_endpoints (k : ℕ) (hk : k < 8) :
    0 ≤ reference k 0 0 ∧ reference k (duration k) 0 ≤ 3/5 := by
  interval_cases k <;> norm_num [reference, position, duration]

/-- The stated corridor is proved for the reference. -/
theorem reference_corridor (k : ℕ) (hk : k < 8) (t : ℝ)
    (ht : t ∈ Icc 0 (duration k)) : reference k t 0 ∈ Icc 0 (3/5 : ℝ) := by
  have hm : MonotoneOn (fun t => reference k t 0) (Icc 0 (duration k)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((continuous_apply 0).comp (reference_continuous k)).continuousOn
    · intro x hx
      exact (reference_derivatives k x 0).differentiableAt.differentiableWithinAt
    · intro x hx
      change 0 ≤ deriv (fun s => reference k s 0) x
      rw [(reference_derivatives k x 0).deriv]
      exact reference_velocity_nonnegative k hk x
        (Ioo_subset_Icc_self (by simpa only [interior_Icc] using hx))
  have hends := phase_position_endpoints k hk
  have hD := (duration_positive k hk).le
  exact ⟨hends.1.trans (hm ⟨le_rfl,hD⟩ ht ht.1),
    (hm ht ⟨hD,le_rfl⟩ ht.2).trans hends.2⟩

/-- A nonzero tracking tube gives an enlarged actual corridor, including a
small possible overshoot past the reference's 0.6 m endpoint. -/
theorem actual_enlarged_corridor {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (h : DirectPlant f r w) {t : ℝ} (ht : t ∈ Icc 0 (3/2 : ℝ)) :
    atTime f t 0 ∈ Icc (-1/5000 : ℝ) (3001/5000 : ℝ) := by
  have hc := reference_corridor (phaseIndex t) (phaseIndex_valid t)
    (t-phaseStart (phaseIndex t)) (phaseIndex_local ht)
  change atTime reference t 0 ∈ Icc 0 (3/5 : ℝ) at hc
  obtain ⟨hl,hu⟩ := abs_le.mp (all_time_tracking h ht).1
  exact ⟨by linarith [hc.1],by linarith [hc.2]⟩

end LeanControls.DirectReference
