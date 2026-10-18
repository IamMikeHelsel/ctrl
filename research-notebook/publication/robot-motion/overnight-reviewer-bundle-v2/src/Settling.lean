module
public import ScaledTracking
@[expose] public section
noncomputable section
namespace LeanControls.Settling
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking

/-- Unequal transient widths give strict contraction in all three coordinates. -/
def weight : Fin 3 → ℝ := ![1, 9/10, 4/5]

theorem weight_pos (i : Fin 3) : 0 < weight i := by
  fin_cases i <;> norm_num [weight]

theorem weight_le_one (i : Fin 3) : weight i ≤ 1 := by
  fin_cases i <;> norm_num [weight]

/-- A moving box has a fixed disturbance part and a decaying transient part. -/
def radius (W C t : ℝ) (i : Fin 3) : ℝ :=
  3*W/8 + weight i * C * Real.exp (-(2/5)*t)

/-- Face inequality derived directly from the transformed actual plant. -/
theorem shrinking_face {W F K r w : ℝ} {z : State}
    (hW : 0 ≤ W) (hF : 3*W/8 ≤ F) (hK : 0 ≤ K)
    (hlo : 8 ≤ r) (hhi : r ≤ 12) (hw : |w| ≤ W)
    (hz : ∀ i, |z i| ≤ F + weight i * K) (i : Fin 3) :
    (z i = F + weight i*K → transformedRHS r w z i ≤ -(2/5)*weight i*K) ∧
    (z i = -(F + weight i*K) → -transformedRHS r w z i ≤ -(2/5)*weight i*K) := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have hww := abs_le.mp hw
  have hF0 : 0 ≤ F := by linarith
  norm_num [weight] at h0 h1 h2
  fin_cases i
  · norm_num [weight, transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight, transformedRHS]
    constructor <;> intro he <;> rw [he] <;> linarith
  · norm_num [weight, transformedRHS]
    have p0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 0+F+K by linarith)
    have p1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ F+9/10*K-z 1 by linarith)
    have n0 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ F+K-z 0 by linarith)
    have n1 := mul_nonneg (show 0 ≤ r-8 by linarith) (show 0 ≤ z 1+F+9/10*K by linarith)
    have pw := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ W-w by linarith)
    have nw := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ W+w by linarith)
    have prF := mul_nonneg (show 0 ≤ 12-r by linarith) hF0
    have prW := mul_nonneg (show 0 ≤ 12-r by linarith) hW
    have prK := mul_nonneg (show 0 ≤ 12-r by linarith) hK
    constructor <;> intro he <;> rw [he] <;> nlinarith

/-- Conditional on a classical trajectory, arbitrary pointwise rate changes
preserve this shrinking box. No bound on the rate derivative is required. -/
theorem transformed_settling {H W C : ℝ} (hH : 0 ≤ H) (hW : 0 ≤ W) (hC : 0 ≤ C)
    {r w : ℝ → ℝ} {z : ℝ → State}
    (hc : ∀ i, ContinuousOn (fun t => z t i) (Icc 0 H))
    (hd : ∀ i t, t ∈ Ioo 0 H → HasDerivAt (fun s => z s i)
      (transformedRHS (r t) (w t) (z t) i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hi : ∀ i, |z 0 i| ≤ radius W C 0 i) :
    ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ radius W C t i := by
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ radius W C t i + ε*(1+t) := by
    let K : ℝ → ℝ := fun t => C * Real.exp (-(2/5)*t)
    let B : Fin 3 → ℝ → ℝ := fun i t => radius W C t i + ε*(1+t)
    let dB : Fin 3 → ℝ → ℝ := fun i t => -(2/5)*weight i*K t + ε
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1) - B p.1 t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r t) (w t) (z t) p.1
       else -transformedRHS (r t) (w t) (z t) p.1) - dB p.1 t
    have hBc (i : Fin 3) : Continuous (B i) := by dsimp [B, radius]; fun_prop
    have hBd (i : Fin 3) (t : ℝ) : HasDerivAt (B i) (dB i t) t := by
      have he := (((hasDerivAt_id t).const_mul (-(2/5):ℝ)).exp).const_mul (weight i*C)
      convert (he.const_add (3*W/8)).add (((hasDerivAt_id t).const_add 1).const_mul ε) using 1 <;>
        (try funext u) <;> dsimp [B, dB, radius, K] <;> ring
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivAt (y p) (dy p t) t := by
      obtain ⟨i,b⟩ := p
      cases b
      · exact (hd i t ht).neg.sub (hBd i t)
      · exact (hd i t ht).sub (hBd i t)
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      cases b <;> dsimp [y,B] <;> linarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H) (hall : ∀ p, y p t ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hK : 0 ≤ K t := mul_nonneg hC (Real.exp_pos _).le
      have hF : 3*W/8 ≤ 3*W/8+ε*(1+t) := by nlinarith [ht.1]
      have hzt (i : Fin 3) : |z t i| ≤ (3*W/8+ε*(1+t)) + weight i*K t := by
        have hp := hall (i,true)
        have hn := hall (i,false)
        dsimp [y,B,radius,K] at hp hn ⊢
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      obtain ⟨i,b⟩ := p
      have hface := shrinking_face hW hF hK (hrlo t htc) (hrhi t htc) (hw t htc) hzt i
      cases b
      · have hzi : z t i = -((3*W/8+ε*(1+t))+weight i*K t) := by
          dsimp [y,B,radius,K] at he ⊢; linarith
        have hh := hface.2 hzi
        dsimp [dy,dB]
        linarith
      · have hzi : z t i = (3*W/8+ε*(1+t))+weight i*K t := by
          dsimp [y,B,radius,K] at he ⊢; linarith
        have hh := hface.1 hzi
        dsimp [dy,dB]
        linarith
    have hbar := finite_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,B] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hdpos : 0 < 1+t := by linarith [ht.1]
  have heq : ε/(1+t)*(1+t) = ε := div_mul_cancel₀ ε (ne_of_gt hdpos)
  simpa only [heq] using inflated (ε/(1+t)) (div_pos hε hdpos) t ht i

/-- The transformed ODE is a consequence of the supplied physical trajectory. -/
theorem actual_settling {H W C c : ℝ} (hH : 0 ≤ H) (hW : 0 ≤ W) (hC : 0 ≤ C)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => command c (f t)+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ radius W C 0 i) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates c (f t) i| ≤ radius W C t i := by
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc (i : Fin 3) : ContinuousOn (fun t => coordinates c (f t) i) (Icc 0 H) := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop
  exact transformed_settling hH hW hC hc
    (fun i t ht => coordinates_ode hf t ht i) hrlo hrhi hw hi

/-- Physical holding feedback with time scale sigma. -/
def holdInput (σ c : ℝ) (f : ℝ → State) (t : ℝ) : ℝ :=
  σ^2 * command c (scaleState σ (f t))

/-- This is the same direct controller when the reference has finished. -/
theorem finished_reference_input {σ : ℝ} (hσ : 0 < σ)
    (c : ℝ) (f : ℝ → State) (t : ℝ) :
    physicalInput σ f (fun _ => ![c,0,0]) (fun _ => 0) t = holdInput σ c f t := by
  dsimp [physicalInput, holdInput, command, scaleState]
  field_simp
  ring

/-- A shrinking bound in physical seconds. The disturbance retains its units
of acceleration target, and the rate can change anywhere within its band. -/
theorem actual_settling_scaled {σ H W C c : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hW : 0 ≤ W) (hC : 0 ≤ C)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput σ c f t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hi : ∀ i, |coordinates c (scaleState σ (f 0)) i| ≤ radius (W/σ^2) C 0 i) :
    ∀ t ∈ Icc 0 H, ∀ i,
      |coordinates c (scaleState σ (f t)) i| ≤ radius (W/σ^2) C (σ*t) i := by
  have hn : IsTrajectory (σ*H) (fun τ => r (τ/σ)/σ)
      (fun τ => command c (normalize σ f τ)+w (τ/σ)/σ^2) (normalize σ f) := by
    convert normalize_trajectory hσ hf using 1
    funext τ
    dsimp [holdInput,ScaledTracking.normalize]
    field_simp
  have hb := actual_settling (mul_nonneg hσ.le hH)
    (div_nonneg hW (sq_nonneg σ)) hC hn
    (fun τ hτ => (le_div_iff₀ hσ).2 (hrlo _ (div_mem_Icc hσ hτ)))
    (fun τ hτ => (div_le_iff₀ hσ).2 (hrhi _ (div_mem_Icc hσ hτ)))
    (fun τ hτ => by
      rw [abs_div, abs_of_pos (pow_pos hσ 2)]
      exact div_le_div_of_nonneg_right (hw _ (div_mem_Icc hσ hτ)) (sq_nonneg σ))
    (by simpa [ScaledTracking.normalize] using hi)
  intro t ht i
  have heq : σ*t/σ = t := by field_simp
  simpa only [ScaledTracking.normalize,heq] using hb (σ*t)
    ⟨mul_nonneg hσ.le ht.1, mul_le_mul_of_nonneg_left ht.2 hσ.le⟩ i

/-- An inherited tracking cube initializes this hold without resetting state. -/
theorem cube_initializes {W R : ℝ} (hW : 0 ≤ W) (hR : 0 ≤ R) {s : State} {c : ℝ}
    (hi : ∀ i, |coordinates c s i| ≤ R) :
    ∀ i, |coordinates c s i| ≤ radius W (5*R/4) 0 i := by
  intro i
  apply (hi i).trans
  fin_cases i <;> norm_num [radius,weight] <;> linarith

/-- This simpler common radius unpacks to speed, acceleration and command
bounds using the already checked coordinate transformation. -/
theorem radius_le_common {W C t : ℝ} (hC : 0 ≤ C) (i : Fin 3) :
    radius W C t i ≤ 3*W/8+C*Real.exp (-(2/5)*t) := by
  have hK : 0 ≤ C*Real.exp (-(2/5)*t) := mul_nonneg hC (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right (weight_le_one i) hK
  dsimp [radius]
  nlinarith

/-- Physical bounds follow from the actual plant through the final hold. The
initial cube is retained; the proof does not set velocity or acceleration to zero. -/
theorem settling_physical_bounds {σ H W R c : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hW : 0 ≤ W) (hR : 0 ≤ R)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput σ c f t+w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hi : ∀ i, |coordinates c (scaleState σ (f 0)) i| ≤ R) :
    ∀ t ∈ Icc 0 H,
      let E := 3*W/(8*σ^2)+(5*R/4)*Real.exp (-(2/5)*(σ*t))
      |f t 0-c| ≤ E ∧ |f t 1| ≤ 8*σ*E ∧ |f t 2| ≤ 64*σ^2*E ∧
      |holdInput σ c f t| ≤ 24*σ^2*E := by
  have hC : 0 ≤ 5*R/4 := by positivity
  have hcub := actual_settling_scaled hσ hH hW hC hf hrlo hrhi hw
    (cube_initializes (div_nonneg hW (sq_nonneg σ)) hR hi)
  intro t ht
  dsimp only
  simp only [neg_mul]
  let E := 3*W/(8*σ^2)+(5*R/4)*Real.exp (-(2/5*(σ*t)))
  have hz : ∀ i, |coordinates c (scaleState σ (f t)) i| ≤ E := by
    intro i
    have hb := (hcub t ht i).trans (radius_le_common hC i)
    convert hb using 1 <;> dsimp [E] <;> ring
  obtain ⟨hx,hv,ha,hu⟩ := cube_physical_bounds hz
  have hv' : |f t 1|/σ ≤ 8*E := by
    simpa [scaleState,abs_div,abs_of_pos hσ] using hv
  have ha' : |f t 2|/σ^2 ≤ 64*E := by
    simpa [scaleState,abs_div,abs_of_pos (pow_pos hσ 2)] using ha
  dsimp [E] at hx hv' ha' hu
  refine ⟨by simpa [scaleState] using hx, ?_, ?_, ?_⟩
  · have h := (div_le_iff₀ hσ).mp hv'; nlinarith
  · have h := (div_le_iff₀ (pow_pos hσ 2)).mp ha'; nlinarith
  · dsimp [holdInput]
    rw [abs_mul,abs_of_nonneg (sq_nonneg σ)]
    nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg σ)]

/-- Any explicit exponential upper bound gives a checked threshold certificate. -/
theorem threshold_arithmetic {σ W R t B E : ℝ}
    (hσ : 0 < σ) (hR : 0 ≤ R) (he : Real.exp (-(2/5)*(σ*t)) ≤ B)
    (hE : 3*W/(8*σ^2)+(5*R/4)*B ≤ E) :
    3*W/(8*σ^2)+(5*R/4)*Real.exp (-(2/5)*(σ*t)) ≤ E := by
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 5*R/4 by positivity)
  linarith

/-- The disturbance floor is part of the certificate, even after a long hold. -/
theorem illustrative_floor :
    3*(1/100:ℝ)/(8*10^2) = 3/80000 ∧
    8*10*(3*(1/100:ℝ)/(8*10^2)) = 3/1000 ∧
    64*10^2*(3*(1/100:ℝ)/(8*10^2)) = 6/25 := by norm_num

/-- This particular certificate cannot establish the tighter robot bands.
This is a bound limitation, not an impossibility theorem for the plant. -/
theorem illustrative_floor_exceeds_tight_bands :
    (1/1000:ℝ) < 3/1000 ∧ (1/50:ℝ) < 6/25 := by norm_num

/-- The actual endpoint state initializes the hold. This identity connects the
existing scaled tracking theorem to the new settling theorem. -/
theorem matched_hold_cube {σ R c T : ℝ} {previous reference hold : ℝ → State}
    (hphysical : hold 0 = previous T)
    (hfinished : reference T = ![c,0,0])
    (hcube : ∀ i, |coordinates 0 (scaledError σ previous reference T) i| ≤ R) :
    ∀ i, |coordinates c (scaleState σ (hold 0)) i| ≤ R := by
  intro i
  rw [hphysical]
  have heq : coordinates c (scaleState σ (previous T)) i =
      coordinates 0 (scaledError σ previous reference T) i := by
    fin_cases i <;> dsimp [coordinates,scaledError,scaleState,error] <;>
      rw [hfinished] <;> simp <;> ring
  rw [heq]
  exact hcube i

end LeanControls.Settling
