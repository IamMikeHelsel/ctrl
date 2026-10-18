module
public import CommandSmoothing
@[expose] public section
noncomputable section
namespace LeanControls.JointFilter
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking

-- Normalized-time equations. The physical theorem below proves this change of units.
def coeff (r : ℝ) (z : State) : ℝ :=
  (-64+4*r)*z 0+(160-12*r)*z 1+(-96+12*r)*z 2

def jerkCoeff (r : ℝ) : ℝ := 3/2-5*r/96

def filterRHS (l r w j d : ℝ) (z : State) : ℝ :=
  -(l-r/2)*d-coeff r z-jerkCoeff r*j+(r/2)*w

theorem coeff_bound {r K : ℝ} {z : State}
    (hlo : 8 ≤ r) (hhi : r ≤ 12) (hK : 0 ≤ K)
    (hz : ∀ i, |z i| ≤ K) : |coeff r z| ≤ 96*K := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  have p0 := mul_nonneg (show 0 ≤ 64-4*r by linarith) (show 0 ≤ z 0+K by linarith)
  have n0 := mul_nonneg (show 0 ≤ 64-4*r by linarith) (show 0 ≤ K-z 0 by linarith)
  have p1 := mul_nonneg (show 0 ≤ 160-12*r by linarith) (show 0 ≤ K-z 1 by linarith)
  have n1 := mul_nonneg (show 0 ≤ 160-12*r by linarith) (show 0 ≤ z 1+K by linarith)
  have p2 := mul_nonneg (show 0 ≤ -96+12*r by linarith) (show 0 ≤ K-z 2 by linarith)
  have n2 := mul_nonneg (show 0 ≤ -96+12*r by linarith) (show 0 ≤ z 2+K by linarith)
  have hslack := mul_nonneg (show 0 ≤ r-8 by linarith) hK
  dsimp [coeff]
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

theorem filter_face {l r w j K E W J d : ℝ} {z : State}
    (hlo : 8 ≤ r) (hhi : r ≤ 12) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hW : 0 ≤ W) (hJ : 0 ≤ J) (hw : |w| ≤ W) (hj : |j| ≤ J)
    (budget : 96*K+(13/12)*J+6*W ≤ (l-6)*E)
    (hz : ∀ i, |z i| ≤ K) :
    (d = E → filterRHS l r w j d z ≤ 0) ∧
    (d = -E → 0 ≤ filterRHS l r w j d z) := by
  have hc := abs_le.mp (coeff_bound hlo hhi hK hz)
  have hbc : |jerkCoeff r| ≤ (13:ℝ)/12 := by
    rw [abs_le]; dsimp [jerkCoeff]; constructor <;> linarith
  have hb := abs_le.mp ((show |jerkCoeff r*j| ≤ (13/12)*J from by
    rw [abs_mul]; exact mul_le_mul hbc hj (abs_nonneg _) (by norm_num)))
  have hr : 0 ≤ r/2 := by linarith
  have hwb := abs_le.mp ((show |(r/2)*w| ≤ 6*W from by
    rw [abs_mul, abs_of_nonneg hr]
    exact mul_le_mul (by linarith : r/2 ≤ 6) hw (abs_nonneg _) (by norm_num)))
  have hrate := mul_nonneg (show 0 ≤ 12-r by linarith) hE
  constructor <;> intro he <;> dsimp [filterRHS] <;> rw [he] <;> nlinarith

-- The same factor inflates both radii. Constant disturbances do not inflate.
theorem inflated_budgets {R D W J l k : ℝ}
    (hW : 0 ≤ W) (hJ : 0 ≤ J) (hk : 1 ≤ k)
    (b1 : W+D+J/48 ≤ 2*R)
    (b2 : 96*R+(13/12)*J+6*W ≤ (l-6)*D) :
    W+k*D+J/48 ≤ 2*(k*R) ∧
    96*(k*R)+(13/12)*J+6*W ≤ (l-6)*(k*D) := by
  have p1 := mul_le_mul_of_nonneg_left b1 (by linarith : 0 ≤ k)
  have p2 := mul_le_mul_of_nonneg_left b2 (by linarith : 0 ≤ k)
  have pW := mul_nonneg (show 0 ≤ k-1 by linarith) hW
  have pJ := mul_nonneg (show 0 ≤ k-1 by linarith) hJ
  constructor <;> nlinarith

-- Four coordinates, two signs each: exactly eight simultaneous barriers.
theorem joint_invariant {H R D W J l : ℝ} (hH : 0 ≤ H)
    (hR : 0 < R) (hD : 0 < D) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    {r w : ℝ → ℝ} {j : ℝ} {z : ℝ → State} {d : ℝ → ℝ}
    (hzc : ∀ i, ContinuousOn (fun t => z t i) (Icc 0 H))
    (hdc : ContinuousOn d (Icc 0 H))
    (hzd : ∀ i t, t ∈ Ioo 0 H → HasDerivAt (fun s => z s i)
      (transformedRHS (r t) (w t+d t+(5/48-1/r t)*j) (z t) i) t)
    (hdd : ∀ t ∈ Ioo 0 H, HasDerivAt d (filterRHS l (r t) (w t) j (d t) (z t)) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W) (hj : |j| ≤ J)
    (b1 : W+D+J/48 ≤ 2*R) (b2 : 96*R+(13/12)*J+6*W ≤ (l-6)*D)
    (hzi : ∀ i, |z 0 i| ≤ R) (hdi : |d 0| ≤ D) :
    ∀ t ∈ Icc 0 H, (∀ i, |z t i| ≤ R) ∧ |d t| ≤ D := by
  let v : (Fin 3 ⊕ Unit) → ℝ → ℝ := Sum.elim (fun i t => z t i) (fun _ => d)
  let dv : (Fin 3 ⊕ Unit) → ℝ → ℝ := Sum.elim
    (fun i t => transformedRHS (r t) (w t+d t+(5/48-1/r t)*j) (z t) i)
    (fun _ t => filterRHS l (r t) (w t) j (d t) (z t))
  let B : (Fin 3 ⊕ Unit) → ℝ := Sum.elim (fun _ => R) (fun _ => D)
  have hB (a) : 0 < B a := by cases a <;> assumption
  have hvc (a) : ContinuousOn (v a) (Icc 0 H) := by cases a with
    | inl i => exact hzc i
    | inr _ => exact hdc
  have hvd (a) (t) (ht : t ∈ Ioo 0 H) : HasDerivAt (v a) (dv a t) t := by
    cases a with
    | inl i => exact hzd i t ht
    | inr _ => exact hdd t ht
  have hvi (a) : |v a 0| ≤ B a := by cases a with
    | inl i => exact hzi i
    | inr _ => exact hdi
  have inflated (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 H, ∀ a, |v a t| ≤ (1+ε*(1+t))*B a := by
    let k := fun t : ℝ => 1+ε*(1+t)
    let y : ((Fin 3 ⊕ Unit) × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then v p.1 t else -v p.1 t)-k t*B p.1
    let dy : ((Fin 3 ⊕ Unit) × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then dv p.1 t else -dv p.1 t)-ε*B p.1
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hkd (a) (t : ℝ) : HasDerivAt (fun t => k t*B a) (ε*B a) t := by
      convert ((((hasDerivAt_id t).const_add 1).const_mul ε).const_add 1).mul_const (B a) using 1 <;> simp [k]
    have hyc (p) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨a,b⟩ := p; cases b <;> dsimp [y] <;> fun_prop
    have hyd (p) (t) (ht : t ∈ Ioo 0 H) : HasDerivAt (y p) (dy p t) t := by
      obtain ⟨a,b⟩ := p; cases b
      · exact (hvd a t ht).neg.sub (hkd a t)
      · exact (hvd a t ht).sub (hkd a t)
    have hyi (p) : y p 0 < 0 := by
      obtain ⟨a,b⟩ := p; have hv := abs_le.mp (hvi a)
      have hp := mul_pos hε (hB a)
      cases b <;> dsimp [y,k] <;> nlinarith
    have hin (t) (ht : t ∈ Ioo 0 H) (hall : ∀ p, y p t ≤ 0)
        (p) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hk : 1 ≤ k t := by dsimp [k]; nlinarith [ht.1]
      have hv (a) : |v a t| ≤ k t*B a := by
        have hp := hall (a,true); have hn := hall (a,false)
        dsimp [y] at hp hn; exact abs_le.mpr ⟨by linarith,by linarith⟩
      have hz (i) : |z t i| ≤ k t*R := hv (Sum.inl i)
      have hd : |d t| ≤ k t*D := hv (Sum.inr ())
      have budgets := inflated_budgets hW hJ hk b1 b2
      have hres : |w t+d t+(5/48-1/r t)*j| ≤ 2*(k t*R) := by
        have hwd := (abs_add_le (w t) (d t)).trans (add_le_add (hw t htc) hd)
        have hb := residual_bound (by norm_num : (0:ℝ) ≤ 1/48)
          (centered_reciprocal_bound (hrlo t htc) (hrhi t htc)) hwd hj
        nlinarith [hb, budgets.1]
      have hKR : 0 ≤ k t*R := mul_nonneg (by linarith) hR.le
      have hKD : 0 ≤ k t*D := mul_nonneg (by linarith) hD.le
      have faces (a) : (v a t = k t*B a → dv a t ≤ 0) ∧
          (v a t = -(k t*B a) → 0 ≤ dv a t) := by
        cases a with
        | inl i => exact cube_face hKR le_rfl (hrlo t htc) (hrhi t htc) hres hz i
        | inr _ =>
          exact filter_face (hrlo t htc) (hrhi t htc) hKR hKD hW hJ
            (hw t htc) hj budgets.2 hz
      obtain ⟨a,b⟩ := p
      have hp := mul_pos hε (hB a)
      cases b
      · dsimp [y] at he
        have hf := (faces a).2 (by linarith)
        dsimp [dy]; linarith
      · dsimp [y] at he
        have hf := (faces a).1 (by linarith)
        dsimp [dy]; linarith
    have hb := finite_barrier hH hyc hyd hyi hin
    intro t ht a
    have hp := hb t ht (a,true); have hn := hb t ht (a,false)
    dsimp [y,k] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hfinal (t) (ht : t ∈ Icc 0 H) (a) : |v a t| ≤ B a := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hden : 0 < (1+t)*B a := mul_pos (by linarith [ht.1]) (hB a)
    have hh := inflated (ε/((1+t)*B a)) (div_pos hε hden) t ht a
    have heq : (1+ε/((1+t)*B a)*(1+t))*B a = B a+ε := by
      field_simp [ne_of_gt (hB a), ne_of_gt (show 0 < 1+t by linarith [ht.1])] <;> ring
    rwa [heq] at hh
  intro t ht
  exact ⟨fun i => hfinal t ht (Sum.inl i),hfinal t ht (Sum.inr ())⟩

-- The target derivative follows from the actual plant, not a command-rate premise.
theorem target_derivative {H : ℝ} {r w u : ℝ → ℝ} {j : ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => u t+w t) f)
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,j] i) t)
    (t : ℝ) (ht : t ∈ Ioo 0 H) :
    HasDerivAt (input (5/48) f q (fun _ => j))
      (coeff (r t) (coordinates 0 (error f q t))+jerkCoeff (r t)*j-
        (r t/2)*(u t-input (5/48) f q (fun _ => j) t+w t)) t := by
  have hx := hf.ode t ht 0
  have hv := hf.ode t ht 1
  have ha := hf.ode t ht 2
  have hq0 := hdq t ht 0
  have hq1 := hdq t ht 1
  have hq2 := hdq t ht 2
  change HasDerivAt (fun s => f s 0) (f t 1) t at hx
  change HasDerivAt (fun s => f s 1) (f t 2) t at hv
  change HasDerivAt (fun s => f s 2) (r t*(u t+w t-f t 2)) t at ha
  change HasDerivAt (fun s => q s 0) (q t 1) t at hq0
  change HasDerivAt (fun s => q s 1) (q t 2) t at hq1
  change HasDerivAt (fun s => q s 2) j t at hq2
  convert (((hq2.sub ((hx.sub hq0).const_mul 8)).sub
    ((hv.sub hq1).const_mul 6)).sub ((ha.sub hq2).div_const 2)).add_const ((5/48)*j)
    using 1 <;> (try funext s) <;> dsimp [input,command,error,coeff,jerkCoeff,coordinates] <;> ring

/-- A joint invariant from the normalized actual plant/reference/filter ODEs.
Only the initial box is a premise. -/
theorem actual_joint {H R D W J l : ℝ} (hH : 0 ≤ H)
    (hR : 0 < R) (hD : 0 < D) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    {r w u : ℝ → ℝ} {j : ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => u t+w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,j] i) t)
    (hu : ContinuousOn u (Icc 0 H))
    (hdu : ∀ t ∈ Ioo 0 H, HasDerivAt u (l*(input (5/48) f q (fun _ => j) t-u t)) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W) (hj : |j| ≤ J)
    (b1 : W+D+J/48 ≤ 2*R) (b2 : 96*R+(13/12)*J+6*W ≤ (l-6)*D)
    (hzi : ∀ i, |coordinates 0 (error f q 0) i| ≤ R)
    (hdi : |u 0-input (5/48) f q (fun _ => j) 0| ≤ D) :
    ∀ t ∈ Icc 0 H, (∀ i, |coordinates 0 (error f q t) i| ≤ R) ∧
      |u t-input (5/48) f q (fun _ => j) t| ≤ D := by
  let d := fun t => u t-input (5/48) f q (fun _ => j) t
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hqc (i : Fin 3) := (continuous_apply i).comp_continuousOn hq
  have hc (i : Fin 3) : ContinuousOn (fun t => coordinates 0 (error f q t) i) (Icc 0 H) := by
    fin_cases i <;> dsimp [coordinates,error] <;> fun_prop
  have hdc : ContinuousOn d (Icc 0 H) := by dsimp [d,input,command,error]; fun_prop
  have hf' : IsTrajectory H r (fun t => input (5/48) f q (fun _ => j) t+(w t+d t)) f := by
    have he : (fun t => input (5/48) f q (fun _ => j) t+(w t+d t)) = (fun t => u t+w t) := by
      funext t; dsimp [d] <;> ring
    rwa [he]
  have he := error_trajectory hf' hq hdq
    (fun t ht => ne_of_gt (by linarith [hrlo t ⟨ht.1.le,ht.2.le⟩]))
  have hzode (i) (t) (ht : t ∈ Ioo 0 H) := coordinates_ode he t ht i
  have hdode (t) (ht : t ∈ Ioo 0 H) :
      HasDerivAt d (filterRHS l (r t) (w t) j (d t) (coordinates 0 (error f q t))) t := by
    convert (hdu t ht).sub (target_derivative hf hdq t ht) using 1
    dsimp [filterRHS,d] <;> ring
  exact joint_invariant hH hR hD hW hJ hc hdc hzode hdode hrlo hrhi hw hj b1 b2 hzi hdi

lemma target_normalized {σ : ℝ} (hσ : 0 < σ)
    (f q : ℝ → State) (j τ : ℝ) :
    physicalInput σ f q (fun _ => j) (τ/σ)/σ^2 =
      input (5/48) (normalize σ f) (normalize σ q) (fun _ => j/σ^3) τ := by
  simpa using normalized_input hσ f q (fun _ => j) (fun _ => 0) τ

/-- The physical plant/reference/filter equations imply the joint box on the
whole closed segment. The reference jerk is constant on this segment. -/
theorem actual_joint_scaled {σ H R D W J l : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hR : 0 < R) (hD : 0 < D)
    (hW : 0 ≤ W) (hJ : 0 ≤ J)
    {r w u : ℝ → ℝ} {j : ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => u t+w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1,q t 2,j] i) t)
    (hu : ContinuousOn u (Icc 0 H))
    (hdu : ∀ t ∈ Ioo 0 H,
      HasDerivAt u (l*(physicalInput σ f q (fun _ => j) t-u t)) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W) (hj : |j| ≤ J)
    (b1 : W+D+J/(48*σ) ≤ 2*σ^2*R)
    (b2 : 96*σ^3*R+(13/12)*J+6*σ*W ≤ (l-6*σ)*D)
    (hzi : ∀ i, |coordinates 0 (scaledError σ f q 0) i| ≤ R)
    (hdi : |u 0-physicalInput σ f q (fun _ => j) 0| ≤ D) :
    ∀ t ∈ Icc 0 H, (∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R) ∧
      |u t-physicalInput σ f q (fun _ => j) t| ≤ D := by
  let un := fun τ => u (τ/σ)/σ^2
  have hsn := ne_of_gt hσ
  have hfn : IsTrajectory (σ*H) (fun τ => r (τ/σ)/σ)
      (fun τ => un τ+w (τ/σ)/σ^2) (normalize σ f) := by
    simpa only [add_div] using normalize_trajectory hσ hf
  have hun : ContinuousOn un (Icc 0 (σ*H)) := by
    exact (hu.comp (continuous_id.div_const σ).continuousOn
      (fun τ hτ => div_mem_Icc hσ hτ)).div_const _
  have hdun (τ) (hτ : τ ∈ Ioo 0 (σ*H)) :
      HasDerivAt un ((l/σ)*(input (5/48) (normalize σ f) (normalize σ q)
        (fun _ => j/σ^3) τ-un τ)) τ := by
    have hh := ((hdu (τ/σ) (div_mem_Ioo hσ hτ)).comp τ
      ((hasDerivAt_id τ).div_const σ)).div_const (σ^2)
    convert hh using 1
    · rfl
    · rw [← target_normalized hσ]
      dsimp [un]; field_simp <;> ring
  have bn1 : W/σ^2+D/σ^2+(J/σ^3)/48 ≤ 2*R := by
    have hh := normalized_budget hσ b1
    convert hh using 1 <;> field_simp <;> ring
  have bn2 : 96*R+(13/12)*(J/σ^3)+6*(W/σ^2) ≤ (l/σ-6)*(D/σ^2) := by
    calc
      _ = (96*σ^3*R+(13/12)*J+6*σ*W)/σ^3 := by field_simp <;> ring
      _ ≤ ((l-6*σ)*D)/σ^3 := div_le_div_of_nonneg_right b2 (pow_nonneg hσ.le 3)
      _ = _ := by field_simp <;> ring
  have hdin : |un 0-input (5/48) (normalize σ f) (normalize σ q) (fun _ => j/σ^3) 0| ≤ D/σ^2 := by
    rw [← target_normalized hσ]
    dsimp [un]
    rw [zero_div, ← sub_div, abs_div, abs_of_pos (pow_pos hσ 2)]
    exact div_le_div_of_nonneg_right hdi (sq_nonneg σ)
  have hb := actual_joint (mul_nonneg hσ.le hH) hR (div_pos hD (pow_pos hσ 2))
    (div_nonneg hW (sq_nonneg σ)) (div_nonneg hJ (pow_nonneg hσ.le 3))
    hfn (normalize_continuous hσ hq) (normalize_reference hσ hdq) hun hdun
    (fun τ hτ => (le_div_iff₀ hσ).2 (hrlo _ (div_mem_Icc hσ hτ)))
    (fun τ hτ => (div_le_iff₀ hσ).2 (hrhi _ (div_mem_Icc hσ hτ)))
    (fun τ hτ => by
      rw [abs_div,abs_of_pos (pow_pos hσ 2)]
      exact div_le_div_of_nonneg_right (hw _ (div_mem_Icc hσ hτ)) (sq_nonneg σ))
    (by rw [abs_div,abs_of_pos (pow_pos hσ 3)];
        exact div_le_div_of_nonneg_right hj (pow_nonneg hσ.le 3))
    (by simpa using bn1) bn2
    (by simpa only [normalized_error,zero_div] using hzi) hdin
  intro t ht
  have htime : σ*t/σ = t := by field_simp
  have hh := hb (σ*t) ⟨mul_nonneg hσ.le ht.1,mul_le_mul_of_nonneg_left ht.2 hσ.le⟩
  constructor
  · simpa only [normalized_error,htime] using hh.1
  · have hfilter := hh.2
    rw [← target_normalized hσ] at hfilter
    dsimp [un] at hfilter
    rw [htime, ← sub_div,abs_div,abs_of_pos (pow_pos hσ 2)] at hfilter
    exact (div_le_div_iff_of_pos_right (pow_pos hσ 2)).mp hfilter

theorem illustrative_joint_budgets :
    (1:ℝ)/100+11/1200+10/(48*10) ≤ 2*10^2*(1/5000) ∧
    (96:ℝ)*10^3*(1/5000)+(13/12)*10+6*10*(1/100) ≤ (4000-6*10)*(11/1200) := by
  constructor <;> norm_num

theorem sharp_coeff_example : coeff 8 ![-1,1,0] = 96 := by norm_num [coeff]

end LeanControls.JointFilter
