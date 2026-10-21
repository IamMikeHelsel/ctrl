import AdaptiveAdmission
open Set Filter LeanControls.DigitalHold LeanControls.AdaptiveAdmission
noncomputable section
namespace C11InventorAdapter
variable {m : State}
-- Isolated adaptation of the original source proofs; only startup premises generalized.
section Prefix
variable {H D T K : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ}
  {read : Bool → ℝ → State} (ex : Execution H D m f r d stamp read)
  (hT : T ≤ H) (hK : 0 ≤ K) (hKmax : K ≤ 1/16)
  (hz : ∀ t ∈ Icc 0 T, ∀ i, |coordinates (center m) (f t) i| ≤ K)

include ex hT hz hKmax hK
theorem prefix_budget_adapter (hKR : radius ≤ K) (hD : 0 ≤ D) (hDH : D ≤ H)
    (hstartup : ∀ t ∈ Ico 0 D, |actualSlope D m f r d read true t| ≤ 8) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch (center m) f d read b t| ≤ 2*K := by
  have hsl0 : ∀ x ∈ Ico 0 T, |actualSlope D m f r d read true x| ≤ 384*K+618/1000 := by
    intro x hx
    by_cases hb : x < D
    · have hh := hstartup x ⟨hx.1,hb⟩
      norm_num [radius] at hKR
      linarith
    · have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch (center m) f d read true x) hK
        (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
      have hw := coarse_mismatch ex hT hKmax hz true x hxc
      have he : actualSlope D m f r d read true x =
          slopeRHS (r true x) (mismatch (center m) f d read true x) (coordinates (center m) (f x)) := by
        simp [actualSlope,actualMismatch,actualCommand,mismatch,hb]
      rw [he]
      linarith
  have hw0 := improve_mismatch ex hT hKmax hz (by positivity : 0 ≤ 384*K+618/1000) hsl0
  have hsl1 : ∀ x ∈ Ico 0 T, |actualSlope D m f r d read true x| ≤ 8 := by
    intro x hx
    by_cases hb : x < D
    · exact hstartup x ⟨hx.1,hb⟩
    · have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch (center m) f d read true x) hK
        (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
      have hw := hw0 true x hxc
      have he : actualSlope D m f r d read true x =
          slopeRHS (r true x) (mismatch (center m) f d read true x) (coordinates (center m) (f x)) := by
        simp [actualSlope,actualMismatch,actualCommand,mismatch,hb]
      rw [he]
      linarith
  have hw1 := improve_mismatch ex hT hKmax hz (by norm_num : (0:ℝ) ≤ 8) hsl1 b t ht
  norm_num [radius] at hKR
  linarith
end Prefix

theorem delayed_invariant_adapter {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hDH : D ≤ H) (hlim : D ≤ startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H D m f r d stamp read) (hstartupcube : ∀ t ∈ Icc 0 D, ∀ i, |coordinates (center m) (f t) i| ≤ radius)
    (hstartupslope : ∀ t ∈ Ico 0 D, |actualSlope D m f r d read true t| ≤ 8) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates (center m) (f t) i| ≤ radius := by
  have hi := hstartupcube 0 ⟨le_rfl,hD⟩
  let z := fun t => coordinates (center m) (f t)
  have hradius : 0 ≤ radius := by norm_num [radius]
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) (hsmall : ε*(1+H) ≤ 1/16-radius) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ radius+ε*(1+t) := by
    let K := fun t : ℝ => radius+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t) (actualMismatch D m f d read false t) (z t) p.1
       else -transformedRHS (r false t) (actualMismatch D m f d read false t) (z t) p.1)-ε
    have hKc : Continuous K := by dsimp [K]; fun_prop
    have hKd (t : ℝ) : HasDerivAt K ε t := by
      convert (((hasDerivAt_id t).const_add 1).const_mul ε).const_add radius using 1 <;> simp [K]
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := center m) (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub (hKd t).hasDerivWithinAt
      · exact hd.sub (hKd t).hasDerivWithinAt
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      cases b <;> dsimp [y,K,z] <;> linarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hKR : radius ≤ K t := by dsimp [K]; nlinarith [ht.1]
      have hKpos : 0 ≤ K t := hradius.trans hKR
      have hKmax : K t ≤ 1/16 := by dsimp [K]; nlinarith [ht.2]
      have hzt (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin 3) : |z u i| ≤ K t := by
        have hp := hall u hu (i,true)
        have hn := hall u hu (i,false)
        dsimp [y,K] at hp hn ⊢
        exact abs_le.mpr ⟨by nlinarith [hu.2],by nlinarith [hu.2]⟩
      by_cases hpre : t ≤ D
      · have hs := abs_le.mp (hstartupcube t ⟨ht.1.le,hpre⟩ p.1)
        obtain ⟨i,b⟩ := p
        cases b <;> dsimp [y,K,z] at he <;> dsimp at hs <;> exfalso <;> nlinarith [ht.1]
      have hw := prefix_budget_adapter ex ht.2.le hKpos hKmax hzt hKR hD hDH hstartupslope false t ⟨ht.1.le,le_rfl⟩
      have heff : actualMismatch D m f d read false t = mismatch (center m) f d read false t := by
        simp [actualMismatch,actualCommand,mismatch,hpre]
      obtain ⟨i,b⟩ := p
      have hface := cube_face hKpos le_rfl (ex.rate false t htc).1 (ex.rate false t htc).2 hw
        (hzt t ⟨ht.1.le,le_rfl⟩) i
      cases b
      · dsimp [y] at he
        have hzi : z t i = -K t := by linarith
        have hh := hface.2 hzi
        dsimp [dy]
        rw [heff]
        linarith
      · dsimp [y] at he
        have hzi : z t i = K t := by linarith
        have hh := hface.1 hzi
        dsimp [dy]
        rw [heff]
        linarith
    have hbar := finite_prefix_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,K] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < 1+H := by linarith
  let δ := min (ε/(1+H)) ((1/16-radius)/(1+H))
  have hδ : 0 < δ := lt_min (div_pos hε hden) (div_pos (by norm_num [radius]) hden)
  have hδ1 : δ*(1+H) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hδ2 : δ*(1+H) ≤ 1/16-radius := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hh := inflated δ hδ hδ2 t ht i
  change |z t i| ≤ radius+ε
  nlinarith [ht.2]


end C11InventorAdapter
#print axioms C11InventorAdapter.prefix_budget_adapter
#print axioms C11InventorAdapter.delayed_invariant_adapter
