import AdaptiveAdmission
noncomputable section
namespace C11Actual
open Set Filter LeanControls.DigitalHold LeanControls.AdaptiveAdmission
variable {H D : ℝ} {m : State} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
  (ex : LeanControls.AdaptiveAdmission.Execution H D m f r d stamp read) (hD : 0 ≤ D) (hDH : D ≤ H)
  (hinit : |f 0 2| ≤ 13/10)
include ex hD hDH hinit

theorem startup_acceleration : ∀ t ∈ Icc 0 D, |f t 2| ≤ 13/10 := by
  have hc : ContinuousOn (fun t => f t 2) (Icc 0 D) :=
    (continuous_apply 2).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hDH))
  have hai := hinit
  have infl (ε : ℝ) (hε : 0 < ε) : ∀ t ∈ Icc 0 D, |f t 2| ≤ 13/10+ε := by
    let y : Bool → ℝ → ℝ := fun b t => (if b then f t 2 else -f t 2)-(13/10+ε)
    let dy : Bool → ℝ → ℝ := fun b t =>
      if b then r false t*(-121/100+d false t-f t 2) else -(r false t*(-121/100+d false t-f t 2))
    have hyc : ∀ b, ContinuousOn (y b) (Icc 0 D) := by
      intro b; cases b <;> dsimp [y] <;> fun_prop
    have hyd : ∀ b t, t ∈ Ioo 0 D → HasDerivWithinAt (y b) (dy b t) (Iic t) t := by
      intro b t ht
      have hd := ex.left_ode t ⟨ht.1,ht.2.le.trans hDH⟩ 2
      have hdt : t ≤ D := ht.2.le
      simp only [rhs,actualCommand,Bool.false_eq_true,ite_false,hdt,ite_true,Matrix.cons_val_two] at hd
      cases b
      · exact hd.neg.sub_const _
      · exact hd.sub_const _
    have hyi : ∀ b, y b 0 < 0 := by
      intro b
      have hh := abs_le.mp hai
      cases b <;> dsimp [y] <;> linarith
    have hyin : ∀ t ∈ Ioo 0 D, (∀ u ∈ Icc 0 t, ∀ b, y b u ≤ 0) → ∀ b, y b t = 0 → dy b t < 0 := by
      intro t ht _ b he
      have hr := ex.rate false t ⟨ht.1.le,ht.2.le.trans hDH⟩
      have hd := abs_le.mp (ex.target_error false t ⟨ht.1.le,ht.2.le.trans hDH⟩)
      cases b
      · dsimp [y] at he
        have hg : 0 < -121/100+d false t-f t 2 := by linarith
        have hp := mul_pos (by linarith [hr.1] : 0 < r false t) hg
        dsimp [dy]; linarith
      · dsimp [y] at he
        have hg : -121/100+d false t-f t 2 < 0 := by linarith
        have hp := mul_neg_of_pos_of_neg (by linarith [hr.1] : 0 < r false t) hg
        exact hp
    have hb := finite_prefix_barrier hD hyc hyd hyi hyin
    intro t ht
    have hp := hb t ht true
    have hn := hb t ht false
    dsimp [y] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht
  exact le_of_forall_pos_le_add (fun ε hε => infl ε hε t ht)


end C11Actual
#print axioms C11Actual.startup_acceleration
