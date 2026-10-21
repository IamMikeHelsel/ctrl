import domain_pm_bridge

noncomputable section

namespace V06FullBridge
open Matrix

def vecSq (v : Fin 2 → ℝ) : ℝ := ∑ i, (v i)^2

def fullMatrixObjective (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (p₁ p₂ : Fin 2 → ℝ) : ℝ :=
  V06Bridge.matrixObjective R₁ R₂ + vecSq (p₁-![1,0]) +
  vecSq (p₂-p₁-R₁.mulVec ![3/5,4/5]) + vecSq (p₂-![1,1])

theorem expansion (c s d t : ℝ) (p₁ p₂ : Fin 2 → ℝ) :
    fullMatrixObjective (V06.rotation c s) (V06.rotation d t) p₁ p₂ =
    V06PM.fullObjective c s d t (p₁ 0) (p₁ 1) (p₂ 0) (p₂ 1) := by
  unfold fullMatrixObjective
  rw [V06Bridge.expansion]
  simp [vecSq,V06.rotation,Fin.sum_univ_two,V06PM.fullObjective]
  ring

theorem actual_global_bound (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (p₁ p₂ : Fin 2 → ℝ)
    (h₁ : R₁.transpose*R₁=1) (d₁ : R₁.det=1)
    (h₂ : R₂.transpose*R₂=1) (d₂ : R₂.det=1) :
    (12/5 : ℝ) ≤ fullMatrixObjective R₁ R₂ p₁ p₂ := by
  obtain ⟨e₁,n₁⟩ := V06.proper_rotation_parameterization R₁ h₁ d₁
  obtain ⟨e₂,n₂⟩ := V06.proper_rotation_parameterization R₂ h₂ d₂
  have he : fullMatrixObjective R₁ R₂ p₁ p₂ =
      V06PM.fullObjective (R₁ 0 0) (R₁ 1 0) (R₂ 0 0) (R₂ 1 0)
        (p₁ 0) (p₁ 1) (p₂ 0) (p₂ 1) := by
    conv_lhs => rw [e₁,e₂]
    exact expansion _ _ _ _ _ _
  rw [he]
  exact V06PM.full_global_lower _ _ _ _ _ _ _ _ n₁ n₂

theorem actual_unique (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (p₁ p₂ : Fin 2 → ℝ)
    (h₁ : R₁.transpose*R₁=1) (d₁ : R₁.det=1)
    (h₂ : R₂.transpose*R₂=1) (d₂ : R₂.det=1)
    (hv : fullMatrixObjective R₁ R₂ p₁ p₂=12/5) :
    R₁=V06.rotation (4/5) (3/5) ∧ R₂=V06.rotation (7/25) (24/25) ∧
    p₁=![1,0] ∧ p₂=![1,1] := by
  obtain ⟨e₁,n₁⟩ := V06.proper_rotation_parameterization R₁ h₁ d₁
  obtain ⟨e₂,n₂⟩ := V06.proper_rotation_parameterization R₂ h₂ d₂
  have he : fullMatrixObjective R₁ R₂ p₁ p₂ =
      V06PM.fullObjective (R₁ 0 0) (R₁ 1 0) (R₂ 0 0) (R₂ 1 0)
        (p₁ 0) (p₁ 1) (p₂ 0) (p₂ 1) := by
    conv_lhs => rw [e₁,e₂]
    exact expansion _ _ _ _ _ _
  rw [he] at hv
  obtain ⟨hc,hs,hd,ht,hx,hy,hz,hw⟩ := V06PM.full_unique _ _ _ _ _ _ _ _ n₁ n₂ hv
  refine ⟨by simpa only [hc,hs] using e₁,by simpa only [hd,ht] using e₂,?_,?_⟩
  · ext i
    fin_cases i <;> simp [hx,hy]
  · ext i
    fin_cases i <;> simp [hz,hw]

theorem actual_candidate :
    fullMatrixObjective (V06.rotation (4/5) (3/5)) (V06.rotation (7/25) (24/25))
    ![1,0] ![1,1]=12/5 := by
  rw [expansion]
  exact V06PM.full_candidate

#print axioms expansion
#print axioms actual_global_bound
#print axioms actual_unique
#print axioms actual_candidate
end V06FullBridge
