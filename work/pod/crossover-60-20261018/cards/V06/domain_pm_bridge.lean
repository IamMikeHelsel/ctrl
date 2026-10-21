import pm_cycle
import domain_certificate

noncomputable section

namespace V06Bridge
open Matrix

def matrixObjective (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  V06.frobSq (R₁-1)+V06.frobSq (R₂-R₁)+
  V06.frobSq (R₂-V06.rotation (-44/125) (117/125))

theorem expansion (c s d t : ℝ) :
    matrixObjective (V06.rotation c s) (V06.rotation d t)=V06PM.objective c s d t := by
  simp [matrixObjective,V06.frobSq,V06.rotation,Fin.sum_univ_two,V06PM.objective]
  ring

theorem actual_global_bound (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (h₁ : R₁.transpose*R₁=1) (d₁ : R₁.det=1)
    (h₂ : R₂.transpose*R₂=1) (d₂ : R₂.det=1) :
    (12/5 : ℝ) ≤ matrixObjective R₁ R₂ := by
  obtain ⟨e₁,n₁⟩ := V06.proper_rotation_parameterization R₁ h₁ d₁
  obtain ⟨e₂,n₂⟩ := V06.proper_rotation_parameterization R₂ h₂ d₂
  have he : matrixObjective R₁ R₂ = V06PM.objective (R₁ 0 0) (R₁ 1 0) (R₂ 0 0) (R₂ 1 0) := by
    conv_lhs => rw [e₁,e₂]
    exact expansion _ _ _ _
  rw [he]
  exact V06PM.global_lower _ _ _ _ n₁ n₂

theorem actual_unique_optimum (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (h₁ : R₁.transpose*R₁=1) (d₁ : R₁.det=1)
    (h₂ : R₂.transpose*R₂=1) (d₂ : R₂.det=1)
    (hv : matrixObjective R₁ R₂=12/5) :
    R₁=V06.rotation (4/5) (3/5) ∧ R₂=V06.rotation (7/25) (24/25) := by
  obtain ⟨e₁,n₁⟩ := V06.proper_rotation_parameterization R₁ h₁ d₁
  obtain ⟨e₂,n₂⟩ := V06.proper_rotation_parameterization R₂ h₂ d₂
  have he : matrixObjective R₁ R₂ = V06PM.objective (R₁ 0 0) (R₁ 1 0) (R₂ 0 0) (R₂ 1 0) := by
    conv_lhs => rw [e₁,e₂]
    exact expansion _ _ _ _
  rw [he] at hv
  obtain ⟨hc,hs,hd,ht⟩ := V06PM.unique_optimum _ _ _ _ n₁ n₂ hv
  exact ⟨by simpa only [hc,hs] using e₁,by simpa only [hd,ht] using e₂⟩

theorem actual_candidate :
    matrixObjective (V06.rotation (4/5) (3/5)) (V06.rotation (7/25) (24/25))=12/5 := by
  rw [expansion]
  exact V06PM.candidate.2.2

#print axioms expansion
#print axioms actual_global_bound
#print axioms actual_unique_optimum
#print axioms actual_candidate
end V06Bridge
