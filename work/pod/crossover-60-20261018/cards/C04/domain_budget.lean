import Mathlib.Tactic
namespace C04Budget
/-- Exact finite two-pass arithmetic at16ms. The coarse residual comes from two
commands in the same weighted box plus unchanged sensor/physical error. The
startup slope bound8 is retained in both passes. This theorem is algebra, not
a replacement for the mixed-history derivative and first-exit proof. -/
theorem two_pass_sixteen_ms (K : ℝ) (hK : (9/200:ℝ)≤K) :
    let M : ℝ := 301/3000
    let W0 := (1348/25)*K+M
    let L0 := (33148/75)*K+6*M
    let W1 := M+(2/125)*L0
    let L1 := max 8 (max ((9736/75)*K+4*W1) ((8884/75)*K+6*W1))
    8≤L0 ∧ (9736/75)*K+4*W0≤L0 ∧ (8884/75)*K+6*W0≤L0 ∧
      M+(2/125)*L1<(394/75)*K := by
  dsimp
  have h0 : (8:ℝ)≤33148/75*K+6*(301/3000) := by linarith
  have h1 : (9736/75:ℝ)*K+4*(1348/25*K+301/3000)≤33148/75*K+6*(301/3000) := by linarith
  have h2 : (8884/75:ℝ)*K+6*(1348/25*K+301/3000)≤33148/75*K+6*(301/3000) := by linarith
  refine ⟨h0,h1,h2,?_⟩
  have hL : max (8:ℝ)
      (max (9736/75*K+4*(301/3000+2/125*(33148/75*K+6*(301/3000))))
        (8884/75*K+6*(301/3000+2/125*(33148/75*K+6*(301/3000)))))
      < ((394/75)*K-301/3000)/(2/125) := by
    apply max_lt
    · linarith
    · apply max_lt <;> linarith
  linarith

/-- Authority remains inactive inside every source policy box and a small
inflated first-contact box K≤.05. Physical target error follows clipping. -/
theorem retuned_authority (K : ℝ) (hK : K≤1/20) :
    (674/25)*K+(271/3000)<2 := by linarith

theorem nominal_second_pass :
    (301/3000:ℝ)+(2/125)*8=137/600 ∧
    (394/75:ℝ)*(9/200)-137/600=121/15000 := by norm_num

#print axioms two_pass_sixteen_ms
#print axioms retuned_authority
#print axioms nominal_second_pass
end C04Budget
