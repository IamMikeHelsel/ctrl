import CheckedTree
set_option maxHeartbeats 4000000
namespace E10

theorem completion_high {c : ℚ} (hc : 22/25 ≤ c) :
 completion c = -1/4+3/(8*c)-1/(8*c^2) := by
 have hp : 0 < 2*c := by linarith
 have hx : ¬ xval c ≤ 3/8 := by
  have h : 1/(2*c) < 5/8 := (div_lt_iff₀ hp).2 (by linarith)
  unfold xval
  linarith
 unfold completion Q
 rw [if_neg hx]
 unfold xval
 have hn : c ≠ 0 := by linarith
 field_simp [hn]
 <;> ring

theorem exterior_identity {c : ℚ} (hc : 22/25 ≤ c) :
 (1+c^2)*R-c^2*(completion c+I) =
  54123/293750000+(201409/5875000)*(c-22/25)+(109297/470000)*(c-22/25)^2 := by
 rw [completion_high hc]
 unfold R I
 have hn : c ≠ 0 := by linarith
 field_simp [hn]
 <;> ring

theorem high_exterior {c j : ℚ} (hc : 22/25 ≤ c) : Selected c j := by
 by_cases hu : c^2*j ≤ R
 · exact Or.inl hu
 · have hid := exterior_identity hc
   have hp : 0 < (1+c^2)*R-c^2*(completion c+I) := by
    rw [hid]
    have h1 : 0 ≤ (201409/5875000 : ℚ)*(c-22/25) := mul_nonneg (by norm_num) (by linarith)
    have h2 : 0 ≤ (109297/470000 : ℚ)*(c-22/25)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith
   have hq : completion c+I-j ≤ R := by
    by_contra hh
    have hm := mul_nonneg (sq_nonneg c) (show 0 ≤ completion c+I-j-R by linarith)
    nlinarith
   exact Or.inr (Or.inl ⟨by linarith,hq⟩)

theorem low_exterior {c j : ℚ} (hc : 1/2 ≤ c) (hu : c ≤ 767/1000)
 (hj : 0 ≤ j) (hju : j ≤ I) : Selected c j :=
 uniform_sound (cb := (1/2,767/1000)) (jb := (0,I)) ⟨hc,hu⟩ ⟨hj,hju⟩
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Complete fixed-target rational selector. No cover-validity or certificate premise remains. -/
theorem universal_selector (c j : ℚ) (hc : 1/2 ≤ c) (hcu : c ≤ 1)
 (hj : 0 ≤ j) (hju : j ≤ I) : Selected c j := by
 by_cases hlo : c ≤ 767/1000
 · exact low_exterior hc hlo hj hju
 by_cases hhi : 22/25 ≤ c
 · exact high_exterior hhi
 exact middle c j ⟨by linarith,by linarith⟩ ⟨hj,hju⟩
end E10
