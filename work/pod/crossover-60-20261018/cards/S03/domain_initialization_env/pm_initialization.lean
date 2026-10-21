import pm_cell
import pm_encoding
namespace S03Initialization

theorem full_cell_guard (X V : ℤ) (x v : ℝ)
    (hx : |(X:ℝ)/10000-x|≤1/20000)
    (hv : |(V:ℝ)/10000-v|≤1/20000)
    (guard : ∀ sx sv : ℤ, (sx = -1 ∨ sx = 1) → (sv = -1 ∨ sv = 1) →
      5*(2*X+sx)^2+2*(2*X+sx)*(2*V+sv)+(2*V+sv)^2≤40000000) :
    S03Cell.E x v≤1/10 := by
  have hcorner (sx sv : ℤ) (hsx : sx = -1 ∨ sx = 1) (hsv : sv = -1 ∨ sv = 1) :
      S03Cell.E ((X:ℝ)/10000+(sx:ℝ)/20000)
        ((V:ℝ)/10000+(sv:ℝ)/20000)≤1/10 := by
    have h := S03Encoding.corner_bound X V sx sv (guard sx sv hsx hsv)
    push_cast at h
    dsimp [S03Cell.E]
    nlinarith only [h]
  have h00 := hcorner (-1) (-1) (Or.inl rfl) (Or.inl rfl)
  have h01 := hcorner (-1) 1 (Or.inl rfl) (Or.inr rfl)
  have h10 := hcorner 1 (-1) (Or.inr rfl) (Or.inl rfl)
  have h11 := hcorner 1 1 (Or.inr rfl) (Or.inr rfl)
  norm_num at h00 h01 h10 h11
  rcases abs_le.mp hx with ⟨hx0,hx1⟩
  rcases abs_le.mp hv with ⟨hv0,hv1⟩
  exact S03Cell.cell_bound _ _ _ _ x v (1/10)
    ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩ h00 h01 h10 h11

#print axioms full_cell_guard
end S03Initialization
