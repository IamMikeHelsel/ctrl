import Mathlib.Tactic

namespace V12Inventor

/-- Literal six calibration constraints for inventor_metric.py's three homographies. -/
theorem nullspace_indefinite
    (b11 b12 b22 b13 b23 b33 : ℝ)
    (h0 : b12 = 0)
    (h1 : b11 - b22 = 0)
    (h2 : (5/3:ℝ)*b12 + (4/3:ℝ)*b23 = 0)
    (h3 : (25/9:ℝ)*b11 - b22 + (40/9:ℝ)*b13 + (16/9:ℝ)*b33 = 0)
    (h4 : (5/3:ℝ)*b12 + (4/3:ℝ)*b13 = 0)
    (h5 : b11 - (25/9:ℝ)*b22 - (40/9:ℝ)*b23 - (16/9:ℝ)*b33 = 0) :
    b12 = 0 ∧ b13 = 0 ∧ b23 = 0 ∧ b22 = b11 ∧ b33 = -b11 := by
  refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Positive definiteness requires positive quadratic forms on both coordinate axes. -/
theorem no_positive_metric
    (b11 b12 b22 b13 b23 b33 : ℝ)
    (h0 : b12 = 0)
    (h1 : b11 - b22 = 0)
    (h2 : (5/3:ℝ)*b12 + (4/3:ℝ)*b23 = 0)
    (h3 : (25/9:ℝ)*b11 - b22 + (40/9:ℝ)*b13 + (16/9:ℝ)*b33 = 0)
    (h4 : (5/3:ℝ)*b12 + (4/3:ℝ)*b13 = 0)
    (h5 : b11 - (25/9:ℝ)*b22 - (40/9:ℝ)*b23 - (16/9:ℝ)*b33 = 0)
    (positive_x : 0 < b11) (positive_z : 0 < b33) : False := by
  have h := nullspace_indefinite b11 b12 b22 b13 b23 b33 h0 h1 h2 h3 h4 h5
  linarith [h.2.2.2.2]

/-- Homography scaling weights the homogeneous residual quadratically. -/
theorem scaled_bilinear (l a b c d : ℝ) :
    (l*a)*(l*b)+(l*c)*(l*d) = l^2*(a*b+c*d) := by ring

end V12Inventor
#print axioms V12Inventor.nullspace_indefinite
#print axioms V12Inventor.no_positive_metric
#print axioms V12Inventor.scaled_bilinear
