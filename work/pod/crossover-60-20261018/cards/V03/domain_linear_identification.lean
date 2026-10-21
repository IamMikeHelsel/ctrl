import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- AI-written exact11-pair incidence certificate. The nine grid pairs and two
   predeclared separating pairs match domain_rank_gate.py. Zero matrix is included;
   physical nonzero translation is a separate obligation. No source edits. -/
set_option autoImplicit false
namespace V03LinearIdentification

theorem eleven_correspondences_force_matrix_line
    (f00 f01 f02 f10 f11 f12 f20 f21 f22 : ℝ)
    -- x=(0,0,1), y=(1,0,1).
    (h0 : f02 + f22 = 0)
    -- x=(0,1/2,1), y=(1,1/2,1).
    (h1 : (1/2)*f01 + f02 + (1/4)*f11 + (1/2)*f12 + (1/2)*f21 + f22 = 0)
    -- x=(0,1,1), y=(1,1,1).
    (h2 : f01 + f02 + f11 + f12 + f21 + f22 = 0)
    -- x=(1/2,0,1), y=(3/2,0,1).
    (h3 : (3/4)*f00 + (3/2)*f02 + (1/2)*f20 + f22 = 0)
    -- x=(1/2,1/2,1), y=(3/2,1/2,1).
    (h4 : (3/4)*f00 + (3/4)*f01 + (3/2)*f02 + (1/4)*f10 + (1/4)*f11 + (1/2)*f12 + (1/2)*f20 + (1/2)*f21 + f22 = 0)
    -- x=(1/2,1,1), y=(3/2,1,1).
    (h5 : (3/4)*f00 + (3/2)*f01 + (3/2)*f02 + (1/2)*f10 + f11 + f12 + (1/2)*f20 + f21 + f22 = 0)
    -- x=(1,0,1), y=(2,0,1).
    (h6 : (2)*f00 + (2)*f02 + f20 + f22 = 0)
    -- x=(1,1/2,1), y=(2,1/2,1).
    (h7 : (2)*f00 + f01 + (2)*f02 + (1/2)*f10 + (1/4)*f11 + (1/2)*f12 + f20 + (1/2)*f21 + f22 = 0)
    -- x=(1,1,1), y=(2,1,1).
    (h8 : (2)*f00 + (2)*f01 + (2)*f02 + f10 + f11 + f12 + f20 + f21 + f22 = 0)
    -- x=(1/4,1/4,1), y=(3/4,1/4,1).
    (h9 : (3/16)*f00 + (3/16)*f01 + (3/4)*f02 + (1/16)*f10 + (1/16)*f11 + (1/4)*f12 + (1/4)*f20 + (1/4)*f21 + f22 = 0)
    -- x=(1/4,3/4,1), y=(3/4,3/4,1).
    (h10 : (3/16)*f00 + (9/16)*f01 + (3/4)*f02 + (3/16)*f10 + (9/16)*f11 + (3/4)*f12 + (1/4)*f20 + (3/4)*f21 + f22 = 0)
    : f00 = 0 ∧ f01 = 0 ∧ f02 = 0 ∧ f10 = 0 ∧ f11 = 0 ∧
      f20 = 0 ∧ f22 = 0 ∧ f12 = -f21 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

#print axioms eleven_correspondences_force_matrix_line
end V03LinearIdentification
