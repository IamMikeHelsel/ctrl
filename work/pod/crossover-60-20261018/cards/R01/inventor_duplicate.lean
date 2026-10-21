import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- AI-written isolated reference/interval certificate. Positions below use metres.
The exact P/F0 formula is reproduced from certificate-03/builder/Kernel.lean;
this file does not import the old plant theorem or assert its ODE assumptions.
The failure is replay AFTER compilation into displacement events, not replay of
an absolute-goal command through an already-idempotent compiler. -/
set_option autoImplicit false
namespace R01Inventor

noncomputable def P (n : ℕ) (z : ℝ) : ℝ :=
  (max z 0)^n - 4*(max (z-1) 0)^n + 6*(max (z-2) 0)^n -
    4*(max (z-3) 0)^n + (max (z-4) 0)^n

noncomputable def F0 (z : ℝ) : ℝ := P 4 z / 24

noncomputable def duplicateReferenceAtDeadline : ℝ :=
  (1/1000) * F0 (((3/2:ℝ)-(11/50))/(1/5)) +
  (1/1000) * F0 (((3/2:ℝ)-(23/100))/(1/5))

theorem duplicate_reference_value : duplicateReferenceAtDeadline = 1/500 := by
  norm_num [duplicateReferenceAtDeadline, F0, P]

theorem duplicated_event_misses_goal (x : ℝ)
    (tube : |x - duplicateReferenceAtDeadline| ≤ 1/5000) :
    4/5000 ≤ |x - 1/1000| := by
  rw [duplicate_reference_value] at tube
  have lower := (abs_le.mp tube).1
  have h : (4/5000:ℝ) ≤ x - 1/1000 := by linarith
  exact le_trans h (le_abs_self _)

theorem duplicated_event_not_success (x : ℝ)
    (tube : |x - duplicateReferenceAtDeadline| ≤ 1/5000) :
    ¬ |x - 1/1000| ≤ 1/5000 := by
  have h := duplicated_event_misses_goal x tube
  intro success
  linarith

theorem zero_reference_margin_exact (q g R : ℝ) (nonneg : 0 ≤ R)
    (robust : ∀ e : ℝ, -R ≤ e → e ≤ R → |q+e-g| ≤ R) : q = g := by
  have hp := (abs_le.mp (robust R (by linarith) (by rfl))).2
  have hm := (abs_le.mp (robust (-R) (by rfl) (by linarith))).1
  linarith

theorem reference_encoding_injective {α : Type} (encode : ℝ → α)
    (decode : α → ℝ) (R : ℝ) (nonneg : 0 ≤ R)
    (robust : ∀ g e : ℝ, -R ≤ e → e ≤ R → |decode (encode g)+e-g| ≤ R) :
    Function.Injective encode := by
  intro g₁ g₂ same
  have h₁ := zero_reference_margin_exact (decode (encode g₁)) g₁ R nonneg (robust g₁)
  have h₂ := zero_reference_margin_exact (decode (encode g₂)) g₂ R nonneg (robust g₂)
  calc
    g₁ = decode (encode g₁) := h₁.symm
    _ = decode (encode g₂) := congrArg decode same
    _ = g₂ := h₂

#print axioms duplicate_reference_value
#print axioms duplicated_event_misses_goal
#print axioms duplicated_event_not_success
#print axioms zero_reference_margin_exact
#print axioms reference_encoding_injective
end R01Inventor
