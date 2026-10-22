import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite transport weak duality

This is a small algebraic certificate principle, not a formalization of a transport
solver, robot dynamics, or the Python checker. A coupling with exact marginals and
nonnegative entries bounds every feasible additive transport dual from above.
The theorem is standard; this file makes no mathematical novelty claim.

AI assistance: this module and the accompanying experimental checker were drafted
with Codex. The declared theorem is independently checked by Lean's kernel.
-/

namespace Research.TransportCertificate

open scoped BigOperators

theorem finite_transport_weak_duality
    {n m : ℕ} (a u : Fin n → ℚ) (b v : Fin m → ℚ)
    (p c : Fin n → Fin m → ℚ)
    (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = a i)
    (hcol : ∀ j, ∑ i, p i j = b j)
    (hdual : ∀ i j, u i + v j ≤ c i j) :
    (∑ i, a i * u i) + (∑ j, b j * v j) ≤ ∑ i, ∑ j, p i j * c i j := by
  have hrows : (∑ i, a i * u i) = ∑ i, ∑ j, p i j * u i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hrow i]
  have hcols : (∑ j, b j * v j) = ∑ i, ∑ j, p i j * v j := by
    calc
      (∑ j, b j * v j) = ∑ j, ∑ i, p i j * v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_mul, hcol j]
      _ = ∑ i, ∑ j, p i j * v j := Finset.sum_comm
  calc
    (∑ i, a i * u i) + (∑ j, b j * v j) = ∑ i, ∑ j, p i j * (u i + v j) := by
      rw [hrows, hcols, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, ∑ j, p i j * c i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hdual i j) (hp i j)

/-- A dual lower bound and a candidate upper gap bound imply a bound relative to
every feasible competitor. Candidate feasibility is a separate obligation. -/
theorem finite_transport_candidate_gap
    {n m : ℕ} (a u : Fin n → ℚ) (b v : Fin m → ℚ)
    (q c : Fin n → Fin m → ℚ) (candidateCost gap : ℚ)
    (hq : ∀ i j, 0 ≤ q i j)
    (hrow : ∀ i, ∑ j, q i j = a i)
    (hcol : ∀ j, ∑ i, q i j = b j)
    (hdual : ∀ i j, u i + v j ≤ c i j)
    (hupper : candidateCost ≤ (∑ i, a i * u i) + (∑ j, b j * v j) + gap) :
    candidateCost ≤ (∑ i, ∑ j, q i j * c i j) + gap := by
  have hweak := finite_transport_weak_duality a u b v q c hq hrow hcol hdual
  linarith

#print axioms finite_transport_weak_duality
#print axioms finite_transport_candidate_gap

end Research.TransportCertificate
