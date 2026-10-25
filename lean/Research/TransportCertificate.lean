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

/-! ## Four-Support Static Command-Correction Interval & Exact Rational Farkas Certificates (S12-B01) -/

/-- Lower endpoint of the 4-support static command-correction interval:
`max(-alpha - wl, -beta - bl)`. -/
def fourSupportLower (wl bl alpha beta : ℚ) : ℚ :=
  max (-alpha - wl) (-beta - bl)

/-- Upper endpoint of the 4-support static command-correction interval:
`min(alpha - wu, beta - bu)`. -/
def fourSupportUpper (wu bu alpha beta : ℚ) : ℚ :=
  min (alpha - wu) (beta - bu)

/-- **Four-Support Static Command-Correction Interval Soundness**:
If `(w, b)` lies in the 4-support box `[wl, wu] × [bl, bu]`, `alpha ≤ beta`, `0 ≤ rho ≤ 1`,
and command `u` lies in `[fourSupportLower wl bl alpha beta, fourSupportUpper wu bu alpha beta]`,
then `w + u ∈ [-alpha, alpha]`, `b + u ∈ [-beta, beta]`, and every convex response combination
`(1 - rho) (w + u) + rho (b + u)` lies in `[-beta, beta]`. -/
theorem four_support_interval_sound
    (wl wu bl bu w b u alpha beta rho : ℚ)
    (hw : wl ≤ w ∧ w ≤ wu)
    (hb : bl ≤ b ∧ b ≤ bu)
    (hab : alpha ≤ beta)
    (hrho : 0 ≤ rho ∧ rho ≤ 1)
    (hu : fourSupportLower wl bl alpha beta ≤ u ∧ u ≤ fourSupportUpper wu bu alpha beta) :
    (-alpha ≤ w + u ∧ w + u ≤ alpha) ∧
    (-beta ≤ b + u ∧ b + u ≤ beta) ∧
    (-beta ≤ (1 - rho) * (w + u) + rho * (b + u) ∧
      (1 - rho) * (w + u) + rho * (b + u) ≤ beta) := by
  unfold fourSupportLower fourSupportUpper at hu
  have hlo : -alpha - wl ≤ u ∧ -beta - bl ≤ u := max_le_iff.mp hu.1
  have hhi : u ≤ alpha - wu ∧ u ≤ beta - bu := le_min_iff.mp hu.2
  have hw_lo : -alpha ≤ w + u := by linarith [hw.1, hlo.1]
  have hw_hi : w + u ≤ alpha := by linarith [hw.2, hhi.1]
  have hb_lo : -beta ≤ b + u := by linarith [hb.1, hlo.2]
  have hb_hi : b + u ≤ beta := by linarith [hb.2, hhi.2]
  have h1rho : 0 ≤ 1 - rho := by linarith [hrho.2]
  have hmix_lo : -beta ≤ (1 - rho) * (w + u) + rho * (b + u) := by
    have h_w_beta : 0 ≤ w + u + beta := by linarith [hw_lo, hab]
    have h_b_beta : 0 ≤ b + u + beta := by linarith [hb_lo]
    have hp1 : 0 ≤ (1 - rho) * (w + u + beta) := mul_nonneg h1rho h_w_beta
    have hp2 : 0 ≤ rho * (b + u + beta) := mul_nonneg hrho.1 h_b_beta
    linarith
  have hmix_hi : (1 - rho) * (w + u) + rho * (b + u) ≤ beta := by
    have h_w_beta : 0 ≤ beta - (w + u) := by linarith [hw_hi, hab]
    have h_b_beta : 0 ≤ beta - (b + u) := by linarith [hb_hi]
    have hp1 : 0 ≤ (1 - rho) * (beta - (w + u)) := mul_nonneg h1rho h_w_beta
    have hp2 : 0 ≤ rho * (beta - (b + u)) := mul_nonneg hrho.1 h_b_beta
    linarith
  exact ⟨⟨hw_lo, hw_hi⟩, ⟨hb_lo, hb_hi⟩, ⟨hmix_lo, hmix_hi⟩⟩

/-- **LP Dual Support Upper Bound Certificate**:
For any halfspace system `A x ≤ b` and nonnegative dual weights `y ≥ 0` with `Aᵀ y = c`
and `yᵀ b ≤ bound`, every feasible `x` satisfies `cᵀ x ≤ bound`. -/
theorem lp_dual_upper_bound
    {m n : ℕ} (A : Fin m → Fin n → ℚ) (b y : Fin m → ℚ) (c x : Fin n → ℚ) (bound : ℚ)
    (hy : ∀ i, 0 ≤ y i)
    (hstat : ∀ j, ∑ i, y i * A i j = c j)
    (hbound : (∑ i, y i * b i) ≤ bound)
    (hfeas : ∀ i, ∑ j, A i j * x j ≤ b i) :
    (∑ j, c j * x j) ≤ bound := by
  have hcx : (∑ j, c j * x j) = ∑ i, y i * (∑ j, A i j * x j) := by
    calc
      (∑ j, c j * x j) = ∑ j, (∑ i, y i * A i j) * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hstat j]
      _ = ∑ j, ∑ i, (y i * A i j) * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, y i * (A i j * x j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, y i * (∑ j, A i j * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
  have hle : (∑ i, y i * (∑ j, A i j * x j)) ≤ ∑ i, y i * b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hfeas i) (hy i)
  linarith

/-- **Exact Rational Farkas Infeasibility Certificate for Box + Halfspace Safety Constraints**:
Given linear safety constraints `A u ≤ b` and box bounds `l ≤ u ≤ u_max`, if nonnegative
rational multipliers `y ≥ 0`, `z_lo ≥ 0`, `z_hi ≥ 0` satisfy `Aᵀ y + z_hi - z_lo = 0` and
`bᵀ y + u_maxᵀ z_hi - lᵀ z_lo < 0`, then no vector `u` satisfies both `A u ≤ b` and
`l ≤ u ≤ u_max`. -/
theorem farkas_box_infeasibility_certificate
    {m n : ℕ} (A : Fin m → Fin n → ℚ) (b y : Fin m → ℚ)
    (l u_max z_lo z_hi : Fin n → ℚ)
    (hy : ∀ i, 0 ≤ y i)
    (hz_lo : ∀ j, 0 ≤ z_lo j)
    (hz_hi : ∀ j, 0 ≤ z_hi j)
    (hstat : ∀ j, (∑ i, y i * A i j) + z_hi j - z_lo j = 0)
    (hneg : (∑ i, y i * b i) + (∑ j, z_hi j * u_max j) - (∑ j, z_lo j * l j) < 0) :
    ¬ ∃ u : Fin n → ℚ, (∀ i, ∑ j, A i j * u j ≤ b i) ∧ (∀ j, l j ≤ u j ∧ u j ≤ u_max j) := by
  rintro ⟨u, hAu, hbox⟩
  have hsum_A : (∑ i, y i * (∑ j, A i j * u j)) = ∑ j, (∑ i, y i * A i j) * u j := by
    calc
      (∑ i, y i * (∑ j, A i j * u j)) = ∑ i, ∑ j, y i * (A i j * u j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, (y i * A i j) * u j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j, (∑ i, y i * A i j) * u j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_mul]
  have hzero :
      (∑ j, (∑ i, y i * A i j) * u j) + (∑ j, z_hi j * u j) - (∑ j, z_lo j * u j) = 0 := by
    calc
      (∑ j, (∑ i, y i * A i j) * u j) + (∑ j, z_hi j * u j) - (∑ j, z_lo j * u j)
        = ∑ j, (((∑ i, y i * A i j) + z_hi j - z_lo j) * u j) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ _j : Fin n, (0 : ℚ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hstat j, zero_mul]
      _ = 0 := Finset.sum_const_zero
  have h1 : (∑ i, y i * (∑ j, A i j * u j)) ≤ ∑ i, y i * b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hAu i) (hy i)
  have h2 : (∑ j, z_hi j * u j) ≤ ∑ j, z_hi j * u_max j := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hbox j).2 (hz_hi j)
  have h3 : (∑ j, z_lo j * l j) ≤ ∑ j, z_lo j * u j := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hbox j).1 (hz_lo j)
  linarith

#print axioms four_support_interval_sound
#print axioms lp_dual_upper_bound
#print axioms farkas_box_infeasibility_certificate

end Research.TransportCertificate
