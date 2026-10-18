/-
Checked-certificate replay candidate, generated from the existing exact cubic
Bernstein witness. This is shared-witness interoperability, NOT an independently
CSDP-discovered witness. The target and all hypotheses match SOSDiscovery.lean.
No search tactic occurs in this file; sos_witness checks rational identities.
-/
import SOS

open CPoly

namespace SameObjectComparison

noncomputable def residual (c h x v : ℝ) : ℝ :=
  (-5 * h ^ 3 - 4 * h ^ 2 + 6 * h + 4 - c) * x ^ 2 +
  2 * (-(15 / 2) * h ^ 3 - h ^ 2 + (9 / 2) * h) * x * v +
  (-(45 / 4) * h ^ 3 + 6 * h ^ 2 - 5 * h + 4 - c) * v ^ 2

theorem baseline_residual (h x v : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ 1 / 2) :
    0 ≤ residual 1 h x v := by
  unfold residual
  sos_witness
    { sigmas := [
      ([0], { terms := [
        ((24 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (2 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.X 1 + CMvPolynomial.C (3 / 16 : ℚ) * CMvPolynomial.X 2)),
        ((389 / 32 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (2 : ℚ) * CMvPolynomial.X 0) * CMvPolynomial.X 2),
        ((35 : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.X 1 + CMvPolynomial.C (17 / 70 : ℚ) * CMvPolynomial.X 2)),
        ((94 / 35 : ℚ), CMvPolynomial.X 0 * CMvPolynomial.X 2)] }),
      ([1], { terms := [
        ((6 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (2 : ℚ) * CMvPolynomial.X 0) * CMvPolynomial.X 1),
        ((6 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (2 : ℚ) * CMvPolynomial.X 0) * CMvPolynomial.X 2),
        ((112 : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.X 1 + CMvPolynomial.C (17 / 56 : ℚ) * CMvPolynomial.X 2)),
        ((943 / 28 : ℚ), CMvPolynomial.X 0 * CMvPolynomial.X 2)] })] }

#print axioms SameObjectComparison.baseline_residual

end SameObjectComparison
