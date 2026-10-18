/-
UNVERIFIED COMPARISON INPUT — NOT PART OF THE CHECKED LEAN ARTIFACT.

This source has not been elaborated. It is a proposed same-object benchmark for
leanprover/sos at fb7ae417609093f04cf0608dc92e9343550c2ae4.
Do not replace the lean-controls project's toolchain to run it. Use a separate
checkout of the SOS repository with its own pinned dependencies.

The transition and P are exactly those of benchmarks/double-integrator.json:
 A(h) = [[1-h², h-3h²/2], [-2h, 1-3h]], P = [[5,1],[1,1]].
 residual(c,h,x,v) = [x,v] ((P-A(h)^T P A(h))/h-cI) [x,v]^T,
 with the polynomial continuation at h=0.

The first theorem uses c=1 and H=1/2, as DoubleIntegrator.lean does.
The second uses c=1/100 and H=33/50, as DoubleIntegratorWide.lean does.

Discover with sos?, save its frozen sos_witness, then time/audit frozen replay
separately. Successful search, failure, timeout, and integration failure are
different outcomes. No success or performance claim is made by this file.
-/

import SOS

namespace SameObjectComparison

noncomputable def residual (c h x v : ℝ) : ℝ :=
  (-5 * h ^ 3 - 4 * h ^ 2 + 6 * h + 4 - c) * x ^ 2 +
  2 * (-(15 / 2) * h ^ 3 - h ^ 2 + (9 / 2) * h) * x * v +
  (-(45 / 4) * h ^ 3 + 6 * h ^ 2 - 5 * h + 4 - c) * v ^ 2

theorem baseline_residual (h x v : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ 1 / 2) :
    0 ≤ residual 1 h x v := by
  unfold residual
  sos?

theorem wide_residual (h x v : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ 33 / 50) :
    0 ≤ residual (1 / 100) h x v := by
  unfold residual
  sos?

#print axioms SameObjectComparison.baseline_residual
#print axioms SameObjectComparison.wide_residual

end SameObjectComparison
