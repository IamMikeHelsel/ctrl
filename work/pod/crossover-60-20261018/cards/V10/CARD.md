# V10: Global bounded-reprojection feasibility

**PM decision: GO for a bounded certificate-consumer experiment.** AI-written research.
Original question: Under positive depth and fixed versus unknown rotations, which
multiview maximum-reprojection-error subproblems admit convex feasibility certificates?

## Provenance and framing

Frozen provenance: `.agents/teamwork/explorer_survey_vision_1/handoff.md` in this repository,
SHA256 d3d5200ee80de5d5b2daf14199379f0b42d6a0e441b26e38cf368ae916700f3f.
It is a survey, not evidence that all algorithms or papers were checked. We checked the
[Hartley–Kahl author paper](https://users.cecs.anu.edu.au/~hartley/Papers/PDF/HartleyKahl:Ematrix.pdf)
and Kahl's [UCSD publication source](https://vision.ucsd.edu/publications/2005/multiple-view-geometry-and-l-infinity-norm).
Fixed-rotation convex subproblems and rotation search are established prior work. The
rotation paper uses angular errors; our concrete fixtures use Euclidean pixel error per
view, with maximum across views. They are not silently interchangeable.

With fixed cameras and fixed nonnegative threshold γ, positive-depth projection error
bounds become second-order-cone inequalities. With fixed rotations, translations and
unknown 3D points can also enter affinely in these subproblems. Unknown rotations introduce
nonconvex constraints and products. The feasibility sets are nested in γ, but the joint
parameter/γ epigraph need not be convex. No claim of a complete numerical SOCP oracle:
exact verification may return UNKNOWN when no valid primal/dual certificate is available.

## Three transfers

1. **Safety reachability to rotation-cell exclusion.** Enclose every camera in a declared
   rotation cell by enlarged nominal cones. A certificate of nominal infeasibility excludes
   that whole cell. Preserve fixed physical camera centers, calibrated projection and positive
   depth. Outer feasibility alone is not a realizable rotation witness.
2. **Convex dual separation to simple geometric certificates.** Opposing vertical residuals
   give a sharp exact lower bound, avoiding reliance on a solver's status. The invariant is
   actual reprojection error, not algebraic cross-multiplied error with unknown signs.
3. **Unexpected projective compactification and calibration lens.** A point escaping to
   infinity can turn an infimum into an apparent solution if finite-depth requirements are
   lost. Averaging rotations can instead imitate a change in focal calibration. Both are
   useful failure modes with exact falsifiers.

## Exact tests and results

- Fixed calibrated cameras P1=[I|0], P2=[I|(-1,0,0)], pixels(0,0),(-1,1/2):
  global minimum γ=1/4, uniquely attained at X=(0,1/4,1). Original pixel formulas,
  cone conversion, lower bound and uniqueness are kernel checked.
- General rectified stereo with baseline B>0, disparity d=u1−u2 and vertical discrepancy
  c=v2−v1 reduces at s=B/z>0 to squared minimax error ((s−d)²+c²)/4. Actual pixel
  identities, lower bound and balanced finite witness are kernel checked. For d>0, s=d
  minimizes; for d≤0 every finite s has a strict gap above (d²+c²)/4. Approach to the
  limit is a hand consequence of the checked exact gap polynomial.
- Equal pixels with unit stereo baseline have infimum0 but no finite zero-error point.
  Every positive threshold has a finite witness. A positive lower depth bound does not
  prevent escape. Adding an explicit upper depth cap Z changes the model and gives attained
  optimum1/(2Z). Six root statements check these facts.
- Unknown rotations: a valid rational Cayley-chart midpoint with positive depth fails
  γ=1/10 despite both endpoint poses fitting exactly. Separately, for known orthogonal
  points e1,e3, fixed center and pixels(+1/10,0),(−1/10,0), a FULL-RANK matrix in convSO3
  fits exactly with positive depths and determinant1/100; every true calibrated rotation
  has error≥9/10, attained by a 45-degree rotation. Exact rational/Qsqrt2 checks and five
  scalar kernel helpers support this; full matrix/9/10 composition is a hand derivation.
- Declared Cayley cubes [-1/100,1/100]^3 around I for each camera admit Frobenius-squared
  bound24/10003<1/400, hence operator budgetδ=1/20. At targetγ=1/10, positive constants
  U=9/8,M=3/2,K=8/5 give enlarged nominal threshold11/46<1/4. This excludes the entire
  specified two-camera cell under the hand norm/center transport derivation. Eleven root
  polynomial/scalar helpers check the algebra; 125 exact grid rotations independently
  check implementation, not universal coverage. Full norm/matrix assembly remains open.
- Negatives: same extrinsic t does not preserve the physical center; dropping the residual
  map norm M understates error; a squared Frobenius quantity is not its norm; nonpositive
  depth and singular/all-zero rays are not valid finite projections. A full-rank filter
  alone fails to repair convSO3. The conservative bound's δ<3/56 cutoff is not a true
  geometric feasibility threshold.

## Critique, evidence and decision

Independent critic replay covers proof axioms, literal camera binding, exact rotation and
rectified examples, and negative controls. See critic_acceptance.json, critic.md and
pm_cell_derivation.md. Root's first Cayley proof had a type error; failed source/log retained,
corrected version separately compiled. No numerical solver verdict is promoted as proof.

GO: after all60 initial reviews, one30-minute certificate consumer with a camera/metric/depth/
gauge manifest and one declared rotation-cell tree. Test20 prefrozen cases, require actual
finite positive-depth witnesses or independently verified exclusion certificates, preserve
UNKNOWN, and bind every search cell to its complete parent cover. No full global search,
novelty, physical camera or robotics validation is claimed.

Quality19/20=95/100: faithfulness4,reproducibility4,discrimination4,critique4,actionability3.
Subjective confidence is high for these explicit fixtures and low-to-unestablished for
production/global/physical extension; no calibrated success probability is assigned.

Final independent proof count:53 (domain27,critic4,inventor5,root17), all permitted axioms. Critic quality17/20 uses a separate rubric and is not the PM score.
