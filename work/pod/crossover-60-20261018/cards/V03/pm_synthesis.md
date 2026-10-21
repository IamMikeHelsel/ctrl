# PM synthesis and gate rationale

AI-written. Root PM with inherited-model domain, inventor and critic workers; exact runtime model identifiers unavailable. No alternate family actually contributed to V03. Earlier Kimi/Gemma authentication failures were not retried. No Spark inference or hardware commands occurred.

## Original question preserved

The inverse problem concerns calibrated two-view normalized bearings from an unknown static rigid scene. An alternative reconstruction may change unknown scene structure. This differs from pose with a known metric target. The source's epipolar identity is valid on its broad algebraic assumptions; the defect is interpretive prose, not a false Lean proof.

## What changes the next experiment

A local rank certificate, even combined with positive depths and noncoplanarity, can accept two globally distinct poses. The final inventor fixture supplies fourteen distinct image features, noncoplanar scenes in both reconstructions, and full local rank after removing translation scale. The competing reconstructions have different rotations and translation directions. A proposed estimator test must retain these alternatives rather than arbitrarily selecting the first or best-conditioned one.

The counterexample also supplies a positive test. Adding a transverse correspondence makes the unconstrained epipolar design rank eight and fixes the nonzero matrix line. For this special line, a direct proper-rotation/positive-depth argument gives global pose uniqueness up to positive translation scale. Zero translation must first be excluded using a bearing-angle mismatch; otherwise the zero matrix escapes a projective kernel-line argument. This entire conclusion is currently a mathematical derivation with a directly kernel-checked fixed-fixture matrix-line step and isolated Lean lemmas, not one complete Lean theorem.

## Connection to control and coding theory

Differential observability detects nearby changes and should be interpreted on a gauge quotient. It does not establish injectivity of the whole observation map. The fixed-unit-translation distant-plane family retains rank five for every positive tested parallax but its conditioning deteriorates without bound in the stated chart. This is a warning against using a Boolean rank label as an uncertainty margin.

Treating candidate image sets as code sets motivates an exclusion margin. Unlike a finite codebook, each camera pose induces a set through unknown depths; full finite positive-depth reconstruction remains necessary for acceptance. An algebraic epipolar line supplies a necessary condition useful for rejection. It is not an acceptance certificate. An interval that contains zero is therefore inconclusive, not evidence that a physical alternative exists.

## Exact matrix-box experiment

The PM experiment uses E_B=[[0,-2,0],[2,0,1],[0,1,0]] with a fixed registered scale. Each of its nine entries can vary independently by1/100, and each of four finite normalized-ray coordinates can vary by1/100. At the true-A depth2 correspondence x=(0,1/3,1), y=(1/2,1/3,1), every residual in this product box is positive:

    25667/90000 <= y^T E x <= 34369/90000.

This rejects the entire stated candidate-matrix box, including its physically admissible subset. It does not cover every competing pose or establish that this matrix uncertainty is physically justified. Multi-affinity makes box vertices sufficient; the optimized calculation was matched against all8192 vertices and independently reproduced with integer arithmetic by the critic. Negative controls at near-planar depth101/100 and critical direction v0 retain zero in the interval; increasing matrix uncertainty destroys the rejection. Rescaling E requires rescaling its uncertainty radius. The critic rejected corrupted bounds, radius metadata and a false acceptance.

The independent PM Cayley-rotation check verifies288 tangent entries using exact rational rotations and translation finite differences. It checks the differential formulas through a different path from the producer's cross-product implementation.

## Explicit critical branch mechanism

For any candidate F=[e]cross H with e=(a,b,c), the matrix is

    [[0,-c,b],[c,0,c-a],[-b,a,-b]].

An A-generated off-plane correspondence at first ray(u,v,1), depthZ, gives residual(1-1/Z)(cv-b). A critical v0 point forces b0. In that family the two nonzero Gram eigenvalues are a²+c² and c²+(c-a)². Equality reduces to c(c-2a)=0; excluding the zero matrix leaves exactly the two projective essential classes already exhibited. Thus the extra critical point can improve linear rank while preserving both physical branches. This is an explicit family analysis, not a general homography decomposition theorem. The PM Lean file checks the cubic entry and branch sufficiency for the displayed matrix family; connecting the entire family to all observations still requires the stated linear constraints.

## Literature and novelty boundary

The author-hosted [Hartley–Zisserman epipolar chapter](https://www.robots.ox.ac.uk/~vgg/hzbook/hzbook2/HZepipolar.pdf) supports scene-independent incidence and distinguishes calibrated matrix decomposition from matrix recovery. The [Torr–Fitzgibbon–Zisserman paper record](https://robots.ox.ac.uk/~vgg/publications/1998/Torr98c/) describes established degeneracy/model-selection work. [Bråtelund's author preprint record, version4](https://arxiv.org/abs/2112.05074v4) identifies projective critical configurations with quadrics; only its abstract/version metadata were checked here. The reduced quadric Y(Z-1)=0 is independently derived for our particular pair, not imported as a calibrated uniqueness theorem. Its 2024 revision flags a correction to the published table; no unreviewed table is relied on.

Malis–Vargas RR6303 was located, but the HAL full text returned access denied and the university repository returned403. No full-review claim or novelty assessment depends on that report. These are known types of ambiguity, with a concrete certificate-oriented research direction rather than a claimed new vision discovery.

## PM decision

GO for one thirty-minute certificate-interface experiment after all sixty initial reviews. Keep the scope bounded to exact synthetic candidates and independently checked rejection evidence. Predeclare at least twenty fixtures spanning planar, critical nonplanar, separating nonplanar, pure rotation and small parallax; include positive-depth, matrix-scale, stale-correspondence and candidate-omission mutations. Compare a residual-plus-local-rank acceptance rule with the layered certificate. A uniqueness label must require either a complete candidate cover or an independently checked sufficient linear/physical argument. Arbitrary candidate omission must fail closed.

Renew only if the experiment produces new evidence or a materially different discriminating test. General noisy global uniqueness, real calibration/model error, novel estimator performance and physical robot use remain HOLD. No source proposal edit, public CLI change or approved Challenge change is part of this review.
