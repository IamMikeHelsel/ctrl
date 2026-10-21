# Dispatch Log

## 2026-10-19T05:14:52Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
You are the Project Orchestrator for the research program.

Your working directory is:
/Users/mike/dev/ctrl/.agents/teamwork/orchestrator_1

The user's original request is recorded verbatim at:
/Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md

Project root workspace:
/Users/mike/dev/ctrl

Please read ORIGINAL_REQUEST.md and follow all requirements and acceptance criteria:
- Create a fresh branch in ~/dev/ctrl (sibling repos are read-only context); integrity mode: development
- Read context first: README.md, AGENTS.md (binding rules), docs/ (especially crossover-program-report-2026-10-18.md, targets.md, architecture.md, machines.md), lean/Research/ControlCertificates.lean, work/834/, data/erdos/; sibling repos ~/dev/ctrl-erdos-rename, ~/dev/ctrl-erdos-lab, ~/dev/ctrl-research-notebook, ~/dev/ctrls, ~/dev/LeanForControl
- Consider the candidate seeds from Mike on the 12-state centroidal SE(3) floating-base template (verify open claims against literature before investing)
- R1: Survey and triage across math, controls, and vision. Produce a ranked shortlist of attacks with cross-discipline transfers, prior-art checks, and falsification tests.
- R2: Rotate and push across disciplines in rounds, carrying techniques and artifacts. Long jobs may run on the Spark through `ctrl spark`.
- R3: Checked results meeting the repo contract (frozen challenge statements untouched, Lean build, axiom audit, ctrl check, evidence tiers).
- R4: Write findings report in docs/.
- Acceptance criteria: Integrity (no challenge statements edited, no human approval fabricated, Lean build + #print axioms clean with no sorry, novelty prior-art searches recorded), Substance (at least 3 cross-discipline attacks attempted across math, controls, and vision; at least one verified artifact or exact negative result with certificate; control certificate verified symbolically/exact arithmetic; independent reviewer agent re-runs checks).

Maintain your progress in progress.md and BRIEFING.md in your working directory. When complete, notify me with your victory claim.


## 2026-10-19T05:51:11Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Note from the parent agent (please relay to the team, M2 gate reviewers, and record in your BRIEFING.md / GATE_STATUS.md):

"I read lean/Research/LorentzConeCBF.lean. It is correct but elementary — the master theorem is 'Lorentz cone is convex + linear interpolation between u_nom and pi_b meets a linear inequality'. The genuinely hard content of Seed 1 is ASSUMED as hypotheses: `h_margin : b ≤ a·pi_b` (the backup policy has margin everywhere) and `h_denom`. There is no dynamics, no SE(3)/rotation, no Lie derivative along the centroidal template, and no forward-invariance argument. It must not be reported as 'closed-form friction-cone backup CBF on the centroidal template' — evidence tier for that claim is at most 'candidate / scaffolding'. To count as progress on Seed 1, the team should prove (exactly) that for the stated template + cone + bounds, the backup policy satisfies the margin condition on the whole safe set (i.e., discharge h_margin), or produce a counterexample showing where it fails. Please don't spend more rounds polishing this scaffolding; prioritise attacks that can yield a non-trivial checked artifact."

Appended to ORIGINAL_REQUEST.md. Please ensure Milestone 2 classification reflects "candidate / scaffolding", avoid over-polishing the scaffolding, and prioritize non-trivial checked artifacts across the remaining milestones (Vision, Math).


## 2026-10-19T05:57:09Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent note for orchestrator (recorded in ORIGINAL_REQUEST.md):

"M3 (Faugeras–Lustman in Lean) and M4 (rational SDP certificate tool) are infrastructure / formalization of known results — fine, but the plan shouldn't jump from them straight to M5 (report). Before writing the report, please run at least one more R2 'push' round that USES these tools on an actual open or improvable target: e.g. (a) feed the M4 rational-certificate pipeline a real bound from the active lanes (work/pod/mf13, work/pod/885, work/273, or a flag-algebra/SOS bound) and get it Lean-rechecked; (b) attempt to discharge the M2 h_margin condition exactly (SOS/interval) or find a counterexample; (c) a vision→control transfer such as a certified homography-based visual-servoing invariant. Prior-art check each before investing. The report should reflect what these push attempts actually achieved, including clear negatives."

Please update your `PROJECT.md`, `BRIEFING.md`, and milestone plan to include an R2 Push Phase executing on open/improvable targets using these tools before finalizing the report.


## 2026-10-19T06:17:41Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent note for orchestrator + all gate reviewers (recorded in ORIGINAL_REQUEST.md):

"I read lean/Research/HomographyDecomposition.lean. `PlanarHomographyDecomp H` takes BOTH decompositions (R_a,t_a,n_a),(R_b,t_b,n_b) with H = R + t nᵀ as structure fields — i.e. the actual Faugeras–Lustman content (existence of exactly two solutions from the SVD, R ∈ SO(3), uniqueness) is assumed, not proved. R is not even constrained to be a rotation. The '8 branches / 6 eliminated / 2+6=8' results are sign bookkeeping, and chirality depends on positivity facts passed in as hypotheses. Tier: formalization scaffolding, not a formalization of Faugeras–Lustman. Report it that way.

Process fix for M5 and all remaining gates: add a mandatory HYPOTHESIS AUDIT. For each headline theorem, reviewers must list every hypothesis/structure field and mark whether it encodes the crux of the claimed result. Any theorem whose crux is a hypothesis is capped at 'scaffolding', regardless of zero-sorry status. Also drop trivia like `2+6=8` from headline lists. A smaller theorem with no smuggled crux beats a large file of bookkeeping."

Please ensure:
1. M3 is classified and reported strictly as "formalization scaffolding".
2. Incorporate the mandatory HYPOTHESIS AUDIT into your Gate criteria for Milestone 5 and all subsequent reviews.
3. In Milestone 5 (R2 push round), focus on substantive results with no smuggled crux.


## 2026-10-19T06:37:23Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent note for orchestrator / worker_m5_push, before effort is sunk (recorded in ORIGINAL_REQUEST.md):

"- Push B: a_max = g·min(μ, W/h_G) is the textbook friction/tip-over (ZMP) braking limit for a rigid body on flat ground. A kernel-checked proof is a fine artifact but must be labelled 'formalization of known result', not new. Make it worth something: state the model explicitly (point-contact support polygon, flat ground, constant h_G, quasi-static?) and ideally go beyond the textbook case, e.g. the exact limit with the 3D Lorentz cone + support polygon jointly, sloped ground, or non-constant CoM height — and check prior art for that variant.
- Push C: 'positive depth preserved for all t ≥ 0 unconditionally' is very likely FALSE for homography-based visual servoing in general (camera retreat / Chaumette's conundrum, local minima, features leaving the view). Treat 'unconditionally' as a red flag. Specify the exact control law and closed-loop dynamics; then either prove invariance with explicit sufficient conditions (e.g. a specific decoupled law with a barrier on n·X) or produce a counterexample trajectory. A clean counterexample plus a conditional theorem is a better outcome than an 'unconditional' theorem with a hidden crux.
- Push A: name the specific open/improvable bound being certified, and why the certified value matters (does it beat or match the best known bound?). Certifying a known value of a known relaxation is tool validation, not a push."

Please relay immediately to worker_m5_push to calibrate the proofs, models, and certified bounds accordingly.


## 2026-10-19T06:52:25Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent HYPOTHESIS AUDIT of M5 & MANDATORY REDIRECT (recorded in ORIGINAL_REQUEST.md):

"Parent HYPOTHESIS AUDIT of M5 — please relay to orchestrator; M6 must not report these as pushes on open targets.

1. Push C `visual_servoing_depth_positive`: the closed loop is DEFINED as X(t)=e^{-λt}X0+(1-e^{-λt})X* (ideal Cartesian exponential convergence with perfect pose). Depth positivity is then 'a convex combination of positives is positive'. The crux (that a homography-based law actually produces this trajectory from image measurements with estimated n, d) is assumed. `chaumette_retreat_unbounded` defines z(t)=z0·e^{ct} and proves exponentials are unbounded — the IBVS dynamics are asserted, not derived. Tier: scaffolding.
2. Push B: 2D textbook ZMP/friction limit (label: known result). `deceleration_safe_3d_lorentz` assumes |a_x| ≤ min(√((μg)²−a_y²), gW/h) and concludes a_x²+a_y² ≤ (μg)² — a restatement. Tier: formalization of known result.
3. Push A — INTEGRITY ISSUE: `certify_lyapunov_contraction` uses a hand-invented 4×4 matrix A (comment: 'canonical centroidal…') and is labelled 'active lane (mf13)'. mf13 is the Byers–Nash n=6 lane and has nothing to do with that matrix. Remove the mf13 label; this is a toy Lyapunov example. The 44.5279 item remains the previously known negative relaxation result, now exact.

REDIRECT (most important): the repo already contains real, deep open-problem lanes that the pod has not engaged:
- work/pod/mf13 (Byers–Nash conjecture, n=6): reduced to an 11-parameter convex family; numerics say k−s ≤ 0 with equality sets; 'a proof for n=6 now looks more plausible'; stated Lean gap = normal-form lemma for rank≤4 real skew 6×6 matrices. This is where the rational SDP/SOS certificate tool genuinely fits: try to certify k(A) ≤ s(A) on the reduced family (exact SOS / rational certificate, handling the equality sets), and/or formalize the normal-form lemma.
- work/273: 11-smooth covering extension has only a Python certificate — needs independent audit + Lean.
- work/pod/885: 6×4 grids found (prior art: rediscovery); rational-column extension searched to q ≤ 10^6 — Spark-scale search or a structural (algebraic-geometry / elliptic-curve) obstruction to extension is the open step.
Read each lane's FINDINGS/PRIOR_ART first. Please spend the remaining effort (very large team authorized) on these, mf13 first, before M6. Toy controls/vision scaffolding should stop."

Execute this redirect immediately:
1. Reclassify M5 outputs as scaffolding/known result; remove the mf13 label from `push_sdp_cert.py`'s 4x4 toy Lyapunov example.
2. Direct your team (utilizing the very large team authorized) to work on the real open lanes (`work/pod/mf13` Byers-Nash n=6 first, then `work/273` and `work/pod/885`). Read each lane's FINDINGS/PRIOR_ART first.
3. Do not proceed to M6 report until genuine work is done on these open lanes.

## 2026-10-19T07:34:02Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent audit of the latest Byers–Nash (mf13) deliverables — relay to mf13 workers and gate reviewers:

1. certify_mf13_pair.py: Locus 1 (Common-T involution ⇒ s ≥ 1 = k) was already a known fact in the lane (explorer reported it as existing). Locus 2 certifies SPECIFIC rational sample pairs (e.g. card M05 at t=1/2, 1/3). Pointwise certificates do not prove k ≤ s over the 11-parameter family. Report as: 'exact pointwise certificates at N sample pairs + exact identity on known equality locus'. Do NOT describe it as certifying the family or the n=6 case. The real target is a certificate valid on the whole (reduced, compact after normalization) family: e.g. a polynomial SOS/Positivstellensatz certificate in the 11 outer parameters, or a branch-and-bound with interval/exact certificates covering the parameter domain (with the equality sets excised by a local argument). Say whether that is feasible and what blocks it.

## 2026-10-19T07:49:31Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent audit of SkewNormalForm.lean (605 lines) — relay immediately to mf13 Lean workers and gate reviewers:

"The new theorems `rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion` take K already in the form Q·skewWitness(a,b)·Qᵀ. That is exactly what work/pod/mf13/theory/SameSquareExclusion.lean ALREADY proved (FINDINGS M3: 'unconditional rank-2 and rank-4 same-square exclusion in Fin 6 for witnesses Q·skewWitness(a,b)·Qᵀ'). So this is a re-proof, not progress. The stated gap is still open: there is NO theorem in the file with a rank hypothesis, i.e. nothing of the form `∀ K : Mat, Kᵀ = -K → K.rank ≤ 4 → ∃ Q a b, Qᵀ*Q = 1 ∧ K = conjugate Q (skewWitness a b)`.

Please do not move to M6 claiming the normal-form gap is closed. Either deliver that exact theorem (spectral theorem on the symmetric PSD −K·K via Matrix.IsHermitian.eigenvectorBasis, pairing via skew_invariant_plane, kernel dimension ≥ 2 from rank ≤ 4 — the delicate part is choosing a K-adapted orthonormal basis when eigenvalues repeat; handle by working with eigenspaces of −K² and applying skew_invariant_plane inductively on orthogonal complements), plus the corollary composing it with the exclusion theorem for arbitrary skew K of rank ≤ 4; or report precisely what remains unproved. This is worth one focused push (possibly two parallel workers with different strategies / model types) before M6."


## 2026-10-19T08:10:01Z
Parent check and constructive proof plan for SkewRankFourNormalForm.lean — relay immediately to orchestrator, worker_mf13_lean_alt, and reviewers:

"The main theorem `skew_rank_le_four_normal_form` is still ABSENT. `general_rank_four_exclusion_of_normal_form` takes `h_nf : ∃ Q a b, … K = conjugate Q (skewWitness a b)` as a hypothesis — that hypothesis IS the gap. `ker_dim_ge_two` and `orthonormal_extension_pair` are genuine but auxiliary. Please don't hand off as done.

A proof plan that sidesteps the repeated-eigenvalue problem (only ONE eigenvector needed):
1. K = 0: take Q = 1, a = b = 0.
2. K ≠ 0: −K·K is Hermitian PSD (isHermitian_neg_sq) with trace ‖K‖_F² > 0, so some vector of its eigenvectorBasis has eigenvalue λ₁ > 0. Normalize to u₁; set v₁ := K u₁/√λ₁. skew_invariant_plane gives orthonormal u₁,v₁ with K u₁ = √λ₁ v₁, K v₁ = −√λ₁ u₁.
3. ker K has dim ≥ 2 (ker_dim_ge_two). u₁, v₁ ∈ range K (u₁ = −K v₁/√λ₁), and range K ⊥ ker K for skew K. So pick orthonormal z₁, z₂ ∈ ker K; they are automatically ⊥ u₁, v₁.
4. Extend (u₁,v₁,z₁,z₂) to an orthonormal basis (generalize orthonormal_extension_pair to 4 vectors); call the two new vectors u₂, w. W = span(u₂,w) = span(u₁,v₁,z₁,z₂)^⊥ is K-invariant (skew_orthogonal_plane_invariant / ker invariance). K u₂ ∈ W and u₂·K u₂ = 0 (skew), so K u₂ = β w for β = w·K u₂; by skewness K w = −β u₂. No eigen-decomposition needed for the second block.
5. Order/sign-adjust to match the hq0..hq5 convention (K q0 = −a q1, etc.: e.g. q0 = v₁, q1 = u₁ with a = √λ₁ — check signs), then apply skew_rank_four_normal_form_of_adapted_basis / orthonormal_basis_gives_skewWitness.
6. Compose with general_rank_four_exclusion_of_normal_form to get the hypothesis-free corollary for every skew K with rank ≤ 4.

If any step blocks, report exactly which lemma."

## 2026-10-19T08:25:16Z
From: d48063ba-6ffb-4cff-a95b-f6f38cadab89 (parent)
Content:
Parent note on SkewRankFourNormalForm.lean and M6 drafting — relay immediately to orchestrator, worker_mf13_lean_alt, and M6 report authors:

"The normal-form gap is now down to essentially one extraction lemma — worth finishing in PARALLEL with M6 drafting (don't block M6, but don't drop it).

Suggestions:
- Work with K as a linear map on E6 := EuclideanSpace ℝ (Fin 6) (Matrix.toEuclideanLin K).
- Let N := LinearMap.ker of it, get `2 ≤ finrank ℝ N` from ker_dim_ge_two (transfer via the linear equiv WithLp.linearEquiv / EuclideanSpace.equiv if needed).
- Then `stdOrthonormalBasis ℝ N` (Mathlib, Analysis.InnerProductSpace.PiL2) indexed by Fin (finrank ℝ N); take entries 0 and 1 (via Fin.castLE / the ≥2 bound) and coerce with Submodule.subtype — orthonormality is preserved (Orthonormal.comp / Submodule.coe_inner).
- Also confirm explicitly whether Step 4b (K acts on span(u₂,w) as β·J: K u₂ = β w, K w = −β u₂) and Step 5 (sign/order matching hq0..hq5) are proved, or also remaining.
- The M6 report must state precisely: 'normal-form lemma: proved modulo <exact lemma names>' unless the final hypothesis-free theorem `skew_rank_le_four_normal_form` compiles."
