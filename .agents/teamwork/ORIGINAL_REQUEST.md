# Original User Request

## 2026-10-19T05:12:50Z

Use a very large team of agents. Mike asked for an interdisciplinary pod that moves between math, controls, and machine-vision problems, using models of different types, and works hard on the most likely paths to a genuine new result. Run it as a research program over Mike's `~/dev/ctrl` lab (Erdős problems + control theory, Lean-checked, with a DGX Spark for long jobs). Lean into the cross-discipline transfers behind recent breakthroughs: LLM-guided evolutionary/symbolic search with fast verifiers (FunSearch, AlphaEvolve, Alfarano–Charton–Hayat backward synthesis of Lyapunov functions), SAT/SDP/flag-algebra certificates, Lyapunov/barrier/contraction certificates, and algebraic-geometric methods from vision (minimal problems, certifiable pose estimation). Purpose: exploration aimed at a real, checkable finding.

Working directory: ~/dev/ctrl (create a fresh branch; sibling repos are read-only context)
Integrity mode: development

## Context to read first
- `~/dev/ctrl`: `README.md`, `AGENTS.md` (binding rules), `docs/` — especially `crossover-program-report-2026-10-18.md` (evidence tiers, prior negative results), `targets.md`, `architecture.md`, `machines.md`; `lean/Research/ControlCertificates.lean`; `work/834/`; `data/erdos/`.
- `~/dev/ctrl-erdos-rename` history notes Erdős 834 was already claimed upstream — treat it as a pilot, not a novelty target; it has a `./ctrl triage` prior-art gate.
- `~/dev/ctrl-erdos-lab` (formalizations of #261, #931, #834), `~/dev/ctrl-research-notebook` (control pods, recovery manuscript, and vision proposals `docs/proposals/01_planar_homography.md`, `03_information_filter.md`), `~/dev/ctrls`, `~/dev/LeanForControl`.

## Candidate seeds from Mike (starting points, not mandates; verify every "open" claim against the literature before investing)
Work on the 12-state centroidal SE(3) floating-base template (Sleiman et al. arXiv:2103.00946), where certificates would transfer to legged/aerial/manipulator robots via centroidal QPs, and where polynomial SOS struggles (SO(3) trig terms, √ friction cones, quadratic drag) but symbolic search + fast checking does not:
1. Closed-form backup CBF with a Lorentz friction-cone input set (cf. van Wijk et al. arXiv:2510.05436 for box inputs; Cohen–Molnar–Ames arXiv:2403.09865).
2. Closed-form control contraction metric on underactuated SE(3) (cf. Wu–Yi–Manchester arXiv:2403.15264; Manchester–Slotine arXiv:1503.03144).
3. Closed-form IDA-PBC energy-shaping solutions for coupled contact + drag on a floating base (cf. arXiv:2607.04719, arXiv:2610.05755), possibly via backward synthesis (arXiv:2410.08304).

## Requirements

### R1. Survey and triage
Inventory open problems across the listed repos and the seeds above, spanning math, controls, and vision. Produce a ranked shortlist of attacks; each entry names its cross-discipline transfer, a prior-art check, and a falsification test.

### R2. Rotate and push
Work the shortlist in rounds, moving between disciplines and carrying techniques and artifacts from one to the next. Drop paths that fail their falsification test and record why. Long jobs may run on the Spark through `ctrl spark`, and cloud credits may be used where a measured bottleneck justifies it.

### R3. Checked results
Each claimed result meets the repo contract: frozen challenge statements untouched, Lean build, axiom audit, `ctrl check` where it applies. Otherwise it is labelled with its evidence tier from the crossover report (kernel-checked / exact computation / candidate / unsupported). Citing published results is allowed. Numerical grid checks alone count only as "candidate".

### R4. Report
Write a findings report in `docs/` covering what was tried, what was found, the evidence tier and prior-art status of each claim, negative results, and the recommended next experiment.

## Acceptance Criteria

### Integrity
- [ ] No challenge statement edited and no human approval fabricated (per `AGENTS.md`); work is on a new branch
- [ ] Every claimed theorem builds, and `#print axioms` shows only the default tier, with no `sorry`
- [ ] Every claim of novelty has a recorded prior-art search (arXiv, erdosproblems.com, Formal Conjectures, Google Scholar), with links

### Substance
- [ ] At least 3 distinct cross-discipline attacks attempted, covering all three of math, controls, and vision
- [ ] At least one attack produces a kernel-checked or exactly verified (symbolic/rational) artifact that did not exist at the start, OR an exact negative result with a certificate
- [ ] For any control certificate, the defining inequality is verified symbolically or by exact/interval arithmetic over the stated domain, not only by sampling
- [ ] An independent reviewer agent (a different model from the producer) re-runs every check listed in the report and confirms that it reproduces


## 2026-10-19T05:50:31Z

Note from the parent agent (please relay to orchestrator and the M2 gate reviewers): I read lean/Research/LorentzConeCBF.lean. It is correct but elementary — the master theorem is "Lorentz cone is convex + linear interpolation between u_nom and pi_b meets a linear inequality". The genuinely hard content of Seed 1 is ASSUMED as hypotheses: `h_margin : b ≤ a·pi_b` (the backup policy has margin everywhere) and `h_denom`. There is no dynamics, no SE(3)/rotation, no Lie derivative along the centroidal template, and no forward-invariance argument. It must not be reported as "closed-form friction-cone backup CBF on the centroidal template" — evidence tier for that claim is at most "candidate / scaffolding". To count as progress on Seed 1, the team should prove (exactly) that for the stated template + cone + bounds, the backup policy satisfies the margin condition on the whole safe set (i.e., discharge h_margin), or produce a counterexample showing where it fails. Please don't spend more rounds polishing this scaffolding; prioritise attacks that can yield a non-trivial checked artifact.


## 2026-10-19T05:56:41Z

Parent note for orchestrator: M3 (Faugeras–Lustman in Lean) and M4 (rational SDP certificate tool) are infrastructure / formalization of known results — fine, but the plan shouldn't jump from them straight to M5 (report). Before writing the report, please run at least one more R2 'push' round that USES these tools on an actual open or improvable target: e.g. (a) feed the M4 rational-certificate pipeline a real bound from the active lanes (work/pod/mf13, work/pod/885, work/273, or a flag-algebra/SOS bound) and get it Lean-rechecked; (b) attempt to discharge the M2 h_margin condition exactly (SOS/interval) or find a counterexample; (c) a vision→control transfer such as a certified homography-based visual-servoing invariant. Prior-art check each before investing. The report should reflect what these push attempts actually achieved, including clear negatives.


## 2026-10-19T06:17:13Z

Parent note for orchestrator + all gate reviewers (second instance of the same pattern): I read lean/Research/HomographyDecomposition.lean. `PlanarHomographyDecomp H` takes BOTH decompositions (R_a,t_a,n_a),(R_b,t_b,n_b) with H = R + t nᵀ as structure fields — i.e. the actual Faugeras–Lustman content (existence of exactly two solutions from the SVD, R ∈ SO(3), uniqueness) is assumed, not proved. R is not even constrained to be a rotation. The '8 branches / 6 eliminated / 2+6=8' results are sign bookkeeping, and chirality depends on positivity facts passed in as hypotheses. Tier: formalization scaffolding, not a formalization of Faugeras–Lustman. Report it that way.

Process fix for M5 and all remaining gates: add a mandatory HYPOTHESIS AUDIT. For each headline theorem, reviewers must list every hypothesis/structure field and mark whether it encodes the crux of the claimed result. Any theorem whose crux is a hypothesis is capped at 'scaffolding', regardless of zero-sorry status. Also drop trivia like `2+6=8` from headline lists. A smaller theorem with no smuggled crux beats a large file of bookkeeping.


## 2026-10-19T06:36:52Z

Parent note for orchestrator / worker_m5_push, before effort is sunk:
- Push B: a_max = g·min(μ, W/h_G) is the textbook friction/tip-over (ZMP) braking limit for a rigid body on flat ground. A kernel-checked proof is a fine artifact but must be labelled 'formalization of known result', not new. Make it worth something: state the model explicitly (point-contact support polygon, flat ground, constant h_G, quasi-static?) and ideally go beyond the textbook case, e.g. the exact limit with the 3D Lorentz cone + support polygon jointly, sloped ground, or non-constant CoM height — and check prior art for that variant.
- Push C: 'positive depth preserved for all t ≥ 0 unconditionally' is very likely FALSE for homography-based visual servoing in general (camera retreat / Chaumette's conundrum, local minima, features leaving the view). Treat 'unconditionally' as a red flag. Specify the exact control law and closed-loop dynamics; then either prove invariance with explicit sufficient conditions (e.g. a specific decoupled law with a barrier on n·X) or produce a counterexample trajectory. A clean counterexample plus a conditional theorem is a better outcome than an 'unconditional' theorem with a hidden crux.
- Push A: name the specific open/improvable bound being certified, and why the certified value matters (does it beat or match the best known bound?). Certifying a known value of a known relaxation is tool validation, not a push.


## 2026-10-19T06:51:28Z

Parent HYPOTHESIS AUDIT of M5 — please relay to orchestrator; M6 must not report these as pushes on open targets.

1. Push C `visual_servoing_depth_positive`: the closed loop is DEFINED as X(t)=e^{-λt}X0+(1-e^{-λt})X* (ideal Cartesian exponential convergence with perfect pose). Depth positivity is then 'a convex combination of positives is positive'. The crux (that a homography-based law actually produces this trajectory from image measurements with estimated n, d) is assumed. `chaumette_retreat_unbounded` defines z(t)=z0·e^{ct} and proves exponentials are unbounded — the IBVS dynamics are asserted, not derived. Tier: scaffolding.
2. Push B: 2D textbook ZMP/friction limit (label: known result). `deceleration_safe_3d_lorentz` assumes |a_x| ≤ min(√((μg)²−a_y²), gW/h) and concludes a_x²+a_y² ≤ (μg)² — a restatement. Tier: formalization of known result.
3. Push A — INTEGRITY ISSUE: `certify_lyapunov_contraction` uses a hand-invented 4×4 matrix A (comment: 'canonical centroidal…') and is labelled 'active lane (mf13)'. mf13 is the Byers–Nash n=6 lane and has nothing to do with that matrix. Remove the mf13 label; this is a toy Lyapunov example. The 44.5279 item remains the previously known negative relaxation result, now exact.

REDIRECT (most important): the repo already contains real, deep open-problem lanes that the pod has not engaged:
- work/pod/mf13 (Byers–Nash conjecture, n=6): reduced to an 11-parameter convex family; numerics say k−s ≤ 0 with equality sets; 'a proof for n=6 now looks more plausible'; stated Lean gap = normal-form lemma for rank≤4 real skew 6×6 matrices. This is where the rational SDP/SOS certificate tool genuinely fits: try to certify k(A) ≤ s(A) on the reduced family (exact SOS / rational certificate, handling the equality sets), and/or formalize the normal-form lemma.
- work/273: 11-smooth covering extension has only a Python certificate — needs independent audit + Lean.
- work/pod/885: 6×4 grids found (prior art: rediscovery); rational-column extension searched to q ≤ 10^6 — Spark-scale search or a structural (algebraic-geometry / elliptic-curve) obstruction to extension is the open step.
Read each lane's FINDINGS/PRIOR_ART first. Please spend the remaining effort (very large team authorized) on these, mf13 first, before M6. Toy controls/vision scaffolding should stop.


## 2026-10-19T07:10:38Z

Parent note for orchestrator: (1) 885 genus-49 claim — before anything builds on it, verify smoothness and genus computationally (Jacobian criterion / Gröbner basis or Magma/Sage/Macaulay2 if available; genus 49 matches 5 quadrics in P^6 only if the intersection is a smooth complete intersection). Record the exact equations. (2) No worker is currently assigned to 885's real next step. If capacity allows (very large team authorized), dispatch one: find low-genus quotients (automorphisms from the grid's symmetries → maps to elliptic/genus-2 curves), compute ranks, and attempt Chabauty/2-cover descent to determine rational points on a quotient — that would prove non-extendability of the known 6×4 classes, a genuinely new, checkable result. Prior-art check first (erdosproblemaday 885, Choudhry arXiv:2508.07806). (3) mf13 cert: watch the equality sets (k=s on the rank-4 ridge and at K=Y=diag(J,2J,3J)) — a strict SDP certificate cannot exist there; the certificate must be non-strict / exact-SOS, or the domain must exclude neighbourhoods with a separate argument. Hypothesis audit applies.


## 2026-10-19T07:21:54Z

Parent audit of tools/verify_885_geometry.py — please relay to orchestrator and worker_885_quotients; also flag to gate reviewers.
- Smoothness/genus 49 for the diagonal quadric intersection: plausible and the Jacobian-minor argument looks right in outline (accept after reviewer check; the minor-formula check is on a single sample point — the general product formulas should be verified symbolically, e.g. with sympy, not at one point).
- 'Chabauty obstruction verified' is FALSE as stated. There is no Chabauty computation anywhere in the file. The 'obstruction_summary' just restates the q ≤ 10^6 search ('OBSTRUCTED: No 5th column exists for q ≤ 10^6'), which is a bounded search, not an obstruction. Must be reported as: bounded search negative + Faltings finiteness (non-effective).
- `verify_mazur_rank_lower_bound` checks only the triple (0,1,2) yet concludes rank ≥ 1 for all 20 E_ijk. Either loop over all 20 or narrow the claim.
- Important consequence: if the E_ijk have rank ≥ 1, plain Chabauty on them is unavailable — that's a real negative finding worth stating. The live route is the 6 genus-2 quotients W² = ∏_{m≠r}(X+u_m): need 2-Selmer rank bounds for their Jacobians (Chabauty needs rank J < 2), or elliptic Chabauty / 2-cover descent over number fields. This needs real tooling: no Sage/Magma/M2 on the Mac. Options: PARI/GP (brew install pari; ellrank, hyperellratpoints for search, genus-2 tools limited), Sage via conda-forge/docker on the Spark, or Magma online calculator (small inputs). Report honestly what could and could not be computed. Do not label anything 'obstructed' without an actual descent/Chabauty certificate.


## 2026-10-19T07:33:32Z

Parent audit of the latest Byers–Nash (mf13) deliverables — relay to orchestrator, mf13 workers, and gate reviewers.
1. certify_mf13_pair.py: Locus 1 (Common-T involution ⇒ s ≥ 1 = k) was already a known fact in the lane (explorer reported it as existing). Locus 2 certifies SPECIFIC rational sample pairs (e.g. card M05 at t=1/2, 1/3). Pointwise certificates do not prove k ≤ s over the 11-parameter family. Report as: 'exact pointwise certificates at N sample pairs + exact identity on known equality locus'. Do NOT describe it as certifying the family or the n=6 case. The real target is a certificate valid on the whole (reduced, compact after normalization) family: e.g. a polynomial SOS/Positivstellensatz certificate in the 11 outer parameters, or a branch-and-bound with interval/exact certificates covering the parameter domain (with the equality sets excised by a local argument). Say whether that is feasible and what blocks it.
2. SkewNormalForm.lean: the building blocks are genuine (skew_invariant_plane is real content). But `orthonormal_basis_gives_skewWitness` takes the adapted orthonormal basis and its K-action as hypotheses — the existence of that basis (the actual normal-form lemma) is still unproved. Close it: −K·K is symmetric PSD, so Mathlib's `Matrix.IsHermitian.eigenvectorBasis` / `Matrix.IsHermitian.spectral_theorem` gives an orthonormal eigenbasis; pair eigenvectors via skew_invariant_plane, use rank ≤ 4 to get a ≥2-dim kernel. Deliver a theorem of the form `∀ K skew, rank K ≤ 4 → ∃ Q orthogonal, ∃ a b, K = Q·skewWitness a b·Qᵀ` with no basis hypotheses, then plug it into SameSquareExclusion to close the stated gap. That would be a real, checkable contribution to the lane.


## 2026-10-19T07:49:18Z

Parent audit of SkewNormalForm.lean (605 lines): the new theorems `rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion` take K already in the form Q·skewWitness(a,b)·Qᵀ. That is exactly what work/pod/mf13/theory/SameSquareExclusion.lean ALREADY proved (FINDINGS M3: 'unconditional rank-2 and rank-4 same-square exclusion in Fin 6 for witnesses Q·skewWitness(a,b)·Qᵀ'). So this is a re-proof, not progress. The stated gap is still open: there is NO theorem in the file with a rank hypothesis, i.e. nothing of the form `∀ K : Mat, Kᵀ = -K → K.rank ≤ 4 → ∃ Q a b, Qᵀ*Q = 1 ∧ K = conjugate Q (skewWitness a b)`. Please do not move to M6 claiming the normal-form gap is closed. Either deliver that exact theorem (spectral theorem on the symmetric PSD −K·K via Matrix.IsHermitian.eigenvectorBasis, pairing via skew_invariant_plane, kernel dimension ≥ 2 from rank ≤ 4 — the delicate part is choosing a K-adapted orthonormal basis when eigenvalues repeat; handle by working with eigenspaces of −K² and applying skew_invariant_plane inductively on orthogonal complements), plus the corollary composing it with the exclusion theorem for arbitrary skew K of rank ≤ 4; or report precisely what remains unproved. This is worth one focused push (possibly two parallel workers with different strategies / model types) before M6.


## 2026-10-19T08:09:40Z

Parent check of SkewRankFourNormalForm.lean (731 lines): the main theorem `skew_rank_le_four_normal_form` is still ABSENT. `general_rank_four_exclusion_of_normal_form` takes `h_nf : ∃ Q a b, … K = conjugate Q (skewWitness a b)` as a hypothesis — that hypothesis IS the gap. `ker_dim_ge_two` and `orthonormal_extension_pair` are genuine but auxiliary. Please don't hand off as done. A proof plan that sidesteps the repeated-eigenvalue problem (only ONE eigenvector needed):
1. K = 0: take Q = 1, a = b = 0.
2. K ≠ 0: −K·K is Hermitian PSD (isHermitian_neg_sq) with trace ‖K‖_F² > 0, so some vector of its eigenvectorBasis has eigenvalue λ₁ > 0. Normalize to u₁; set v₁ := K u₁/√λ₁. skew_invariant_plane gives orthonormal u₁,v₁ with K u₁ = √λ₁ v₁, K v₁ = −√λ₁ u₁.
3. ker K has dim ≥ 2 (ker_dim_ge_two). u₁, v₁ ∈ range K (u₁ = −K v₁/√λ₁), and range K ⊥ ker K for skew K. So pick orthonormal z₁, z₂ ∈ ker K; they are automatically ⊥ u₁, v₁.
4. Extend (u₁,v₁,z₁,z₂) to an orthonormal basis (generalize orthonormal_extension_pair to 4 vectors); call the two new vectors u₂, w. W = span(u₂,w) = span(u₁,v₁,z₁,z₂)^⊥ is K-invariant (skew_orthogonal_plane_invariant / ker invariance). K u₂ ∈ W and u₂·K u₂ = 0 (skew), so K u₂ = β w for β = w·K u₂; by skewness K w = −β u₂. No eigen-decomposition needed for the second block.
5. Order/sign-adjust to match the hq0..hq5 convention (K q0 = −a q1, etc.: e.g. q0 = v₁, q1 = u₁ with a = √λ₁ — check signs), then apply skew_rank_four_normal_form_of_adapted_basis / orthonormal_basis_gives_skewWitness.
6. Compose with general_rank_four_exclusion_of_normal_form to get the hypothesis-free corollary for every skew K with rank ≤ 4.
If any step blocks, report exactly which lemma.


## 2026-10-19T08:24:58Z

Parent note: the normal-form gap is now down to essentially one extraction lemma — worth finishing in PARALLEL with M6 drafting (don't block M6, but don't drop it). Suggestions: work with K as a linear map on E6 := EuclideanSpace ℝ (Fin 6) (Matrix.toEuclideanLin K), let N := LinearMap.ker of it, get `2 ≤ finrank ℝ N` from ker_dim_ge_two (transfer via the linear equiv WithLp.linearEquiv / EuclideanSpace.equiv if needed), then `stdOrthonormalBasis ℝ N` (Mathlib, Analysis.InnerProductSpace.PiL2) indexed by Fin (finrank ℝ N); take entries 0 and 1 (via Fin.castLE / the ≥2 bound) and coerce with Submodule.subtype — orthonormality is preserved (Orthonormal.comp / Submodule.coe_inner). Also confirm explicitly whether Step 4b (K acts on span(u₂,w) as β·J: K u₂ = β w, K w = −β u₂) and Step 5 (sign/order matching hq0..hq5) are proved, or also remaining. The M6 report must state precisely: 'normal-form lemma: proved modulo <exact lemma names>' unless the final hypothesis-free theorem `skew_rank_le_four_normal_form` compiles.
