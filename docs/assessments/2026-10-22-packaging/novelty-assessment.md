# What is new, what is established, and what could become significant

22 October 2026. AI-assisted assessment by the inventor role. This is a representative seven-claim review of the current artifacts, with fresh primary-source checks; it is not a systematic literature review of every theorem or all 60 campaign questions. Source and research receipts were inspected, but proofs and simulations were not rebuilt for this assessment. No external review, submission, outreach or priority registration occurred.

## Assessment

**Much of the mathematics we are using is established, often substantially older than twenty years. Our most defensible contribution today is formalization, precise application-specific derivation, independent checking and integration of those ingredients.** There are narrower candidate insights whose priority is unresolved. The inspected work does not yet establish a major new mathematical result or an award-level engineering advance.

That does not make it merely repackaging. Finding the right restricted model, proving its exact contract, producing counterexamples to tempting generalizations, and delivering an independently checkable implementation can be substantive research. But three different claims must remain separate: “we derived it,” “this implementation is new,” and “nobody previously knew the result.” Only the first two can currently be supported for much of this work, and implementation novelty still needs comparison with actual prior tools.

The strongest prospective distinction is a reliable path from a frozen engineering question through exact certificates to a small usable component. That path is incomplete today: a theorem-name decorator is provenance, not a proof that Python/C/ST refines Lean; simulation is not physical acceptance; and individual checked components do not automatically establish their composition.

## Grading vocabulary

These grades describe **evidence for mathematical novelty**, not utility, code quality or probability of winning an award:

- **N0 — established:** the central mathematical idea is known; no new-mathematics claim is justified.
- **N1 — specific candidate:** a concrete specialization, derived result or method is identifiable, but priority/significance is unresolved.
- **N2 — defended new contribution:** a precise difference from the closest prior work survives a serious comparison and independent technical scrutiny.
- **N3 — significant independently validated advance:** the new contribution solves a consequential open limitation and has independent validation.

None of the seven inspected claims presently earns N2 or N3 on the evidence reviewed. That is a statement about the evidence available, not proof that no original contribution exists. Formalization and engineering contributions have their own acceptance path and do not need to masquerade as new mathematics.

| Claim | Current mathematical-novelty grade | Defensible contribution now | Next discriminator |
|---|---|---|---|
| LQR/Kalman/Sontag foundation | N0 | Lean formalization and reusable identities, with implementation bindings still requiring scrutiny | Compare exact signatures and axioms with current formal libraries; demonstrate one independently usable verified component |
| Septic energy family | N1 for the exact family result; N0 for polynomial energy optimization generally | Explicit exact trade-off/counterexample and model-scoped certificate | Compare the same task, physical objective and constraints with closest energy planners and broader optimization |
| Four-contact circular-cone allocation | N1 for the exact restricted construction; broad closed-form-wrench claim N0 | Constructive, kernel-checked allocator under a specific rectangular stance model | Establish the exact prior-art delta and test generalized geometry/friction/torque constraints |
| S12 joint evidence → support certificates → guard | N0 ingredients; N1 integration method | Source-bound producer/consumer, exact sufficiency/completeness distinctions and misuse controls | End-to-end update/context/target refinement against an existing verifier and optimized baseline |
| M12 structured online Boolean product | N0 for the examined algorithmic ideas | Checked restrictions, semantic negatives and representation adapters | Real application structure plus complete costs; a provable improvement beyond the matching prior bound if claiming algorithm novelty |
| MF13 six-dimensional norm question | N1 certificate/search method; original question unsolved here | Exact hard-class diagnostics and restricted lower certificates | Prove the original universal statement or produce a strict exact counterexample |
| Timing/monitor/guard composition | N0 elementary bounds; N1 possible composition result | Explicit timing/model assumptions and counterexamples to unsafe interfaces | A complete theorem and implementation connection across an actual asynchronous execution protocol |

## 1. Classical control and estimation

Kalman's original 1960 papers establish the linear-quadratic control and filtering foundations; Sontag's 1989 paper supplies the universal stabilization construction. These are primary precedents, not recent inventions of this project. The local `BacksteppingCLF.lean` itself explicitly follows established work. [Kalman optimal-control paper](https://www.ee.iitb.ac.in/~belur/ee640/optimal-classic-paper.pdf), [Kalman filtering paper](https://eceweb1.rutgers.edu/~gajic/pdffiles/519KalmanFiltering/kalman1960.pdf), [Sontag 1989](https://www.sontaglab.org/FTPDIR/art-sycon8903.pdf)

Our `lean/ControlsLean/Estimation/KalmanOptimality.lean` formalizes covariance algebra and completion of squares under stated matrix hypotheses. That is useful formal work; the algebraic theorem must not be inflated into a newly invented estimator or an automatically verified stochastic sensor stack. Likewise, an inverse-free or spectral-free proof can be an elegant proof-engineering contribution without changing the classical mathematical result.

“First in our repository” is a defensible local scope. “First anywhere formalized” needs a dated search across Lean, Isabelle, Coq and other systems, exact theorem comparison and axiom accounting. The current [LeanForControl repository](https://github.com/AnandGokhale/LeanForControl) already formalizes linear systems/control and explicitly discusses proof assumptions and prose/signature drift. Its existence neither establishes nor refutes priority for our exact lemmas; it makes a blanket priority claim inappropriate.

**Next:** select one useful theorem/API pair, compare the full assumptions and conclusion with current formal predecessors, and prove or independently validate its implementation connection. The value could be a dependable component that other control users adopt, rather than a new control law.

## 2. Seventh-degree trajectories and energy

The exact local family is

`qη(s) = 10s³ − 15s⁴ + 6s⁵ + η s³(1−s)³(2s−1)`.

It preserves rest-to-rest position, velocity and acceleration endpoints. `lean/Research/RobotEnergySmoothness.lean` gives exact integrals including `Ia = 2(η+11)²/77 + 14` and `Ij = 720 + 4η²`. At η = −11 the acceleration-squared integral is 11/60 below the quintic baseline, while jerk-squared increases. This is a precise and useful counterexample to treating minimum jerk as minimum electrical energy. The η = −11 optimum applies to that acceleration term and family; a weighted motor-loss objective generally chooses a different η, and actuator constraints can change feasibility.

Neither seventh-degree trajectories nor optimizing robot energy is new as a category. Ata's 2022 primary paper explicitly selects a seventh-degree trajectory to study motor-cycle energy, jerk and joint torque. Only its publisher abstract was accessible in this pass: it establishes broad overlap, **not identity with our coefficients, model or theorem**. [Ata, Energy Consumption-Based Trajectory Planning for Manipulators](https://journals.sagepub.com/doi/10.3233/ATDE220577)

Our derivation may be independently produced and its exact closed-form trade-off worth publishing as a small result, but it is a low-dimensional quadratic optimization after polynomial integration. That alone is not evidence of a major mathematical advance. The [R08 card](../../../work/pod/crossover-60-20261018/cards/R08/CARD.md) properly limits the evidence to declared port models, matched constraints and family optima. README simulation percentages are separate observations, not novelty measurements.

**Next:** obtain the closest full texts; compare boundary conditions and objectives line by line. Then compare against a constrained energy optimizer, not only a minimum-jerk baseline, at matched duration, task, current/voltage/jerk limits and energy port. A meaningful result would be a demonstrated general mechanism, a useful provable approximation bound, or an independently reproduced practical gain under realistic losses. The specific family formula's priority remains open.

## 3. Four-contact allocation under friction cones

`lean/Research/LorentzConeCBF.lean` constructs bilinear normal loads on four rectangular corners and assigns tangential loads proportionally. It proves the net force, zero centroidal torque and individual circular-cone admissibility under rectangular ZMP and friction-disk bounds. This is a concrete constructive specialization, not a general six-dimensional wrench solver, arbitrary-contact optimizer or complete robot controller.

Caron, Pham and Nakamura already published closed-form rectangular contact-wrench conditions in 2015. Therefore “closed form instead of an online optimization for rectangular contacts” is too broad a novelty claim. Their general wrench treatment includes yaw constraints, while our selected construction fixes zero angular-momentum drift. Their analytical rectangular treatment and our circular-cone sufficient construction require an assumption-by-assumption comparison; this review does not assert they are identical. [Primary paper](https://arxiv.org/html/1501.04719v1)

The bilinear weights and common shear ratio make the local proof particularly simple. That simplicity is useful engineering, but does not by itself establish priority or a superiority claim over a solver handling more general constraints. A nanosecond formula timing omits sensing, state validation, fallback selection, command publication and actuation.

**Next:** write the precise feasibility domain and compare it with existing wrench-cone constructions; then test asymmetric geometry, unequal friction, individual force limits and nonzero angular momentum. Retain the original case as a regression. A broader necessary-and-sufficient characterization or a materially more general certified allocator would be a stronger contribution than another unconstrained timing comparison.

## 4. S12 predicate-specific certificate compilation

The mathematical reduction is clear: for `ρ∈[0,1]`, `w+c+ρd` lies between its two endpoint expressions. Four supports, in directions `±w` and `±(w+d)`, suffice for the declared static correction predicate. LP dual witnesses certify upper bounds, primal witnesses establish attainment, and Farkas witnesses certify empty branches. Convex duality and support-function reasoning are established mathematics; producer/checker separation also predates this work by decades. [Boyd–Vandenberghe author-hosted text and materials](https://web.stanford.edu/~boyd/cvxbook/), [Necula's proof-carrying-code research](https://people.eecs.berkeley.edu/~necula/papers.html)

The potentially distinctive contribution is the **faithful integration contract**: complete branches, external context binding, current nonemptiness, exact versus conservative certificates, preservation of joint state for future updates, and bounded runtime representation. The [S12 record](../../../work/pod/crossover-60-20261018/extensions/S12-B01/inventor.md) includes a real mutable-receipt bug and repair. It also reports no Python speed advantage. Neither those finite tests nor the Lean generic lemmas yet prove a complete PLC execution path.

**Next:** freeze a sequence of tightening, relaxation, duplicated observations and simultaneous context changes. Prove the update/publication/use protocol, implement one target, and compare complete cost with an optimized baseline that can cache the same supports. Show a capability that prior certificate/abstract-interpretation systems do not already supply under the same assumptions. That could become a credible formal-methods contribution; “four supports are enough here” alone is elementary.

## 5. M12 structured Boolean multiplication

The original OMv problem requires answering each arriving vector before observing the next, for an arbitrary fixed Boolean matrix. Our interval rows, supplied templates and sparse/temporal corrections impose special structure. The 2021 Gąsieniec–Jansson–Levcopoulos–Lingas–Persson paper already treats clustered rows and arriving vectors; its algorithms include signed differentiating blocks and prefix sums. This is direct prior art, not merely a superficial analogy. [Original OMv formulation](https://arxiv.org/abs/1511.06773), [2021 primary paper, section 3](https://www.df.lth.se/~jj/Publications/OMv_conj6_JCSS_2021.pdf)

The [M12 card](../../../work/pod/crossover-60-20261018/cards/M12/CARD.md) already acknowledges this. Its credible output is checked Boolean semantics, online-causality controls, and exact failure boundaries for proposed geometry/representation adapters. A small cost under small interval count, template count or Hamming change is not a general OMv advance. A new combination of two known optimizations may be useful without being a new algorithmic principle.

**Next:** establish that one real control/vision workload has the required structure after charging construction, updates, input/output and precision. Compare with the closest clustered algorithm and ordinary bitset implementations. An algorithm-novelty claim needs an improved bound or a genuinely different class with a meaningful separation, not a favorable toy dataset.

## 6. MF13 and the unresolved six-dimensional case

The August 2026 Kressner–Vandereycken paper gives an exact seven-dimensional counterexample, extends it to higher dimensions, and explicitly leaves dimension six open. The inspected source is current primary evidence for that status; this is not an exhaustive search for subsequent announcements. [Primary paper](https://arxiv.org/abs/2608.20875)

Our [M05-B01 extension](../../../work/pod/crossover-60-20261018/extensions/M05-B01/CARD.md) does **not** settle dimension six. Its initial bank was biased toward a known common-grading mechanism and partly reused calibration; the report correctly preserves that failure. The no-common-involution example and exact lower certificates extend the method's tested scope, but one skew pair is not the full skew operator norm. A symmetric lower bound relative to that pair cannot establish matrix-wide domination.

This is the clearest inspected path to a genuinely new mathematical theorem, precisely because the original unresolved statement is concrete. **Next:** either produce a rational six-dimensional matrix with a strict independently checked symmetric-upper/skew-lower separation, or prove universal domination with complete coverage of degeneracies and the no-common-grading class. For universal proof, a finite successful bank is insufficient. For a counterexample, a certified strict separation is enough; optimizer success or top-skew identification is not required if the explicit skew witness already exceeds the certified symmetric upper bound.

An exact resolution would warrant specialist scrutiny and a serious publication attempt. It would not automatically imply a particular award, broad industrial value or a prize payment. A useful intermediate paper would need a new structural theorem or demonstrably stronger certifying method, rather than a larger failed search.

## 7. Timing bounds and runtime composition

`lean/Research/TimingContracts.lean` explicitly describes its result as conditional elementary error algebra: position error, velocity error, clock error and an assumed trajectory remainder combine by the triangle inequality. That is N0 mathematics. Our harder prospective contribution is preserving a proved contract through delayed observations, replacement commitments, coherent receipt publication and command use.

This field already has substantial prior art. ModelPlex combines offline verification with runtime model validation and provably safe fallback under explicit deviation assumptions; its original paper appeared in 2014, with a journal version in 2016. “Connect a model proof to runtime monitoring” is therefore not itself our invention. [Mitsch–Platzer primary paper](https://www.cs.cmu.edu/~smitsch/pdf/modelplex.pdf), [journal version](https://link.springer.com/article/10.1007/S10703-016-0241-Z)

**Next:** choose one protocol that existing consumers actually need—such as asynchronous reference replacement plus a stale-state stopping reserve—and state exactly what prior frameworks cannot express or discharge without extra assumptions. Prove its complete trace-level property, include deadline misses and repeated receipt use, and implement it in an existing simulator/controller interface. Only then can we assess a new composition result rather than new names for known inequalities.

## A realistic path to work that could deserve recognition

The aggregate opportunity is stronger as **careful formal engineering with a usable consumer boundary** than as a claim that we have invented a new control canon. This is a qualitative judgment about the inspected slice; counting theorem declarations, GO decisions or public API functions would not produce a defensible percentage of original mathematics.

There are three different paths worth pursuing:

1. **Systems/formal-methods path — strongest practical near-term fit.** Take S12 plus timing/context semantics through one actual target and an existing workflow. The central result should be a precise compositional theorem or verified tool capability missing from the closest prior system. Deliver a complete reproducible artifact, independent adversarial review, a convincing comparison and a real downstream user. A familiar-library adapter that closes an important correctness gap can matter more than a new framework with many examples.
2. **Robotics/controls path — strongest applied experimental fit.** Select either energy or contact allocation, establish the narrow prior-art delta, and run matched strong-baseline experiments. Advance beyond a convenient polynomial or symmetric stance: show robustness, feasibility and useful performance under realistic constraints. Simulation can establish an initial result; claims about actual robot performance require an appropriately designed physical validation effort. A large reduction from a weak baseline is not a substitute for a new method.
3. **Mathematics path — highest explicit open-question upside, largest unresolved gap.** Resolve MF13 dimension six or establish a structural theorem that materially reduces it. Preserve exact statements, certificate soundness and independent replay. The work must survive external mathematical review; large compute expenditure or many negative cases does not supply that missing step.

For each path, first create a one-page claim ledger: exact theorem/capability; closest prior result; assumption/conclusion difference; practical significance; evidence already obtained; and the single result that would falsify the claimed advance. Have an independent domain expert examine that comparison before writing a breakthrough narrative. No contact is proposed or sent by this assessment.

Award-worthy work generally requires a combination of originality, significance and independent validation; none can be replaced by proof volume. Formalizing a known theorem can itself become important through exceptional scope, reusable infrastructure or demonstrated impact, but its contribution should be named honestly. We have credible material for focused research and useful integrations. We do not yet have evidence to predict an award or advertise a breakthrough.

## Limits and assessment quality

Fresh sources were inspected on the assessment date. Original Kalman/Sontag papers, the rectangular-contact paper, the OMv paper and clustered-Mv paper, MF13 status, ModelPlex, and current formal-library documentation support the distinctions above. Ata's publisher abstract supports broad septic/energy overlap only. The Flash–Hogan full PDF was blocked in this session, so no equation-level priority conclusion relies on it. The convex-optimization book landing page/materials were available while one full-PDF fetch timed out. No exact-priority conclusion was inferred from search silence.

Quality grade: **17/20** for this assessment—source relevance 4, local claim specificity 4, separation of evidence/novelty 4, actionable discrimination 4, exhaustive priority validation 1 (each out of 4). The low final component is deliberate: full closest-paper comparisons, cross-prover priority searches and external expert review remain open. Confidence in the broad classical-versus-new distinction is high; confidence that any particular candidate is globally first is unestablished, not a numerical probability.
