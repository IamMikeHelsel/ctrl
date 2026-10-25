# ctrl research program — 21 October 2026

## Purpose

Find small mathematical results that make robotics software easier to reason about,
then test whether those results improve a specified engineering decision. Keep the
statement, implementation, experimental result and physical interpretation separate.
Useful negative results belong in the notebook too.

The initial literature window is **21 August–21 October 2026**, inclusive. This is a
targeted primary-source survey, not a systematic review or a claim of literature
coverage. Preprints remain preprints. Publication/version dates, passages inspected,
assumptions and proposed transfers are recorded per paper in the companion JSON.

## What this pass produces

- Two independently researched source lanes: control/safety and perception/data.
- A matrix connecting mathematical tools, physical models and engineering questions.
- A delayed-braking prototype with exact arithmetic, adversarial checks, a separately
  compiled Lean polynomial-envelope proof, an interactive explanation and Manim video.
- A finite-transport certificate prototype, independent enumeration checks and a
  separately compiled Lean weak-duality proof.
- A quieter site that identifies what was checked and what remains assumed.

These are research artifacts. They do not change the GitHub repository's visibility,
approve any Challenge statement, or certify an industrial system. New local pages
need an explicit release decision after the evidence and site preview are reviewed.

The completed first pass is recorded in [VERIFICATION.md](VERIFICATION.md), with the
[source matrix](MATRIX.md), [transport study](transport-study.md),
[braking review](latency-braking-review.md), [next experiment](latency-next-experiment.md),
and [site claim audit](site-claim-audit.md). No new mathematical discovery is asserted.

## Budget and team

Interpret “maybe 30% of my weekly quota” as **up to 30 additional percentage points**
of the whole weekly allowance, not a requirement to consume that amount. The initial
account-wide reading was 7% used; a nominal stopping level is therefore 37% used in
the same reset window. The meter is rounded, account-wide and may lag. Other chats
consume the same allowance; it is not a precise per-team cost meter or hard cap.

Check before each larger batch. Stop dispatching at 34% and reserve the last three
points for verification and handoff. If the reset timestamp changes, usage becomes
unavailable, or other activity makes attribution unclear, checkpoint rather than
starting a fresh allowance. Do not buy credits, redeem resets or silently switch
to separately billed inference. No ongoing schedule is installed by this plan.

| Work | Approximate share of weekly allowance | Gate |
| --- | ---: | --- |
| Source search and theorem/assumption extraction | 6 points | Traceable primary sources, useful coverage across requested domains |
| Crossover ranking and adversarial model review | 4 points | Explicit new question, failure mode, baseline and measurable endpoint |
| Two or three bounded prototypes/formal slices | 12 points | Reproducible witness or counterexample; no hidden hypothesis carrying the result |
| Independent reproduction and claim review | 5 points | Reviewer can recreate result and state every unproved bridge |
| Site, write-ups and explanatory animation | 3 points | Public text agrees with artifacts; preview checked |

These allocations are planning limits, not measured spending or promises of discovery.
Keep at most three workers plus the coordinator: one source/model owner, one
implementation owner, and one skeptical reviewer per active candidate. Reviewers
should not merely rerun the author's assertions. Use a different integration path,
adversarial input or certificate mutation where possible.

## Research funnel

1. **Source card.** Verify date and primary URL; extract the actual claim location,
   all material assumptions, version, inspected scope and evidence type. A title or
   abstract can seed a question but cannot establish theorem correctness.
2. **Transfer card.** Name the bridge: math → physical abstraction → measured system
   variable → proposed check. Mark which bridge is missing. Search prior art before
   claiming novelty; “a useful composition” is a valid result.
3. **Small falsifiable experiment.** Freeze a model, units, admissible inputs,
   baseline, metrics, grid/seeds and failure criterion before comparing outcomes.
4. **Faithful formal slice.** Prove an explicit statement. List every hypothesis and
   mark any that contains the crux. Separate exact witness checking from solver
   search; separate a real-number theorem from executable arithmetic refinement.
5. **Independent review.** Attempt to break calibration, stale-state handling,
   numerical tolerances, fallback feasibility and the theorem-to-code link.
6. **Promotion.** Publish only the supported claim. Broader or failed directions stay
   marked proposal, conditional lemma, bounded experiment, or inconclusive.

## Candidate priorities

| Order | Crossover | Useful question | Evaluation / rejection condition |
| --- | --- | --- | --- |
| 1 | Interval state bounds × real-time execution × braking dynamics | Does an admission rule account for all motion before braking acts? | False admissions and unnecessary rejection on a declared model; break it with understated latency or weaker braking. Do not count rejection as recovery. |
| 2 | Transport duality × mass conservation × fleet/data allocation | Can a proposed assignment carry a small replayable optimality-gap certificate? | Exact row/column balance, nonnegativity, dual feasibility and gap; reject altered cost, missing mass or invalid dual. No collision-avoidance inference. |
| 3 | Semidefinite duality × rigid-body pose × outlier geometry | Can numerical pose certificates become rational or interval certificates with a stated gap? | Accept/reject rate, gap, residual, rank/degeneracy, checker time and bytes; independent primal/dual validation. Stop if exact repair destroys useful bounds. |
| 4 | Conformal calibration × sensing geometry × reachable sets | Can state uncertainty tighten safely without mistaking marginal coverage for trajectory safety? | Coverage under declared dependence/shift assumptions, set volume, false admissions, p95 compute; reject the transfer if coverage cannot survive the operating regime. |
| 5 | Dissipativity × estimator/controller interaction × sensor physics | Does an estimator improvement survive inside a closed loop? | Matched actuator, latency and disturbance budgets; tracking, constraint violations and energy. Include initial storage and all gain constants. |

The first two are deliberately small. Larger multibody, perception and closed-loop
claims need substantially more model and implementation evidence. Priority is a
planning judgment, not a probability of a novel discovery.

## Scoring without false precision

Score **usefulness, formal tractability, testability, reuse, and assumption burden**
from 0–4. Prefer candidates with a concrete workload and a falsifier. A high score
cannot compensate for missing provenance, a theorem whose crux is assumed, or an
invalid benchmark. Report confidence in the *scope assessment*, separately from
confidence that a new research result will exist. Do not put unsupported percentage
improvement targets on the public site.

## Site and publication gate

Each featured study should include: question, model and units, source/version,
statement, proof/check command, executable artifact, baseline, measured result,
failure example, limitations, AI disclosure and a next experiment. Animations
explain the model; their visual persuasiveness adds no evidence.

Before making the repository public:

- Choose the exact Git commit/tree to release. This working tree contains substantial
  prior work; an uncommitted local check does not certify GitHub's default branch.
- Reconcile README, STATUS_AND_ROADMAP and both AGENT_IDEA_INDEX catalogs with the
  site audit. Existing “production ready” and runtime transfer claims need evidence.
- Review tracked/untracked internal logs, machine paths, configurations, generated
  papers and source licensing in that release tree. Do not publish `.agents/` by
  accident. Review history as well as the current file set before a visibility change.
- Run repository checks on that exact tree. `ctrl check --all` checks Challenge-bound
  solutions; it is not an audit of every robotics proof or a physical safety test.
- Build/audit the selected Research modules separately, verify citations and artifact
  hashes, and inspect desktop/mobile pages and animation frames.
- Publish the reviewed site assets to the existing GitHub Pages `site` branch without
  copying the whole workspace. Review repository visibility as a separate decision.

## Disclosure

This plan, source summaries, prototype code, tests, formal proof attempts, site copy
and animation were AI-assisted by OpenAI Codex and cooperating agents. Papers are
attributed to their authors. No independent human review, novelty determination,
hardware validation or source-paper reproduction is asserted by this document.
