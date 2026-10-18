INTERNAL SCOPE REVIEW — 18 October 2026

Start with ../research/controls-scope-review-20261018/ASSESSMENT.txt.
Fourteen internal comments separate proof correctness from novelty and useful
engineering decisions. Recommended direction: one complete digital braking-to-
holding operation under changing response, followed by a matched comparison.
An exact-arithmetic age-budget screen has a nonempty 1 ms candidate; it is not
a sampled safety proof. The old papers and frozen team packet remain unchanged.
This is root self-review, not new independent or human peer review.

TEAM REVIEW PACKET — 18 October 2026

Start with controls-team-review-20261018/output/pdf/controls-review-brief.pdf.
This five-page brief separates the sampled-controller travel envelope from the
later changing-response settling theorem. It includes diagrams, exact assumption
boundaries, primary-source novelty comparisons, a team agenda and Lean entry points.
NOVELTY-EVAL.txt gives a targeted assessment and three falsifiable next gates.
READ-ME.txt links the unchanged six-page paper and frozen replay sources.
Current packaging checks verified612 input files and all105 archived project
files; no new Lean theorem or whole-project proof replay was performed.
Ready for team technical/novelty review; human novelty and publication decisions
remain open. No team message or external submission was sent.

The overnight motion paper and final63-module proof package are separately listed
in research/overnight/2026-10-18/MORNING-REPORT.txt, relative to the workspace root.
The older dated checkpoints below retain their original scope and history.

NEW WORKING NOTE — 17 October 2026

robot-motion/execution-note/main.pdf: Treating the Tremors We Built into Robots
Fourteen-page illustrated draft. The finite scalar history checker and physical
tracking connection have passed independent computational review. The first
comparison passed numerical review but has a favorable periodic input. The
harder comparison has accepted polynomial results and two native-clock failures.
A separate native-state repair passed finite fidelity checks and independent
physical replay at unchanged tolerances; all task decisions remain unchanged.
The rounded native handoff proof now covers the 12 frozen repaired paths.
A new isolated-task proof gives conditional progress and position arrival.
The new reversal comparison exposes an acceleration-limit failure accepted by
the jerk-only guard. Both proof and numerical gates passed independent review.
A 16-run Franka FR3 simulation rehearsal exposes the remaining coupled-arm gap.
Its code and scores received a separate read-only review, not a dynamics replay.
The draft keeps the known methods, delay costs, and negative cases visible.
No full-arm/VLA result or publication-readiness claim. Editable main.tex and
figures are in the same project folder. New review records are in review-08/.

NEW FINISHED FOLLOW-UP — 17 October 2026

tracking-note/main.pdf: When Plans Change, How Far Can a Robot Stray?
Five-page illustrated note. It closes the actual tracking error ODE, time scaling,
physical margins and finite matched replans. Its 34 new statements passed fresh
source checks, axiom audit and kernel replay. The 144-case numerical comparison
retains both better and worse jerk-feedforward outcomes. Continuous feedback,
model identification, stop reserve and publication novelty remain explicit limits.
See ../research/adjacent-controls/tracking-replans/README.txt and verification.json.
The Manim explanation and its source are in that folder's animation/ directory.
The existing fixed-rate sampled-control paper below has a different scope.

CURRENT PAPER AND ARTIFACT — 17 October 2026

Start with robust-manuscript/main.pdf (six pages). It unifies the fixed-controller
lag-uncertainty result, exact certificates, all-time travel bound, arbitrary ODE
execution contract, existence/uniqueness, physical units, and two exact ablations.
Editable source: robust-manuscript/main.tex.
Review: robust-manuscript/review.txt. Compilation and visual-review evidence:
robust-manuscript/verification.json.

WHAT IS CHECKED
For one fixed nominal controller, fixed actual rate r in [0.9,1.1], uniformly
positive dwell times no larger than 0.2, held pre/post-clamp errors whose combined
magnitude is at most 0.01, and initial quadratic energy at most 12, every continuous
trajectory satisfying its own sampled-feedback ODE has |x(t)| <=2 for all t>=0.
The physical bound is |X(T)| <=2 U tau0^2 with actual tau/tau0 in [10/11,10/9].
The initial ellipsoid constrains position, velocity and acceleration jointly.
The rate is fixed and both errors are held during each sample interval.

VERIFICATION
robust-project-verification.json records all five completed steps: aggregate
build/axiom audit, producer tests, nominal model-binding tests, ten benchmark
regenerations and twelve uncertainty certificate regenerations with two negative
model checks. All steps passed; audited public declarations: 830.

robust-final-fresh-replay.txt/.json/.log record a separate fresh source-copy
build: 105 source/configuration files, 63 project modules, 830 audited public theorem
declarations; 160.45 seconds. Source hashes stayed unchanged. The replay reused
the pinned Lean executable and isolated mathlib cache. It did not bootstrap Lean
or rerun the producer tests, which are covered by the whole-project manifest.
robust-final-fresh-replay.sources.tar.gz contains the exact checked snapshot.

Rebuild with the README in that source archive, or ../lean-controls/README.txt.
Pinned Lean 4.35.0 and mathlib revision are in lean-toolchain/lake-manifest.json.
Install SymPy 1.14.0 from requirements.txt, then run:
  python3 scripts/verify_project.py
Use a Python environment with the pinned requirements. For the paper, compile
robust-manuscript/main.tex with Tectonic or a normal TeX installation.

PUBLICATION BOUNDARY
This is a formal application case study using established mathematics. The
coherent result is a candidate for specialist assessment, not a claim of novel
control theory, hardware validity or publication acceptance. AI-agent review is
not human peer review. Author identity/affiliation/contributions, a release
license, specialist related-work review and venue fit remain to be settled.
Nothing has been submitted or publicly released.

HISTORICAL CHECKPOINTS (preserved)
  manuscript/main.pdf: seven-page nominal-model paper, 43 modules/516 declarations.
  uncertainty-addendum/main.pdf: three-page extension, 60 modules/806 declarations.
  application-fresh-replay.* and uncertainty-fresh-replay.*: their frozen evidence.
  application-comparison/: prior four-vertex shared-witness Lean SOS replay.
These are earlier scopes; the current paper and replay listed above supersede
those counts. No existing historical archive was overwritten.

PARALLEL RESEARCH
  ../research/opportunity-assessment/current-status.html
  ../research/opportunity-assessment/erdos-completion-spike/README.txt
  ../research/opportunity-assessment/big-opportunities-next/assessment.txt
  ../research/problem-trials/README.txt
The Erdős and competition tracks have separate evidence and unresolved claims.
