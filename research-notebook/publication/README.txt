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
