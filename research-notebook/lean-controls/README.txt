EXACT SAMPLED-DATA CERTIFICATES IN LEAN — research prototype
17 October 2026

What this contains

An untrusted exact-rational producer emits Lean proofs of quadratic energy
decrease for every sampling interval in a specified range. The proof interface
uses Bernstein matrix coefficients and LDL witnesses. Positive lower and upper
energy bounds prevent a signed-energy inequality from being misread as stability.
Held-input model bridges and arbitrary-jitter composition are checked separately.

The benchmarks are a double integrator, a jerk integrator, a genuinely coupled
planar double integrator, and a first-order actuator-lag plant. A wider nominal double-integrator variant reaches
h=33/50, with a smaller decay margin. For the lag plant, the exact exponential
transition is proved to lie between two polynomial vertices; their common energy
bound is certified through h=1/5. These are normalized mathematical models.

A separate exact-real rounded controller has a local robust sample-time bound.
The full local budget excludes active clipping; SaturationBoundary proves that
limitation. SaturatedEntry checks one 26-step recovery trace with actual clipping
and composes its endpoint with an infinite robust tail. It does not certify a
whole saturated basin of attraction or machine arithmetic.

TravelSafety now proves a region-wide all-real-time travel bound for the
saturated actuator-lag axis. For every z0 with z0^T P z0 <= 12, every positive-
minimum sampling sequence with h <= 1/5, and every held command-channel
disturbance |w| <= 1/100, its defined trajectory has |position(t)| <= 2 for
all real t >= 0. The region includes (0,0,1), whose request -2 clips to -1.
TravelExecution proves continuity across samples and the plant ODE inside
sampling intervals. Units are normalized; the initial ellipsoid restricts
position, velocity and acceleration jointly. This is not a physical axis test.

MeasuredTravel adds actual pre-clamp request errors, sharing the held error
budget with post-clamp disturbance. It proves continuity, the interior ODE,
and all-time travel safety for that execution. A separate ideal nearest-grid
sensor corollary permits dx/2 + 3*dv/2 + da + W <= 1/100.
PhysicalTravel checks the dimensional transformation, physical ODE, and bound
|X(T)| <= 2*U*tau^2 for known tau>0, U>0. Illustrative tau=.1s and U=2m/s^2
give a 4cm envelope and 20ms maximum sample interval. These are assumed values,
not measured hardware parameters. TravelScope checks a position-only initial
counterexample and the coarse-versus-refined disturbance-budget arithmetic.

CURRENT ROBUST EXECUTION RESULT

UncertainLag, UncertainResponse and UncertainTravel retain one fixed controller
while the actual normalized actuator rate r is unknown and fixed in [0.9,1.1].
For the same initial ellipsoid, h<=1/5, uniformly positive dwell and combined
held request/drive error<=1/100, position stays within +/-2 for all real t>=0.
Both errors are command-equivalent; the post-clamp error is INSIDE r*(u-a).
The normalized proof additionally permits the stronger budget 1/90.

ExecutionUniqueness defines a contract for ANY continuous trajectory satisfying
its own sampled-feedback ODE and initial state. It proves existence, equality
to the constructed execution, uniqueness for the same prescribed h,e,d, and
all-time travel safety. Derivatives are required only inside open hold intervals.
PhysicalExecutionUniqueness proves the corresponding arbitrary-trajectory
contract with fixed nominal controller tau0 and actual plant tau. Its bound is
|X(T)|<=2 U tau0^2 for tau/tau0 in [10/11,10/9]. No time-varying lag, arbitrary
within-hold disturbance, state-dependent quantizer uniqueness or machine
arithmetic is asserted. The earlier nominal ideal-rounding theorem is separate.

UncertaintyScope checks an obstruction to this P on a broader independent
sector and the coarse/direct response budget comparisons. These concern the
certificate and sufficient budget, not a proof that the actual clipped plant
is unsafe. The current coherent paper is ../publication/robust-manuscript/main.pdf.

The matrix-analysis modules are exploratory groundwork. They do not solve the
order-six symmetric-maximizer conjecture. A theorem declaration count includes
helper facts and certificate reconstruction; it is not a count of new research
results.

Versions and prerequisites

  Lean: leanprover/lean4:v4.35.0 (lean-toolchain)
  mathlib: exact revision pinned by lake-manifest.json
  Python: 3.10 or later
  SymPy: 1.14.0 (requirements.txt)

Install elan/Lake using https://lean-lang.org/install/ . From this directory:

  lake exe cache get
  python3 -m venv .venv
  .venv/bin/python -m pip install -r requirements.txt
  ./check.sh
  .venv/bin/python scripts/test_certificate_producer.py --lean
  .venv/bin/python scripts/verify_benchmarks.py

Or, after obtaining dependencies and installing SymPy, run the complete local
checking sequence and produce a source-bound manifest in one command:

  .venv/bin/python scripts/verify_project.py

For exact replay, keep lake-manifest.json unchanged and use its pinned
dependencies. The first
build/cache download can be large. The archive does not bundle those dependencies.

check.sh uses LAKE if supplied, then the current ELAN_HOME, a workspace-local
installation when present, or the standard elan installation/PATH. It never
requires the original author's absolute filesystem paths. The same resolution is
used by the Python verification tools.

Generation is not verification

  .venv/bin/python scripts/generate_interval_certificate.py \
    benchmarks/double-integrator.json --output /tmp/Example.lean --name Example

The producer explicitly reports UNVERIFIED. The JSON witness sidecar is also
unverified. A failed producer command may leave an earlier output file in place;
always check the command's exit status. scripts/verify_benchmarks.py regenerates,
checks the new source, audits its axioms, and binds success to hashes.

What checking establishes

  check.sh builds every imported source module, checks the named theorem audit,
  and rejects dependency axioms outside propext, Classical.choice, Quot.sound.
  In particular, sorryAx and compiler-trust axioms are not accepted.

  scripts/sync_audit.py maintains the module/theorem source inventory.
  `--check` rejects stale inventories. This is a small source inventory utility,
  not a Lean parser or a substitute for the kernel. Private helpers are audited
  transitively through the public theorems that use them.

  scripts/test_certificate_producer.py --lean runs input/factorization regression
  tests, accepts a valid scalar proof, and requires Lean to reject a corrupted
  residual coefficient and a changed model with its old certificate.

  scripts/verify_benchmarks.py freshly typechecks all ten generated sources and
  prints each theorem's transitive axioms. evidence/benchmarks/verification.json
  records input/source hashes, exact commands, toolchain/dependency versions,
  declaration names, timings, and axiom results. Its temporary checked source is
  precisely the generated module plus the recorded declarations' #print commands.

  scripts/test_model_bridge.py accepts the original actuator model, then changes
  its acceleration feedback coefficient and requires all four model-to-vertex
  proofs to fail against the unchanged certificate. This checks binding of the
  written model to the witness, not the safety of that changed controller.

  scripts/verify_uncertainty_artifact.py derives all twelve uncertain-rate
  polynomial certificate inputs from benchmarks/uncertain-lag.json, regenerates
  the Lean modules, compares them modulo terminal whitespace and checks them.
  It also requires rejection when the middle rate Bernstein coefficient is
  replaced by the midpoint plant, or the actual rate multiplier is removed from
  the ODE. Whole-project verification includes this fifth step. The JSON model
  description is metadata; the Lean model identities provide the semantic link.

The Lean kernel validates the formal statements relative to their definitions
and permitted axioms. It does not determine whether the physical plant matches
those definitions, establish originality, certify a numerical implementation,
or replace external mathematical review. Imported dependency artifacts and the
Lean installation are part of the reproducible software trust boundary.

Reading order

  LeanControls/Examples.lean              basic and intermediate examples
  LeanControls/SampledPD.lean             exact held double-integrator dynamics
  LeanControls/BernsteinCertificate.lean  reusable interval certificate interface
  LeanControls/Generated/                 generated exact certificates
  LeanControls/HeldModels.lean             jerk/planar ODE and segment bridges
  LeanControls/DoubleIntegratorBridge.lean two-state generated-model bridge
  LeanControls/VertexCertificate.lean      convex interpolation of energy bounds
  LeanControls/ActuatorLag.lean            exact exponential lag and proved enclosure
  LeanControls/SamplingClock.lean          sample clock and nominal state envelope
  LeanControls/SaturationSector.lean       exact scalar clipping sector
  LeanControls/SaturatedLag.lean           held clipped axis and four vertices
  LeanControls/StepScaledRobustness.lean    elapsed-time-scaled disturbance budget
  LeanControls/TravelDisturbance.lean      exact held response energy bound
  LeanControls/TravelGeometry.lean         position and request bounds
  LeanControls/TravelSafety.lean           universal all-real-time travel theorem
  LeanControls/TravelExecution.lean        continuity and assembled interior ODE
  LeanControls/MeasuredTravel.lean         request error and ideal sensor grids
  LeanControls/PhysicalTravel.lean         physical units and actual scaled ODE
  LeanControls/TravelScope.lean            interpretation limits and budget ablation
  LeanControls/UncertainLag.lean           fixed-rate exact model and 12 vertices
  LeanControls/UncertainResponse.lean      uniform direct response energy bound
  LeanControls/UncertainTravel.lean        held-error all-time invariant
  LeanControls/UncertainExecution.lean     global continuity and interior ODE
  LeanControls/ExecutionUniqueness.lean    every ODE solution equals construction
  LeanControls/PhysicalExecutionUniqueness.lean physical ODE contract and safety
  LeanControls/UncertaintyScope.lean       exact sector and budget ablations
  LeanControls/Certificate.lean            generic and concrete robustness
  LeanControls/SaturationBoundary.lean     proved limitation of the local budget
  LeanControls/SaturatedEntry.lean         clipped recovery and robust tail
  LeanControls/OrthogonalLyapunov.lean     known symmetric-matrix baseline
  LeanControls/CoupledLyapunov.lean        necessary coupled-pair identities
  LeanControls/RankFourCore.lean            conditional two-block comparison

Publication status

This is a checked local research prototype and working manuscript, not an
accepted or submitted paper. The coherent six-page paper focuses on uncertain
fixed lag, all-time safety for arbitrary continuous ODE executions, physical
scaling, exact ablations and reproducible model/certificate checks. The earlier
nominal paper and SOS replay remain historical evidence with narrower scope.
A standalone benchmark contract is in ../publication/robust-benchmark/model.json;
it is structured metadata, not an independently checked semantics parser.

The proposed publication route is a formal application or benchmark/tool case
study. New general control theory is not claimed. Specialist review must assess
usefulness, relevance and prior work; no measured physical axis or independent
matched comparison with another complete verification pipeline is available.
AI-agent reviews are not human refereeing. Full human author details,
affiliation, contribution review and a release license remain to be settled.

No publication license has yet been selected. Dependencies retain their own
licenses and are not included in the source archive. Do not infer institutional
endorsement or approved affiliation from this working package.
