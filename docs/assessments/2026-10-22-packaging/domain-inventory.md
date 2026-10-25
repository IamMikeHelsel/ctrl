# Existing capabilities and adoption bundles

Inventory date: 2026-10-22. Author: domain worker, AI-assisted; inherited model identifier unavailable. Scope: current working tree, including existing dirty files, not a released or committed distribution. No core, site, Rust, approved statement or original research source was changed. Campaign S12-B01 remains paused; this inventory does not close its PM gate.

## Readiness counts and familiar integration points

“More than 11” is supported if we mean existing callable capabilities: **42 domain numerical/helper functions**, across five functional modules (10 trajectory, 10 estimation/control, 9 kinematics, 7 contact, 6 vision), plus **4 simulation entry points and 2 codegen functions**, totaling **48 registered callables**. Separately there are **12 C symbols and 4 ST units**; these overlap Python capabilities and must not be added as independent inventions. The scanner sees **82 Lean modules**, a third counting unit. These are usable building blocks, not 48 certified complete systems.

The campaign's completed reviews and GO routes are research decisions, not release counts. A count of **release-ready packaged bundles is not established**: none was audited here against clean installation, stable input/error contracts, supported platform matrix, fresh proof/implementation binding and target acceptance. That is an unknown acceptance count, not a claim that zero functions work. The five proposed bundles below organize many more than eleven existing capabilities.

| Workflow already anchored in repo | Exact anchor | Practical consumer adapter opportunity |
|---|---|---|
| NumPy/SciPy analysis notebooks | `numpy>=2.4.6`, `scipy>=1.17.1`; array-valued estimation routines | Document shapes, units and dtype; return validated result objects beside numerical residuals. |
| Control design/optimization | `control>=0.10.2`, `cvxpy>=1.9.3`, `osqp>=1.1.3`, `clarabel>=0.11.1` | Accept externally designed gains/certificates and independently check hypotheses; do not require replacing the user's optimizer. |
| Physics experiment loop | `mujoco>=3.16.0`; four explicit rollout functions | Run matched-task A/B controller adapters in an existing simulator project; log common effort, timing and success criteria. |
| Embedded C/C++ consumer | emitted C99 header, clang/ctypes finite parity harness | Add status/error contract and compiled library packaging around the twelve kernels; bind to caller scheduling/actuation. |
| PLC scan logic | four emitted ST units plus S12 static integer guard | Integrate a non-actuating acceptance FB first, then bind command application and snapshot consumption under a named vendor/compiler. |
| Exact offline engineering review | `Fraction`, source certificates, `ctrl check` and JSON CLI envelopes | Add reproducible CI receipts to existing review/build pipelines; permit independent optimizer/solver choice. |

The dependency versions above are current `pyproject.toml` lower bounds, not proof of each installed version. No ROS2, OpenCV, Ruckig, TwinCAT or CODESYS package adapter was found in `src/ctrl`/project dependencies. Those are potential consumer boundaries, not current supported integrations. Existing research comparisons outside the package do not establish a shipped adapter.

## What actually exists

The installable Python distribution is `ctrl` 0.1.0 (`pyproject.toml`), with the `ctrl` command and package `src/ctrl`. `ctrl.robotics` exposes trajectory, contact/CBF, kinematics, vision and estimation routines. Its top-level import eagerly imports the MuJoCo benchmark module; even importing a trajectory submodule executes that package initializer. Dependencies currently include the full research stack (MuJoCo, CVXPY, OR-Tools, PARI, SciPy, plotting and document tools), rather than a small runtime extra. An embedded consumer cannot currently obtain a minimal dependency footprint simply by selecting one import.

Fresh bounded checks in this inventory:

- Seven non-MuJoCo tests in `tests/test_ctrl_robotics_lib.py` passed in 0.24 s; one combined simulation/codegen test deliberately deselected. C99 was separately compiled and exercised.
- `verify_lean_bindings()` passed for 48 registered Python functions and 223 declaration references. Its scan currently finds 82 modules, 29,595 lines and 2,540 declaration names. These are scanner counts, not unique proved theorem counts, proof coverage or a fresh kernel replay.
- `compile_and_verify_c99_kernels()` compiled with clang and reported maximum error `8.881784197001252e-16` on its finite test set. It uses a tolerance, so “bit-level parity” is inaccurate. No universal floating-point refinement follows.
- The exact trajectory example below executes with `Fraction` and gives a 17.26% model-energy reduction, below the user's 30% upgrade hurdle.
- No `Cargo.toml` or `.rs` was found by repository file scanning, including hidden files while excluding dependency/build folders. No existing Rust API or Python/Rust parity can be claimed.

Machine-readable function inventory, hashes, registry results and exact example are in `domain-inventory.json`. The registry lists declaration-name provenance; its implementation does not compile Lean, compare Python semantics with theorem statements, validate every premise, or inspect all transitive axioms. Its forbidden-token scan checks only `sorry`, `admit`, `native_decide`. A clean result is a useful provenance check, not an executable-correctness certificate.

| Surface | Concrete implementation | Present boundary |
|---|---|---|
| Motion/energy | `trajectories.py`: septic q/v/a/j, squared integrals, model energy, eta choice, timewarp derivatives | Scalar polynomial functions support Fraction/float; physical parameters and constraints remain caller obligations. |
| Contact/IK | `contact_cbf.py`, `kinematics_ik.py`: four-contact allocation, Lorentz membership, backup mixture, single-row minimum-change IK, frame derivatives, response-time helpers | Specified reduced models; not whole-body contact estimation, general IK or a deadline-enforcing scheduler. |
| Vision | `vision_se3.py`: homography Gram identities/sign filtering, two-ray triangulation, depth dynamics | Helpers, not an all-degeneracy homography/P3P/multiview solver. Sign filter takes precomputed scalar dot products. |
| Estimation/control | `estimation_lqr.py`: Joseph update, DARE/CARE identities, Kalata gains, Luenberger separation, MPC descent, H-infinity/ISS diagnostics | Several matrix routines use NumPy floating solves/eigenvalues and return numerical residuals; not every API is exact-Q. |
| Runtime generation | `codegen.py`: fixed source-string emission of header/C/ST | Twelve C symbols; four ST units (septic position, quad-wrench FB, Sontag, backstepping). Not generation of all 48 Python functions from Lean. |
| Verification tooling | `ctrl check`, frozen Challenges, audit scripts; `robotics-check` command | Challenge checking and robotics source metadata checking have different strength. The latter optionally runs finite C parity and MuJoCo. |
| New certificate prototypes | `experiments/research/{latency_braking,transport_certificate}.py`; S12 extension exact consumer and `CertifiedCorrection.st` | Useful research artifacts outside installable API; must be promoted with explicit contracts and packaging. |
| Presentation | `site/index.html`, research catalog/data, two interactive study pages, downloadable source/Lean/assets | Static local site exists. This inspection did not verify live deployment or production usage. Research catalog is not an implementation inventory. |

The C and ST functions are visibly small fixed formulas, but emitted files alone do not establish WCET, PLC dialect compatibility, overflow behavior, scheduling, actuator semantics, compiler correctness or safety certification. The S12 ST predicate is a separate integer-comparison prototype, with no installed PLC compiler/runtime acceptance established in that block.

## Five coherent adoption bundles

These are packaging recommendations, not five already shipped products. Prioritize 1 and 2 for bounded integration pilots; 3 and 4 require a plant/vision team; 5 is an engineering workflow enabler.

| Bundle and user task | Existing components and benefit | Integration boundary | 30% hurdle or enabling test |
|---|---|---|---|
| **1. Motion profile and energy evaluator**: tune repeated rest-to-rest moves | Septic profiles, exact model integrals, eta optimizer, timewarp helpers; available C q/v/a/j | Drop-in numerical helper after units, duration, limits and endpoint semantics are fixed. Replacing a native interpolator is deeper: queue ownership, blending, acceleration/jerk/current/voltage limits and drive tracking need validation. | Current exact example saves 17.26%, so no 30% upgrade claim. Existing README simulation reports 4.1% total and 22.47% dynamic reduction, also below 30%. Enablement alternative: exact explainable trade-off evaluation and constraint checks unavailable in baseline, measured as a new accepted workflow. |
| **2. Certificate acceptance and static action guard**: approve a correction without trusting an optimizer | Transport rational verifier; S12 joint-polyhedron supports/Farkas certificates, safe interval and integer guard; latency stopping contract | Offline exact Python checking can be dropped into a CI/review pipeline. Runtime PLC integration is deeper: checked payload, versions, scale, immutable snapshot, bounded integers and actuation binding. Static correction is not dynamic safety. | Enablement gate: reject mutated/empty/stale certificates while accepting independently reproduced valid ones; expose why no action exists. Compare human review time or certificate-check cost for a 30% efficiency claim only after a matched baseline. |
| **3. Contact and disturbance control experiment kit**: add an explicit backup constraint to a controller | Lorentz CBF/quad force allocator, ISS/H-infinity/Sontag/DARE diagnostic helpers, MuJoCo scenarios | Deep integration. Need contact geometry, mass/inertia, friction and actuator limits, model mismatch, estimator validity and execution timing. No complete robot controller is drop-in. | README's 39.42% peak-error reduction against tuned CTC is a candidate benchmark, not freshly reproduced here or a hardware result. Require matched saturation, effort, sensing, timing and perturbation sweep; no promotion on weak-PD baseline alone. |
| **4. Geometry and frame validation kit**: detect invalid vision/control mappings | Exact sign/Gram/triangulation helpers plus transport derivatives and campaign V07/V08/V09 certificates | Individual functions are easy to call. All-candidate calibrated pose, degeneracy handling, noisy data and live frame calibration require larger integration. | Enablement gate: independently distinguish all admitted candidates from degeneracies on frozen small configurations. Do not advertise complete general-purpose vision solvers from fixture proofs. Performance gate could target reduced false-valid poses at fixed recall, but needs a declared dataset. |
| **5. Proof-linked engineering CI**: make assumptions and implementation evidence reviewable | Frozen statement hashes, `ctrl check`, theorem registry, exact fixtures, C differential tests, evidence artifacts and static site | CI adoption is lower risk than physical deployment. Needs a release manifest tying source/theorem/build/compiler/test hashes to specific APIs and premise schemas. | Enablement: reproducible acceptance artifacts and mutation rejection. A 30% onboarding/review-time claim needs an independent engineer performing the same task with and without the kit. |

Avoid selling the repository as a single “production-verified robotics library.” Sell callable capabilities with a short contract, reproducible example and evidence receipt. Larger systems can compose them, but composition is the work.

## Python/Rust parity architecture

There is no Rust implementation to wrap today. Three choices:

1. **Python reference plus selected independent Rust kernels**: keep exact Fraction or certificate reference on the offline side; implement bounded runtime kernels in Rust. Lowest disruption to current code. Highest risk is semantic drift, handled with shared canonical fixtures, input/error contracts and independent differential/mutation checks. This is the recommended first pilot.
2. **Rust core with Python bindings**: reduces duplicate floating runtime implementations after the core is mature. It does not itself prove Rust refines Lean, and does not remove the need for an independent exact oracle. Adds native build/distribution costs; premature for all current research APIs.
3. **Shared small expression specification generating Python/C/Rust/ST**: appropriate later for scalar polynomial and guard kernels; not a realistic automatic treatment of NumPy solvers, ODE reasoning or all Lean theorems. A generator can replicate a bug across every language, so independent fixtures remain necessary.

Use one versioned contract/fixture format with dimensions, frame convention, units, domains, failure modes, rational encoding, rounding, evidence digest and snapshot applicability. Each target gets its own receipt: Python example/tests; Rust tests and supported-target build; C differential results; PLC compiler/simulator test. Do not mark all languages equivalent because source text emitted or because all consume a Boolean `ReceiptVerified` flag.

For S12, explicitly distinguish an absolute/idempotent correction command from an additive increment. Repeated scans must not repeatedly add the same correction against the old snapshot. Use one-shot consumption/version advancement or define the output as an absolute setpoint; the existing static mathematical theorem does not choose either execution policy.

## Executed existing API example

```python
from fractions import Fraction as F
from ctrl.robotics.trajectories import optimal_septic_eta, electromechanical_energy

# Explicit toy actuator model; all parameters and matched distance/time are 1.
eta = optimal_septic_eta(F(1), F(1), F(1), F(1), F(1))
e0 = electromechanical_energy(F(1), F(1), F(1), F(1), F(1), F(1), F(0))
e1 = electromechanical_energy(F(1), F(1), F(1), F(1), F(1), F(1), eta)
assert eta == -11
assert e0 == 20 and e1 == F(3227, 195)
assert (e0 - e1) / e0 == F(673, 3900)  # about 17.26%; below 30%
```

This evaluates the declared loss model; it does not validate a physical motor, admissible jerk, supply regeneration, thermal variation or drive tracking. The source docstring says clamp to `[-11,-9]` while implementation clamps `[-11,0]`; repair that documentation before productizing. Inputs also need an explicit validation/error contract (for example positive duration and nonzero torque constant).

## Packaging gaps worth fixing first

1. Add minimal dependency groups/lazy benchmark imports; separate numerical runtime from solver/proof/simulation development dependencies.
2. Publish a capability manifest with function signatures, supported exact/float modes, constraints, test scope and language coverage. Replace broad source metadata labels with explicit evidence tiers.
3. Reconcile README counts/paths and remove production/bit-parity claims unsupported by current receipts. Some README links use top-level `ControlsLean/` and `scripts/` while this repository's source organization is under `lean/`.
4. Move promoted research helpers into a stable package only after input validation, versioned schema and caller examples; keep campaign artifacts separately archived.
5. Build target-specific integration examples: pure Python analysis, C numerical kernel, Rust selected-kernel prototype and PLC static acceptance function. Each must exercise a rejection path as well as a happy path.

No whole-repository test, fresh Lean build, MuJoCo rerun, Rust build, PLC compilation, hardware run or live-site deployment verification was performed in this inventory. The existing dirty work was preserved. Assessment quality: B+ (strong source/API and small-check evidence; deployment/physical and complete cross-language review remain open). Subjective confidence in inventory scope: 90%, not a calibrated correctness probability.
