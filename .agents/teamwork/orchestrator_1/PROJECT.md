# Project: Interdisciplinary Research Program (Math, Controls, Vision)

## Architecture
- **Language & Frameworks**: Lean 4 (mathlib / ControlsLean), Python 3.12 (uv, cvxpy, clarabel, pytest), Shell.
- **Repository Layout**:
  - `lean/Research/ControlCertificates.lean`: Foundational control certificates (braking, robust braking, interconnection budget).
  - `lean/Research/LorentzConeCBF.lean`: Centroidal Lorentz friction-cone CBF scaffolding.
  - `lean/Research/HomographyDecomposition.lean`: Machine-checked planar homography decomposition and chirality filtering (Formalization Scaffolding).
  - `tools/`: Verification tools and exact rational certificate generators (`verify_lorentz_cbf.py`, `sdp_rational_cert.py`).
  - `docs/`: Findings reports, evidence tier declarations, targets, and architecture.
  - `data/erdos/` & `work/`: Erdős problem specifications, triage gates, and proof artifacts.

## Feature Inventory
| # | Feature / Attack | Description | Milestone | Source |
|---|------------------|-------------|-----------|--------|
| 1 | Branch & Environment Integrity | Fresh branch `crossover-research-2026-10-19`, integrity mode `development`, test baseline | M1 | ORIGINAL_REQUEST §Integrity |
| 2 | Controls: Centroidal Lorentz-Cone Backup CBF Scaffolding | Closed-form backup CBF on 12-state centroidal SE(3) under Lorentz friction cones via conic duality & convex interpolation (Seed 1) | M2 | ORIGINAL_REQUEST §Candidate Seeds #1; Survey Controls |
| 3 | Vision: Homography Decomposition & Chirality Scaffolding | Machine-checked analytical Faugeras homography decomposition and two-view chirality filtering in Lean 4 (classified: Formalization Scaffolding) | M3 | ORIGINAL_REQUEST §R1-R3; Survey Vision Transfer #4 |
| 4 | Math: Rational SDP Certificates for Extremal Bounds | Exact rational Cholesky/LDL semidefinite certificates bridging solver output to Lean kernel checking | M4 | ORIGINAL_REQUEST §R1-R3; Survey Math & Vision Transfer #3 |
| 5 | R2 Cross-Discipline Push & Scaffolding Reclassification | Formalization of known results (Push B: CentroidalDecelerationLimit.lean) and scaffolding (Push C: VisualServoingInvariant.lean); relabel Push A toy Lyapunov matrix | M5 | Parent Directive 2026-10-19T06:52:25Z |
| 6 | Real Open Lane Attacks | (1) `work/pod/mf13` Byers–Nash $n=6$: 11-parameter convex family analysis, rank ≤ 4 skew normal-form lemma in Lean, rational SOS/SDP certificate; (2) `work/273` covering system audit & Lean formalization; (3) `work/pod/885` rational extension/obstruction | M5.1 | Parent Directive 2026-10-19T06:52:25Z |
| 7 | Independent Review & Findings Report | Comprehensive audit, independent check reproduction, mandatory hypothesis audit, and findings report in docs/ | M6 | ORIGINAL_REQUEST §R4 & Acceptance Criteria |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Env & Branch Setup | Create branch `crossover-research-2026-10-19`, verify baseline test suite & Lean tools | none | DONE |
| M2 | Controls: Lorentz CBF Scaffolding | Implement closed-form Lorentz friction-cone CBF, exact symbolic/interval check, Lean 4 theorem | M1 | DONE (Candidate / Scaffolding) |
| M3 | Vision: Homography Decomposition | Implement analytical homography decomposition with chirality filtering in Lean 4 (0 sorry, clean axioms) | M1 | DONE (Formalization Scaffolding) |
| M4 | Math: Rational SDP Certificate | Exact rational Cholesky certificate generator and verification of discrete energy bounds | M1 | DONE (Tier 2 Exact ℚ) |
| M5 | R2 Push & Scaffolding Reclassification | Push B: CentroidalDecelerationLimit.lean (Known Result); Push C: VisualServoingInvariant.lean (Scaffolding); Push A: Toy Lyapunov relabeled | M2, M3, M4 | DONE |
| M5.1 | Real Open Lane Attacks | (1) `work/pod/mf13` (Byers–Nash $n=6$): 11-parameter family, Lean normal-form lemma for rank ≤ 4 skew 6×6, rational SOS/SDP certificate; (2) `work/273` covering system audit & Lean formalization; (3) `work/pod/885` grid extension/obstruction | M4, M5 | DONE |
| M6 | Audit, Report & Program Synthesis | Forensic integrity audit, independent reviewer reproduction, mandatory hypothesis audit, findings report in docs/ | M5.1 | DONE |

## Mandatory Hypothesis Audit (Parent Directive 2026-10-19T06:17:41Z)
For each headline theorem in M5 and all subsequent reviews:
1. Reviewers must list every hypothesis and structure field.
2. Reviewers must mark whether any hypothesis encodes the crux of the claimed result.
3. Any theorem whose crux is a hypothesis is capped at "scaffolding", regardless of zero-sorry status.
4. Trivia (e.g. arithmetic identities like `2+6=8`) must not appear as headline findings.
5. A smaller theorem with NO smuggled crux strictly beats a large file of bookkeeping.

## Interface Contracts
### Controls ↔ Lean Kernel
- Function signatures: `lorentz_backup_cbf`, `braking_safe_lorentz`, exact rational scalar interpolation parameter $\lambda^*(x)$.
- Verification: Exact symbolic checking in Python + Lean 4 theorem with 0 `sorry` and standard axioms `[propext, Classical.choice, Quot.sound]`. (Evidence tier: Candidate / Scaffolding).

### Vision ↔ Mathlib / ControlsLean
- Module: `lean/Research/HomographyDecomposition.lean`.
- Signature: Analytical Faugeras decomposition of homography $H = R + \frac{1}{d} t n^\top$ into motion candidates, with chirality filtering $n \cdot X > 0$ reducing 8 mathematical solutions to 2 physical solutions.
- Evidence tier: Formalization Scaffolding (parent directive: assumes solutions as structure fields; sign bookkeeping).

### Math ↔ Exact Arithmetic / Solvers
- Format: JSON certificate with rational matrix entries `{"L": ..., "D": ..., "bound": ...}`.
- Verification: Identity $S_{\mathbb{Q}} = L D L^\top$ checked over $\mathbb{Q}$ via exact arithmetic / Lean `norm_num`. (Evidence tier: Tier 2 Exact computation over ℚ).

## Code Layout
- `lean/Research/ControlCertificates.lean`: Controls certificates extensions.
- `lean/Research/LorentzConeCBF.lean`: Centroidal Lorentz-cone CBF Lean formalization.
- `lean/Research/HomographyDecomposition.lean`: Vision formalization.
- `tools/verify_lorentz_cbf.py`: Exact symbolic & interval arithmetic verifier for Lorentz CBF.
- `tools/sdp_rational_cert.py`: Rational semidefinite certificate generator.
- `tests/test_lorentz_cbf.py`: Verification tests for control certificate.
- `tests/test_homography_decomposition.py`: Tests for homography decomposition.
- `tests/test_sdp_rational_cert.py`: Tests for rational SDP certificate extractor.
- `docs/crossover-program-report-2026-10-19.md`: Final findings report.
