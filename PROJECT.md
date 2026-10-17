# Project: ctrl — Formal Control Theory, Estimation & Machine Vision in Lean 4

## Architecture
- Target repository: `/Users/mike/lean-work/ctrl` (remote `https://github.com/IamMikeHelsel/ctrl.git`)
- Seed repository: `/Users/mike/lean-work/ControlsLean`
- Reference repository: `/Users/mike/Dev/LeanForControl`
- Lean 4 Toolchain: `leanprover/lean4:v4.36.0-rc1`
- Mathlib dependency: rev `625d8914199bc567cca9b91f90e8e5afafa5ae51`
- Build system: Lake (`lakefile.toml`, `lake-manifest.json`)
- Cache strategy: Symbolic link `.lake -> /Users/mike/lean-work/ControlsLean/.lake` (shares 7.2 GB cache with 0 disk overhead, enabling ~1.2s cached builds and ~2s per-file verification)
- Axiom policy: Standard Lean 4 axioms only (`propext`, `Classical.choice`, `Quot.sound`). Zero `sorry`, `admit`, or custom `axiom`.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | R1: Cache Symlink & Build Repair | Symlink `.lake` to `ControlsLean/.lake` to fix Mathlib git checkout error | M1 | Survey 1 |
| 2 | R1: Comprehensive `.gitignore` | Configure `.gitignore` matching `.lake` (no trailing slash for symlink), `.DS_Store`, `*.olean`, etc. | M1 | Survey 1 |
| 3 | R1: Verification of Seed Baseline in `ctrl` | Ensure `scripts/check.sh` and `scripts/Audit.lean` pass cleanly in `ctrl` | M1 | Survey 1 |
| 4 | R2: Formal Control Landscape Doc | Write `docs/landscape.md` synthesizing ControlsLean vs LeanForControl vs Mathlib | M2 | Survey 2 |
| 5 | R2: Library Architecture Doc | Write `docs/architecture.md` defining design principles, matrix representations, and proof idioms | M2 | Survey 2 |
| 6 | R2: Prioritized Roadmap Doc | Write `docs/roadmap.md` mapping short/medium/long-term efforts, Erdős bounties, and open problems | M2 | Survey 2 |
| 7 | R3-A: Planar Homography Formalization | Machine-check `ControlsLean/Vision/Homography.lean` (collineation duality, line incidence, collinearity, plane constraint) | M3 | Survey 3 |
| 8 | R3-A: Planar Homography Proposal | Research write-up in `docs/proposals/01_planar_homography.md` with citations (Hartley-Zisserman) and novelty analysis | M3 | Survey 3 |
| 9 | R3-B: Controllability Gramian Formalization | Machine-check `ControlsLean/Controls/Gramian.lean` (Gramian symmetry, energy quadratic form, minimum-energy steering) | M4 | Survey 3 |
| 10 | R3-B: Controllability Gramian Proposal | Research write-up in `docs/proposals/02_controllability_gramian.md` with citations (Kalman-Ho-Narendra) and novelty analysis | M4 | Survey 3 |
| 11 | R3-C: Information Filter Formalization | Machine-check `ControlsLean/Estimation/InformationFilter.lean` (Woodbury ring identity, Kalman-Information equivalence) | M5 | Survey 3 |
| 12 | R3-C: Information Filter Proposal | Research write-up in `docs/proposals/03_information_filter.md` with citations (Sherman-Morrison-Woodbury, Anderson-Moore) | M5 | Survey 3 |
| 13 | R3-D: Pole Placement & Deadbeat Formalization (Bonus) | Machine-check `ControlsLean/Controls/PolePlacement.lean` (nilpotent deadbeat control, 2-step extinction) & proposal | M6 | Survey 3 |
| 14 | Final Integration & Axiom Audit | Update `ControlsLean.lean`, `scripts/Audit.lean`, run `scripts/check.sh`, review and adversarial challenge | M7 | Request |
| 15 | Forensic Integrity Audit | Independent verification by `teamwork_preview_auditor` for non-duplication, genuine logic, and standard axioms | M7 | Request |
| 16 | Git Commit & Push to Remote | Commit consolidated repository and verified additions to `origin/main` (`https://github.com/IamMikeHelsel/ctrl`) | M8 | Follow-up |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | R1: Repository Organization & Git Hygiene | Symlink `.lake`, configure `.gitignore`, verify seed baseline | none | DONE |
| M2 | R2: Seed Synthesis & Landscape Documentation | `docs/landscape.md`, `docs/architecture.md`, `docs/roadmap.md` | M1 | DONE |
| M3 | R3: Novel Addition 1 — Planar Homography (Vision) | `ControlsLean/Vision/Homography.lean` & `docs/proposals/01_planar_homography.md` | M1 | DONE |
| M4 | R3: Novel Addition 2 — Controllability Gramian (Controls) | `ControlsLean/Controls/Gramian.lean` & `docs/proposals/02_controllability_gramian.md` | M1 | DONE |
| M5 | R3: Novel Addition 3 — Information Filter (Estimation) | `ControlsLean/Estimation/InformationFilter.lean` & `docs/proposals/03_information_filter.md` | M1 | DONE |
| M6 | R3: Novel Addition 4 — Deadbeat Pole Placement (Bonus) | `ControlsLean/Controls/PolePlacement.lean` & `docs/proposals/04_pole_placement_deadbeat.md` | M1 | DONE |
| M7 | Full Library Integration, Review & Forensic Audit | Import in `ControlsLean.lean`, update `scripts/Audit.lean`, pass `check.sh`, Reviewer + Challenger + Auditor gate | M2, M3, M4, M5, M6 | DONE |
| M8 | Git Finalization & Remote Push | Clean `git status`, commit, and push to `https://github.com/IamMikeHelsel/ctrl` | M7 | IN_PROGRESS |

## Code Layout
- Root: `/Users/mike/lean-work/ctrl`
- Source files:
  - `ControlsLean.lean` (Library root import file)
  - `ControlsLean/Vision/Epipolar.lean` (Seed: Essential matrix & epipolar constraint)
  - `ControlsLean/Vision/Homography.lean` (Novel 1: Planar homography & collineation)
  - `ControlsLean/Controls/Hurwitz2.lean` (Seed: Second-order Hurwitz polynomial stability)
  - `ControlsLean/Controls/Reachability.lean` (Seed: Coordinate-free reachability without Cayley-Hamilton)
  - `ControlsLean/Controls/DiscreteLyapunov.lean` (Seed: Asymptotic stability without symmetry)
  - `ControlsLean/Controls/Gramian.lean` (Novel 2: Controllability Gramian & minimum-energy steering)
  - `ControlsLean/Controls/PolePlacement.lean` (Novel 4: Second-order companion pole placement & deadbeat control)
  - `ControlsLean/Estimation/ScalarKalman.lean` (Seed: Scalar Kalman optimality & Riccati contraction)
  - `ControlsLean/Estimation/InformationFilter.lean` (Novel 3: Woodbury identity & Information matrix equivalence)
- Scripts:
  - `scripts/check.sh` (Build check + sorry/admit scanner + axiom auditor)
  - `scripts/Audit.lean` (Headline theorems axiom verification)
  - `scripts/sync.sh` (Google Drive backup)
  - `scripts/bounty_triage.sh` (Erdős/bounty triage utility)
- Documentation:
  - `README.md`
  - `LICENSE`
  - `AGENTS.md`
  - `BOUNTIES.md`
  - `docs/landscape.md`
  - `docs/architecture.md`
  - `docs/roadmap.md`
  - `docs/proposals/01_planar_homography.md`
  - `docs/proposals/02_controllability_gramian.md`
  - `docs/proposals/03_information_filter.md`
  - `docs/proposals/04_pole_placement_deadbeat.md`
