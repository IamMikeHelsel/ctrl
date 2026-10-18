# Finite robot-motion reference certificate: reviewer bundle

This is a portable replay bundle for the accepted certificate03. It contains the exact local proof sources and a fresh-build runner. It adds no theorem, experiment, or novelty claim. The artifact is prepared for private review. Publication permission, licensing, and affiliation remain the author's decisions. This README grants no new license. External dependencies retain their own licenses.

## Replay

Requirements: Python 3.9 or newer; an already installed Lean/Lake **4.35.0** toolchain; and a provisioned dependency project with the exact files in `dependency-project/`. The runner targets macOS or Linux, including WSL. The recorded run is on macOS arm64; another platform has not been tested here. The Lean compiler commit must be `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The Lake manifest pins mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679` and pins its transitive dependencies.

Run from this bundle, with absolute paths to your existing environment:

```sh
python3 replay.py --dependency-project /absolute/path/to/provisioned-project --lake /absolute/path/to/lake --output /absolute/path/to/new-replay-output
```

If elan uses a nondefault home, add `--elan-home /absolute/path/to/elan-home`. The output directory must not exist. The runner needs no network access and performs no package installation or version update. A successful run ends with `PASS` and writes `results.json`. Read that file and the logs; a copied historical result is not a new replay.

For a separate dependency setup, copy the three files from `dependency-project/` into a new empty directory. With the stated Lean toolchain already installed and selected, the standard mathlib command is `lake exe cache get` from that directory. Lake uses the supplied manifest to obtain the public package dependencies. Do not run `lake update`, change the version pins, or add a local proof-library cache. This setup may need network access. It was not performed as part of this packaging task; the recorded verification uses the existing pinned cache. The original `lakefile.toml` declares a `LeanControls` library. It is retained byte for byte for dependency setup; the replay runner compiles the bundled sources itself and does not invoke that library's default build target.

The exact local verification command, run from the research workspace, is:

```sh
python3 publication/robot-motion/reviewer-bundle/replay.py --dependency-project lean-controls --lake .tools/elan/bin/lake --elan-home .tools/elan --output publication/robot-motion/reviewer-bundle/verification/local
```

## Contents and integrity

| Item | Purpose |
|---|---|
| `src/` | All 44 local modules in the complete import closure, unchanged. |
| `source-bindings.json` | Original source paths, hashes, module list, and public declaration inventory. |
| `theorem-map.json`, `contract.txt` | Accepted claims, theorem names, and explicit conditions, unchanged. |
| `inputs/`, `fixture-binding.json` | Exact frozen fixture data and their original hash bindings. |
| `negative-controls/` | Four original false claims that must be rejected. |
| `audit/` | Original named-declaration and complete local-environment axiom audits. |
| `provenance/` | Original builder manifest, verification record, accepted independent review, and independent binding script. Historical paths are preserved. |
| `dependency-project/` | Original toolchain, package declaration, and lock manifest. |
| `input-manifest.json` | Hashes of immutable replay inputs, including the runner. |
| `verification/local/` | The packaging replay result and logs. Its temporary `.build/` directory is excluded from the archive and removed after verification. |
| `artifact-sha256.json` | Final bundle file manifest. It excludes itself and the zip file. |

The original builder manifest has SHA256 `740ebc266891b3f98b9ee567d19cced3c3ff187cbc091c08edfa52b276cd90fa`. The runner binds the original verification record to that manifest, then binds every module to the verification record. The eight package files, theorem map, contract, fixture binding, and negative controls are also checked directly against the builder manifest. The input hashes are checked before and after replay. The final manifest and archive hashes must be supplied out of band if tamper resistance is required; a mutable manifest alone does not authenticate an artifact.

No local compiled proof files are included. The runner copies all 44 sources into a new build directory and compiles them in import order. It overwrites `LEAN_PATH` with that new directory and public dependency package caches only. It excludes the supplied project's `.lake/build` directory. Missing unused package search directories are recorded and omitted; any missing imported dependency causes compilation to fail.

## What is proved

For a finite list of signed target increments, the reference is

`q(t) = g0 + sum(delta * F((t - tau) / h))`, with `h > 0`,

where `F(s) = (1/24) * sum_{i=0}^4 ((-1)^i * choose(4,i) * max(s-i,0)^4)`.

The proofs derive the actual positive-part formula's derivatives and continuity, including at the knots. The reference is three times continuously differentiable. For a nonnegative jerk limit, its future jerk bound holds if and only if the signed jerk sum passes at the current admission time and every future event knot. The result covers empty, repeated, unsorted, old, and future events. It does not replace signed sums with separate magnitude bounds.

The executable Lean rational guard has a proved equivalence to that real-valued future bound. The admission model retains accepted future commitments and appends new events under explicit causal order conditions. Finite induction proves the reference jerk bound, executed-prefix preservation, target telescoping, and final reference rest after the last execution time plus `4h`. These are finite-history results. There is no bounded-storage or pruning theorem.

`RobotMotion.checked_tracking` and `RobotMotion.admitted_tracking` connect the actual reference and its derivatives to the existing `LeanControls.ScaledTracking.tracking_cube_scaled` theorem. This discharges the reference derivative and jerk assumptions. It retains the plant trajectory, uncertain lag-rate bounds, disturbance bound, initial transformed-state bound, positive scale, and numerical budget as hypotheses. See the exact statements in `src/Composition.lean`, the inherited theorem in `src/ScaledTracking.lean`, and `theorem-map.json`.

The tracking error is relative to this generated reference. It is not error relative to an unknown true task goal. Final reference rest is not a physical stop guarantee. This bundle contains no hardware experiment, sampled implementation proof, full-arm proof, collision safety result, or task-progress guarantee.

## Proof and runtime boundary

The Lean kernel and the pinned Lean/mathlib environment are trusted. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are allowed. The runner rejects local axioms, unsafe local declarations, admitted proofs, and unapproved axiom dependencies. It checks all imported local declarations, including private and generated constants, rather than relying only on a text search.

External package caches are reused. Their search paths, compiler hashes, and pinned manifest are recorded. The runner checks the supplied manifest, not a cryptographic source-to-object derivation for each external cache file. A reviewer who requires that stronger boundary should rebuild the external dependencies from the recorded public revisions before replay.

The executable `Rat` guard is the proved decision procedure. Python independently reconstructs the seven fixture histories and all 52 evaluated admissions with exact fractions. Python, JSON parsing, file I/O, and this replay wrapper are not formally verified. Their checks provide input-binding evidence; the Lean proof provides the guard theorem.

The packet boundary receives one winner from an upstream ready-packet batch. Selection of that winner and rejection of conflicting duplicate sequences are preconditions. The package does not prove the complete packet producer, network clocks, real scheduler, floating-point controller implementation, or physical plant assumptions. Rejected, stale, and no-change retention claims apply to the formal boundary under its stated hypotheses. No benchmark or native-clock result is imported into this certificate.

## Acceptance checks and counts

The replay must compile all 44 local modules, inspect all 2,996 local environment constants, audit all 992 public named declarations, and pass nine separate `leanchecker` replays: `ScaledTracking` plus the eight package modules. It must reject all four original negative controls for their intended false claims, rather than a missing import or unknown name. It must execute seven final-history checks and 52 admission checks, and independently bind them to the frozen exact inputs.

| Lean negative control | Deliberate error |
|---|---|
| `OmitCurrent.lean` | Remove the current admission time from the check. |
| `OmitInterior.lean` | Check only start and tail knots, missing interior extrema. |
| `EraseFuture.lean` | Discard accepted future events after checking their signed sum. |
| `FalseUnitJerk.lean` | Replace the unit-step jerk peak of 2 with the false bound 1. |

There are **660 public theorem statements** in this closure: **106 in the eight package modules, including one copied helper, and 554 inherited statements**. The remaining 332 public named declarations are definitions, structures, and related declarations. These are inventory counts, not counts of independent research contributions. The seven final histories also have kernel-proved concrete guard facts in `Fixtures.lean`; the 52 admission outputs are evaluated checks, not 52 new general theorems.

The separate `audit/wrapper-mutation-tests.py` checks four packaging failures: changed source bytes, changed inherited source bytes with a refreshed local hash, changed fixture data with a refreshed local hash, and a changed dependency pin. The stored results are under `verification/wrapper-mutations/`. These are wrapper checks, not additional Lean negative controls or proof statements.

This bundle supports review of a finite scalar formalization and its proof-to-tracking connection. It does not establish that the FIR construction is new or that the method is superior to other trajectory generators.
