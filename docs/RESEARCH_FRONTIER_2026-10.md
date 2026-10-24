# Research Frontier 2026-10

**Scouted**: 2026-10-22 by seven parallel research agents (one per lane), each reading the repo first and then the web.
**Machine-readable twin**: [`docs/SYNERGY_WEIGHTS.json`](SYNERGY_WEIGHTS.json), queried with `./ctrl synergy` (see `tools/README.md`).
**Scope**: problems adjacent to `ctrl` (control, estimation, robotics, vision, real-time, math, Lean tooling, certification) and to the sibling repo `sediment` (local-first Rust archive utility) that are worth exploring, productionizing, or industrializing, plus the cross-domain edges that let one lane unlock another.

## Ten findings that should change what we do next

1. **Most of the claimed Erdős list does not hold up, and the cheap money lane is closed.** A line-by-line audit (2026-10-24) of the 31 numbers the docs claim found: 3 worth rescuing now (`erdos_834.parts.ii` on `main` in `erdos/ErdosLab/`, plus the `erdos_1148` weaker variant and the `erdos_367` k ≤ 2 variant), 7 already formalized by others (261, 291, 370, 493, 645, 1179, 1187), 4 variants only, and **17 with no ctrl proof of any Formal Conjectures statement** (12 have no Lean anywhere in the repo's history). None is JSP-eligible: every exact main-statement proof ctrl has is already covered by someone else. The solved-but-unformalized pool is about 15 hard statements, not 680. `MATH-06` is now: link 834 (and the two variants) in Formal Conjectures, consider one Palomar entry, and correct the README/STATUS counts.
2. **The repo is now public; finish the job.** GitHub reports `IamMikeHelsel/ctrl` as public (checked 2026-10-24; an earlier version of this report said private). The rest of `TOOL-04` still applies: list `ControlsLean` on Reservoir, pin a stable toolchain instead of `v4.36.0-rc1`, and record the date the repo went public, since JSP and Palomar priority run on independently checkable public history.
3. **A direct Lean competitor exists and announced our next topic.** arXiv 2607.19727 (July 2026, "Foundations of Machine-Checked Control Theory in Lean") covers Lyapunov and small-gain on Mathlib and names passivity as its next work. No scout found any proof-assistant formalization of Kalman filtering, POMDP belief planning, SE(3) dynamics or multi-view geometry: `ctrl` appears to be first on all four. Publish the estimation and robotics results before that group expands.
4. **Byers–Nash n = 6 is now the single open order of a named conjecture.** Chen–Tian settled n ≤ 5 and a 2026 preprint (arXiv 2608.20875, seen in search only) refutes the symmetric-maximizer conjecture for n ≥ 7. `MATH-01` already holds the rank ≤ 4 exclusion and exact rational certificates for n = 6. Closing it either way (`MATH-05`) is the flagship research item and a natural Palomar entry.
5. **Nobody sells verified controller or estimator kernels.** The certified channels (Apex.Grace at ASIL D, CODESYS Safety SIL2/3) certify middleware and runtimes, not algorithms; every PLC verification tool in production is bounded model checking of discrete logic. The 2026 DO-178C qualification of CompCert for Airbus/ATR is the first public proof-based tool credit, which lowers the perceived risk of the Lean story. The slot is open.
6. **The first assessor question is the real-to-double gap.** Every proof in `ctrl` is over ℝ; the C99 kernels run on IEEE-754 doubles with a parity test. Lean's rigorous-numerics pieces (girving/interval, LeanCert, the DSLean gappa tactic, FloatSpec) are now just sufficient for straight-line kernels. `IND-02` (8 weeks) is the single most important industrialization enabler, and it must pin the emitter's evaluation order.
7. **ISO/CD 25785-1 is the clearest industrial pull.** The humanoid stability standard (Agility and Boston Dynamics lead the working group; Agility says the safety case was the hard part) wants exactly a machine-checked tip-over or loss-of-balance bound, which `NL-02` plus a capturability certificate (`ROB-04`, `ROB-12`) can supply. ISO 3691-4 for AMRs wants a verified stopping-distance kernel.
8. **Four cross-domain edges were missing from the graph.** Exact pinwheel scheduling is literally an Erdős covering system, so `MATH-03`'s CRT density engine is a schedulability engine (`XD-01`). PAR2 recovery records are Reed–Solomon erasure decoding over GF(2^16), a partial but real bridge to sediment (`XD-02`, `SED-03`). CBF-defined terminal sets give MPC recursive feasibility with less conservatism (`XD-06`). Zero-heap straight-line C99 has a syntactic WCET that feeds the response-time theorems, which is DO-178C timing evidence (`XD-10`, `IND-07`).
9. **sediment avoids every 2025–2026 extractor CVE by construction but cannot prove it.** It never calls the library extractors that shipped zip-slip and PAX advisories; it has no published, machine-checkable statement of what it rejects. Two weeks of fixtures and a named policy (`SED-02`), reproducible creation (`SED-04`) and OpenTelemetry-aligned traces (`SED-07`) are the cheap wins. A Lean-checked path sanitizer via hax/Aeneas (`SED-01`) is the first cross-repo verification artifact. Homebrew 5 now requires notarization, so `SED-05` is blocked on a paid Apple Developer account.
10. **All 2026 funding windows are closed.** DARPA CLARA (April), NSF FMitF (February), AI for Math Fund (March, now topped up by XTX) and the Horizon ECCC call (September) have passed. The next plausible windows are FMitF February 2027 and AI for Math spring 2027; `IND-08` is the proposal vehicle, and it needs an academic PI partner.

## Caveats the scouts flagged

- **Correction (2026-10-24).** An earlier version of this report said the research code was missing from `origin`. It is not. `origin/crossover-research-2026-10-19` holds `lean/Research/` (Byers–Nash, Erdős #885, covering systems) and the `src/ctrl/robotics/` Python/C99 runtime. RoboLean (`Barcode/ReedSolomon.lean`, `RealTime.lean`) lives on `origin/backup/20261020/dev-ctrl/snapshot`. Candidates that build on `ROBO-04`, `MATH-01..03` or the runtime are grounded in real code; none of it is on `main`.
- Several hosts (arxiv.org, lean-lang.org, reservoir, galois.com, conjectures.io, palomar-registry.org, erdosproblems.com) were blocked by the session proxy. Paper-level claims rest on search-result snippets and GitHub mirrors; each candidate lists only URLs the scout actually saw.
- The README credits 29 solved Erdős problems, but only 17 of those numbers appear in `ControlsLean/Bounty/*.lean` on `main` (36, 96, 242, 341, 389, 533, 995, 1055, 1059, 1073, 1102, 1113 do not). Verify each against the Formal Conjectures main statement before any priority claim (`MATH-06`).
- Effort estimates are for one strong engineer and do not include Mathlib review latency, which is the bottleneck for anything upstreamed.

## How to read this

Every candidate below is a node in `docs/SYNERGY_WEIGHTS.json` and is scored by `./ctrl synergy rank -c`. `kind` is explore (new theorem or formalization), productionize (turn a verified result into a tested kernel or tool) or industrialize (package for a standard, customer, prize or market). `in` is the unlock in-weight from READY ideas; `wk` is honest engineer-weeks for one strong person; `conf` is the scout's confidence the opportunity is real and open. Evidence URLs were seen by the scouts in search results or fetched pages; several sandboxes could not fetch arXiv, so treat paper-level claims as pointers to verify, not citations.

## Ranked shortlist

| rank | id | kind | score | wk | conf | payoff | pull | title |
| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | `ROB-01` | explore | 0.522 | 4 | 0.80 | 4 | 0.7 | Geometric SO(3)/SE(3) tracking certificate (Lee-Leok-McClamroch) |
| 2 | `EST-04` | explore | 0.487 | 4 | 0.80 | 4 | 0.4 | Willems' Fundamental Lemma and DeePC certificate in Lean |
| 3 | `ROB-07` | explore | 0.457 | 5 | 0.75 | 5 | 0.7 | Machine-checked optimality certificates for Wahba/Kabsch and pose-graph SDP duals |
| 4 | `ROB-10` | explore | 0.444 | 3 | 0.80 | 3 | 0.4 | Laplacian consensus and displacement-based formation control |
| 5 | `ROB-06` | explore | 0.439 | 4 | 0.75 | 4 | 0.4 | Neural CBF soundness bridge: TorchLean bounds to a Lean forward-invariance theorem |
| 6 | `ROB-02` | explore | 0.431 | 5 | 0.75 | 4 | 0.4 | Invariant EKF: group-affine dynamics imply log-linear error on SE(3)/SE_2(3) |
| 7 | `EST-05` | explore | 0.425 | 3 | 0.75 | 3 | 0.4 | H-infinity (minimax) filter via dual Bounded Real Lemma |
| 8 | `TOOL-01` | productionize | 0.423 | 2 | 0.80 | 3 | 1.0 | ctrl MCP server exposing scratch, check, search, audit and the idea index |
| 9 | `ROB-04` | explore | 0.423 | 4 | 0.65 | 5 | 0.7 | Capturability / DCM push-recovery certificate composed with the ZMP allocator |
| 10 | `TOOL-04` | industrialize | 0.422 | 1 | 0.90 | 3 | 1.0 | Finish going public: Reservoir listing, stable toolchain pin, record the public-since date |
| 11 | `EST-06` | explore | 0.418 | 5 | 0.70 | 4 | 0.4 | Invariant EKF on SO(3)/SE(3): log-linear autonomous error dynamics |
| 12 | `XD-06` | explore | 0.417 | 4 | 0.70 | 4 | 0.4 | Lorentz-cone CBF safe set as MPC terminal set with proven recursive feasibility |
| 13 | `ROB-03` | explore | 0.397 | 5 | 0.70 | 4 | 0.4 | VIO observability: 4-dim unobservable subspace and FEJ consistency theorem |
| 14 | `EST-13` | explore | 0.396 | 3 | 0.80 | 3 | 0.4 | Point-based POMDP value iteration error bounds (PBVI/SARSOP) on Smallwood-Sondik |
| 15 | `MATH-07` | explore | 0.391 | 4 | 0.70 | 3 | 0.7 | Discrete-time Kalman–Yakubovich–Popov lemma (LMI <=> frequency-domain inequality) in Lean |
| 16 | `ROB-11` | explore | 0.391 | 4 | 0.65 | 4 | 0.7 | Whole-body task-priority projection and N-contact closed-form wrench feasibility |
| 17 | `EST-12` | explore | 0.389 | 3 | 0.75 | 3 | 0.4 | Ho-Kalman realization correctness and finite-sample system identification |
| 18 | `TOOL-06` | industrialize | 0.387 | 2 | 0.60 | 4 | 1.0 | Kernel certificate bundle: JSON-LD per kernel with axiom audit, toolchain SHAs, code hashes, parity results and external re-check |
| 19 | `EST-11` | explore | 0.384 | 4 | 0.70 | 4 | 0.4 | Conformal prediction coverage theorem and CP-based safe control |
| 20 | `TOOL-05` | productionize | 0.381 | 4 | 0.60 | 4 | 1.0 | Cedar-style compiled-Lean oracle with differential random testing against the C99/ST kernels |
| 21 | `XD-08` | productionize | 0.380 | 3 | 0.70 | 3 | 0.4 | Verified information-consensus filter for fleets |
| 22 | `XD-12` | productionize | 0.380 | 3 | 0.70 | 3 | 0.4 | Barrier-derived Simplex switching for learned controllers |
| 23 | `XD-10` | industrialize | 0.375 | 5 | 0.60 | 4 | 1.0 | Syntactic WCET bound of generated C99 kernels fed into RTA |
| 24 | `ROB-09` | explore | 0.372 | 3 | 0.80 | 3 | 0.4 | Zhang camera calibration from planar homographies (image of the absolute conic) |
| 25 | `MATH-06` | industrialize | 0.364 | 1 | 0.85 | 2 | 0.4 | Priority rescue: link Erdős 834 (and the 1148/367 variants) in Formal Conjectures, correct the claimed counts |
| 26 | `ROB-12` | industrialize | 0.363 | 4 | 0.60 | 4 | 0.7 | ISO 25785-1 / ISO 3691-4 verified safety-function evidence pack |
| 27 | `XD-05` | productionize | 0.360 | 3 | 0.70 | 3 | 0.4 | Basis-function ILC over the septic trajectory family |
| 28 | `ROB-08` | explore | 0.359 | 3 | 0.70 | 3 | 0.4 | Minimal-solver degeneracies and RANSAC bounds as theorems |
| 29 | `XD-01` | explore | 0.358 | 4 | 0.75 | 4 | 0.4 | Pinwheel scheduling as Erdős covering systems in Lean |
| 30 | `XD-07` | explore | 0.348 | 3 | 0.65 | 3 | 0.7 | Small-gain string stability for robot fleets |
| 31 | `EST-07` | explore | 0.345 | 2 | 0.80 | 2 | 0.4 | Unscented transform sigma-point moment-matching exactness |
| 32 | `TOOL-09` | explore | 0.342 | 3 | 0.60 | 4 | 0.4 | ControlBench: a Croissant-tagged benchmark of ctrl theorem statements with proofs stripped |
| 33 | `ROB-13` | industrialize | 0.337 | 4 | 0.60 | 4 | 0.4 | ASTM F3269 run-time-assurance geofence kernel for drones |
| 34 | `SED-04` | productionize | 0.330 | 2 | 0.85 | 3 | 0.7 | Reproducible ZIP/TAR creation mode (SOURCE_DATE_EPOCH, sorted, normalized) |
| 35 | `EST-09` | explore | 0.330 | 5 | 0.65 | 3 | 0.4 | Moving-horizon estimation robust stability via i-IOSS and MPC duality |
| 36 | `MATH-08` | productionize | 0.330 | 3 | 0.75 | 2 | 0.7 | Kharitonov theorem and interval-Hurwitz stability certificates |
| 37 | `XD-03` | explore | 0.319 | 4 | 0.60 | 3 | 0.7 | Byers-Nash sep bound to certified Riccati/Kalman condition numbers |
| 38 | `EST-08` | explore | 0.317 | 3 | 0.70 | 3 | 0.4 | Rauch-Tung-Striebel fixed-interval smoother and two-filter equivalence |
| 39 | `SED-07` | productionize | 0.310 | 1 | 0.85 | 2 | 0.7 | OpenTelemetry CLI semantic-convention alignment of the JSON trace |
| 40 | `TOOL-12` | productionize | 0.305 | 1 | 0.90 | 2 | 0.4 | CI hygiene: split GitHub cache from Mathlib cache, add lake test/lint and audit targets, schedule Mathlib bumps |
| 41 | `SED-02` | productionize | 0.298 | 2 | 0.80 | 3 | 0.4 | Archive-hardening regression corpus and named extraction policy |
| 42 | `XD-09` | explore | 0.292 | 4 | 0.55 | 3 | 1.0 | Homography ground plane to tilted ZMP/CBF deceleration bound |
| 43 | `IND-01` | industrialize | 0.282 | 4 | 0.50 | 3 | 1.0 | DO-333 evidence pack generator for a verified kernel |
| 44 | `TOOL-03` | explore | 0.275 | 6 | 0.60 | 3 | 0.4 | Upstream four named Mathlib gaps: exp(tA) derivative and x'=Ax, det exp = exp trace, Loewner inverse antitone, PSD Schur complement |
| 45 | `IND-02` | explore | 0.265 | 8 | 0.50 | 4 | 0.7 | Proved IEEE-754 error bounds for straight-line C99 kernels in Lean |
| 46 | `MATH-10` | industrialize | 0.265 | 3 | 0.60 | 2 | 1.0 | SAIR Lean Kernel Challenge entries for the permanent and polynomial-discriminant problems |
| 47 | `XD-02` | productionize | 0.265 | 5 | 0.70 | 3 | 0.4 | Verified PAR2-style recovery records for sediment |
| 48 | `SED-05` | industrialize | 0.264 | 2 | 0.70 | 3 | 1.0 | Notarized Homebrew cask and cargo-dist pipeline with sigstore bundles |
| 49 | `EST-14` | industrialize | 0.261 | 6 | 0.50 | 4 | 0.7 | Verified Joseph/EKF battery state-of-charge kernel for ISO 26262 / EU battery passport |
| 50 | `EST-10` | explore | 0.260 | 6 | 0.55 | 3 | 0.4 | Chance-constrained / CVaR stochastic MPC recursive feasibility |
| 51 | `IND-03` | industrialize | 0.258 | 5 | 0.50 | 3 | 1.0 | Verified numeric function-block library for IEC 61131-3 ST with PLCverif cross-check |
| 52 | `ROB-05` | explore | 0.248 | 8 | 0.55 | 3 | 0.4 | Hybrid systems in Lean: Poincare-map orbit stability and non-Zeno conditions (HZD skeleton) |
| 53 | `XD-04` | explore | 0.244 | 6 | 0.50 | 3 | 1.0 | Occlusion-aware log-depth visual servoing via POMDP belief |
| 54 | `MATH-05` | explore | 0.217 | 6 | 0.50 | 4 | 0.4 | Close the Byers–Nash n=6 symmetric-maximizer case with a kernel-checked certificate |
| 55 | `SED-06` | productionize | 0.212 | 3 | 0.70 | 3 | 0.4 | Read-only zstd, xz, 7z and ZIP-AES support under sediment's limit wrappers |
| 56 | `TOOL-11` | industrialize | 0.212 | 1 | 0.70 | 2 | 0.4 | Agent-facing index upgrade: JSON-LD context on AGENT_IDEA_INDEX, llms.txt and Markdown twins on the Pages site |
| 57 | `IND-04` | productionize | 0.210 | 4 | 0.45 | 2 | 1.0 | ros2_control / Nav2 plugin wrapping zero-heap verified kernels |
| 58 | `TOOL-02` | productionize | 0.206 | 3 | 0.60 | 3 | 1.0 | Prover-tuned inner loop: Goedel-Prover-V2-8B plus kimina-lean-server batch verification and LSP goal feedback |
| 59 | `SED-08` | explore | 0.206 | 2 | 0.65 | 3 | 0.4 | Kani-proved resource accounting for decompression-bomb limits |
| 60 | `SED-03` | explore | 0.198 | 8 | 0.55 | 4 | 0.4 | Verified GF(2^16) PAR2 recovery-record kernel bridging ctrl Reed-Solomon and ArkLib |
| 61 | `SED-01` | explore | 0.198 | 3 | 0.60 | 3 | 0.4 | Lean-checked archive path sanitizer (hax/Aeneas) with Kani harness |
| 62 | `IND-08` | industrialize | 0.197 | 3 | 0.35 | 4 | 1.0 | Grant vehicle: FMitF Feb-2027 / AI-for-Math 2027 proposal for a verified-kernel-to-PLC pipeline |
| 63 | `XD-11` | explore | 0.189 | 4 | 0.50 | 2 | 0.4 | Cross-ratio fiducial detection with Reed-Solomon coded identity |
| 64 | `IND-05` | industrialize | 0.177 | 6 | 0.40 | 3 | 1.0 | Verified attitude/geofence safety module for PX4/ArduPilot with DO-178C-style trace |
| 65 | `TOOL-08` | explore | 0.175 | 1 | 0.45 | 3 | 1.0 | Harmonic Aristotle as an outer loop for Research-branch sorries (Byers-Nash, Erdos) |
| 66 | `EST-15` | industrialize | 0.162 | 5 | 0.50 | 3 | 0.7 | Kalman-filter integrity monitor and protection levels for GNSS/INS |
| 67 | `SED-11` | productionize | 0.154 | 2 | 0.60 | 2 | 0.7 | Signed archive manifest and verify-against-manifest for auditable extraction |
| 68 | `IND-06` | industrialize | 0.146 | 3 | 0.40 | 2 | 0.7 | DO-330-style trusted-base and tool-qualification narrative for the Lean-to-C pipeline |
| 69 | `IND-07` | productionize | 0.146 | 3 | 0.40 | 2 | 0.7 | WCET and schedulability evidence for zero-heap kernels via RTA proofs plus aiT-ready annotations |
| 70 | `MATH-11` | explore | 0.128 | 5 | 0.40 | 2 | 0.4 | Absolute-stability package: Lean-checked Kalman/Aizerman counterexamples and the n<=3 positive case |
| 71 | `SED-10` | industrialize | 0.121 | 3 | 0.50 | 2 | 1.0 | Linux/Windows CLI-first ports with egui GUI as beta |
| 72 | `TOOL-10` | industrialize | 0.118 | 4 | 0.30 | 4 | 0.4 | SEooC-style verified kernel pack offer: certificates plus parity harness plus retainer |
| 73 | `TOOL-07` | explore | 0.113 | 6 | 0.35 | 3 | 0.4 | Rust kernels translated to Lean with Aeneas/hax and proved equal to the ControlsLean spec |
| 74 | `SED-09` | explore | 0.077 | 1 | 0.30 | 1 | 0.4 | Cancellation-latency bound as measured evidence (RTA cross-link, assessed as a stretch) |
| 75 | `IND-09` | explore | 0.066 | 6 | 0.30 | 2 | 0.7 | Verified infusion-rate safety kernel against the FDA Generic PCA pump reference model |
| 76 | `MATH-09` | explore | 0.061 | 6 | 0.35 | 2 | 0.4 | Formalize the few remaining unlinked solved Erdős problems with 2026 papers (1033, 348, 1133, 633) |

## Greedy plan within 12 engineer-weeks

- `TOOL-04` (1 wk, score 0.422) Finish going public: Reservoir listing, stable toolchain pin, record the public-since date
- `MATH-06` (1 wk, score 0.364) Priority rescue: link Erdős 834 (and the 1148/367 variants) in Formal Conjectures, correct the claimed counts
- `SED-07` (1 wk, score 0.310) OpenTelemetry CLI semantic-convention alignment of the JSON trace
- `TOOL-12` (1 wk, score 0.305) CI hygiene: split GitHub cache from Mathlib cache, add lake test/lint and audit targets, schedule Mathlib bumps
- `TOOL-11` (1 wk, score 0.212) Agent-facing index upgrade: JSON-LD context on AGENT_IDEA_INDEX, llms.txt and Markdown twins on the Pages site
- `TOOL-01` (2 wk, score 0.423) ctrl MCP server exposing scratch, check, search, audit and the idea index
- `TOOL-06` (2 wk, score 0.387) Kernel certificate bundle: JSON-LD per kernel with axiom audit, toolchain SHAs, code hashes, parity results and external re-check
- `EST-07` (2 wk, score 0.345) Unscented transform sigma-point moment-matching exactness

## Greedy plan within 26 engineer-weeks

- `TOOL-04` (1 wk, score 0.422) Finish going public: Reservoir listing, stable toolchain pin, record the public-since date
- `MATH-06` (1 wk, score 0.364) Priority rescue: link Erdős 834 (and the 1148/367 variants) in Formal Conjectures, correct the claimed counts
- `SED-07` (1 wk, score 0.310) OpenTelemetry CLI semantic-convention alignment of the JSON trace
- `TOOL-12` (1 wk, score 0.305) CI hygiene: split GitHub cache from Mathlib cache, add lake test/lint and audit targets, schedule Mathlib bumps
- `TOOL-11` (1 wk, score 0.212) Agent-facing index upgrade: JSON-LD context on AGENT_IDEA_INDEX, llms.txt and Markdown twins on the Pages site
- `TOOL-01` (2 wk, score 0.423) ctrl MCP server exposing scratch, check, search, audit and the idea index
- `TOOL-06` (2 wk, score 0.387) Kernel certificate bundle: JSON-LD per kernel with axiom audit, toolchain SHAs, code hashes, parity results and external re-check
- `EST-07` (2 wk, score 0.345) Unscented transform sigma-point moment-matching exactness
- `SED-04` (2 wk, score 0.330) Reproducible ZIP/TAR creation mode (SOURCE_DATE_EPOCH, sorted, normalized)
- `SED-02` (2 wk, score 0.298) Archive-hardening regression corpus and named extraction policy
- `ROB-10` (3 wk, score 0.444) Laplacian consensus and displacement-based formation control
- `EST-05` (3 wk, score 0.425) H-infinity (minimax) filter via dual Bounded Real Lemma
- `SED-05` (2 wk, score 0.264) Notarized Homebrew cask and cargo-dist pipeline with sigstore bundles
- `EST-13` (3 wk, score 0.396) Point-based POMDP value iteration error bounds (PBVI/SARSOP) on Smallwood-Sondik

## Strong domain edges with the fewest concrete projects

| from | to | weight | projects on edge | why |
| --- | --- | ---: | ---: | --- |
| codegen_certification | prizes | 0.5 | 0 | A verified kernel pipeline is grant-shaped (AI for Math Fund tools track, DARPA formal methods programs). |
| vision | nonlinear_safety | 0.5 | 2 | A camera-estimated terrain plane changes the support polygon and ZMP constraint; literature couples vision to steppable regions under ZMP/DCM constraints but not to the closed-form deceleration bound. |
| lean_tooling | prizes | 0.7 | 3 | Prize eligibility and formalizer attribution both require an earliest public commit. |
| realtime_systems | rust_systems | 0.5 | 5 | Reed-Solomon decoding and deadline-bounded cancellation transfer to archive recovery records and cooperative cancellation. |
| vision | estimation | 0.6 | 6 | Multi-view measurement models for filters. |
| lean_tooling | math | 0.7 | 7 | Triage and proof automation are what make the Erdős bounty pipeline cheap. |
| math | realtime_systems | 0.7 | 8 | CoveringCRT exact density products and prime sieves compute exactly what decides exact pinwheel covering/packing feasibility. |
| realtime_systems | controls | 0.5 | 8 | RTA guarantees the sampling-period assumption of every discrete-time theorem. |
| realtime_systems | math | 0.7 | 9 | Exact pinwheel covering is an Erdos covering system; Kawamura's 5/6 density theorem is a covering-density schedulability statement, giving MATH-03 an applied audience and new finite instances. |
| nonlinear_safety | lean_tooling | 0.5 | 9 | Turns ctrl's CBF theorems into the consumer of TorchLean's bound certificates. |
| realtime_systems | nonlinear_safety | 0.5 | 9 | Simplex is a real-time architecture (in repo). |
| estimation | vision | 0.7 | 11 | Kalman pose filtering of homography measurements and POMDP observation models for occluded targets. |
| math | vision | 0.6 | 11 | Exact rational PSD certificates developed for an open matrix inequality become proof-carrying perception outputs. |
| math | prizes | 0.9 | 12 | Solved-but-unformalized Erdős problems are the direct money lane. |
| lean_tooling | controls | 0.6 | 12 | Tactics, Loogle search and the inner loop lower the cost of every new module. |

## Lane IND: Industrialization of verified control kernels

### `IND-01` DO-333 evidence pack generator for a verified kernel

**industrialize** · score 0.282 · 4 wk · confidence 0.50 · payoff 3/5 · domains: codegen_certification, controls, estimation, lean_tooling  
Builds on: `CTRL-01`, `EST-01`, `ROBO-03`.  
Unlocks: `IND-04`, `IND-05`, `IND-06`.  

- **Why now.** CompCert was qualified for the Airbus/ATR MFC_NG in March 2026 with credit claimed under DO-178C, DO-333 and DO-330 — the first public case of proof-based tool credit in airborne certification — and Polytechnique Montréal's 2025-2026 DO-178C UAV work names traceability and labour-intensive formal verification as the open pain points.
- **Prior art.** AdaCore SPARK DO-333 process booklets; NASA DO-333 case studies (theorem proving / model checking / abstract interpretation); CAP2018 drone autopilot at DO-178C Level A using DO-331/332/333; CompCert qualification papers. None generate a trace matrix from proof-assistant metadata.
- **What we would build.** A script that walks the 48 @lean_theorem bindings and emits a DO-333-shaped artifact bundle for one kernel (steady-state Kalman gain or LQR step): formal LLR = theorem statement, proof hash + axiom audit, C99/ST source hash, parity test log, and an objective-by-objective mapping to DO-178C Table A-5/A-6 with an explicit 'not covered' list (float error, WCET, MC/DC, tool qualification).
- **External pull.** standard: DO-178C/DO-333 with the 2026 CompCert precedent; customer: DO-178C UAV programs (Polytechnique/CAP2018 lineage)
- **Edge.** lean_tooling → certification (0.7): The @lean_theorem decorator metadata is already a machine-readable trace link; certification bodies want exactly that link made explicit.
- **Evidence.** <https://compcert.org/> · <https://hal-univ-tlse3.archives-ouvertes.fr/INRIA/hal-01643290> · <https://learn-latest.adacore.com/booklets/adacore-technologies-for-airborne-software/chapters/standards.html> · <https://shemesh.larc.nasa.gov/fm/DO-333-case-studies.html> · <https://publications.polymtl.ca/72401/> · <https://hal.archives-ouvertes.fr/hal-02156141>

### `IND-02` Proved IEEE-754 error bounds for straight-line C99 kernels in Lean

**explore** · score 0.265 · 8 wk · confidence 0.50 · payoff 4/5 · domains: codegen_certification, lean_tooling, robotics, estimation  
Builds on: `ROBO-03`, `EST-01`, `CTRL-01`.  
Unlocks: `IND-01`, `IND-03`, `IND-05`.  

- **Why now.** In 2025-2026 Lean finally got usable rigorous-numerics pieces (Irving's interval, LeanCert, the DSLean gappa tactic, the FloatSpec Flocq port), while the DSLean authors still note the lack of Lean floating-point results — the gap is open and the tools to close it for small kernels now exist.
- **Prior art.** Coq/Rocq: Flocq, Gappa, VCFloat2 (CPP 2024, sound round-off bounds on Clight), CompCert. Lean: FloatSpec (~270 sorry at listing), flean (axiomatic, no intervals), girving/interval, LeanCert, DSLean gappa tactic. ctrl already has exact-Q vs float64 parity tests but no proved bound.
- **What we would build.** For 2-3 straight-line kernels (Rodrigues rotation, scalar/2x2 Kalman update, LQR gain application) a Lean theorem of the form \|float_kernel(x) - real_kernel(x)\| <= eps on a stated input box, discharged with the gappa tactic or LeanCert, plus a C99 emission rule that preserves the evaluation order the bound assumes (no FMA, no reassociation).
- **External pull.** standard: every DO-333/IEC 61508 assessor's first question about real-number proofs; community: Lean numerics is a visible gap named in the DSLean paper
- **Edge.** lean_tooling → codegen (0.8): A proved float bound only holds if codegen fixes evaluation order, turning the emitter into part of the trusted argument.
- **Evidence.** <https://arxiv.org/pdf/2602.18657> · <https://reservoir.lean-lang.org/@Beneficial-AI-Foundation/FloatSpec> · <https://reservoir.lean-lang.org/@girving/interval/dependencies> · <https://reservoir.lean-lang.org/@alerad/LeanCert> · <https://lean-lang.org/doc/reference/4.35.0/Basic-Types/Floating-Point-Numbers/> · <https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf> · <https://arxiv.org/pdf/0801.0523>

### `IND-03` Verified numeric function-block library for IEC 61131-3 ST with PLCverif cross-check

**industrialize** · score 0.258 · 5 wk · confidence 0.50 · payoff 3/5 · domains: codegen_certification, controls, estimation, realtime_systems  
Builds on: `EST-01`, `CTRL-01`, `CTRL-03`, `ROBO-04`.  
Unlocks: `IND-07`.  

- **Why now.** CERN-GSI published 'formal verification of PLCs as a service' for safety-critical programs in Feb 2025 framed against IEC 61508/61511, CODESYS shipped SIL2 (first LTS) and a TÜV Süd SIL3 virtual safety controller in 2025, and all existing PLC verification is bounded model checking of discrete logic — numeric filters/observers/gains in ST are entirely unverified.
- **Prior art.** PLCverif (CERN, ST, CBMC backend, bounded), ESBMC-PLC (Ladder/PLCopen XML), K-ST semantics (found OpenPLC compiler bugs), Soliman-Frey timed-automata models of PLCopen safety FBs, CODESYS validated codegen. No proved numeric FB library.
- **What we would build.** Package ctrl's ST emitter output as PLCopen-XML function blocks (alpha-beta tracker, steady-state Kalman, LQR gain, ISS-bounded saturation) with Lean-derived invariants exported as PLCverif/ESBMC assertions, run bounded checks on the emitted ST, and document the IEC 61508-3 table entries (A.5/A.9) each artifact addresses; test-import into OpenPLC Editor and CODESYS.
- **External pull.** standard: IEC 61508 SIL2/3 and ISO 13849 PLd/e via CODESYS Safety; customer-shaped: CERN-GSI verification service, CODESYS-ecosystem safety OEMs
- **Edge.** estimation → certification (0.6): Kalman/alpha-beta blocks are the first numeric PLC blocks anyone could ship with a proof, which bounded model checkers cannot provide.
- **Evidence.** <https://arxiv.org/pdf/2502.19150> · <https://jacow.org/ICALEPCS2015/papers/WEPGF092.pdf> · <https://www.catalyzex.com/author/Pierre%20Dantas> · <https://doaj.org/article/a130e6215ea943258ad3ed311261d8e2> · <https://www.codesys.com/products/codesys-safety.html> · <https://codesys.com/products/codesys-safety/safety-sil2.html> · <https://www.controleng.com/articles/plcopen-certifies-br-3s-software-solutions/> · <https://eschertech.com/standards/iec61508.php>

### `IND-04` ros2_control / Nav2 plugin wrapping zero-heap verified kernels

**productionize** · score 0.210 · 4 wk · confidence 0.45 · payoff 2/5 · domains: robotics, codegen_certification, controls  
Builds on: `NL-02`, `EST-01`, `ROBO-03`, `CTRL-03`.  
Unlocks: `IND-05`.  

- **Why now.** Apex.Grace is ISO 26262 ASIL D with a ROS 2-compatible API and static memory pools, SYSGO markets reuse of ROS 2 functions up to ASIL D/SIL 4, yet the ROS 2 Safety WG repos have been idle since early 2024 and nothing in Nav2/ros2_control is safety-certified — the algorithm layer is the empty slot.
- **Prior art.** Apex.OS/Grace (certified middleware, 13-step per-package process), ros-safety software_watchdog, ISO 3691-4 practice of a separate safety-rated stop subsystem. No verified controller/estimator plugin for ros2_control found.
- **What we would build.** A ros2_control ControllerInterface and a Nav2 controller/safety-filter plugin that call only the C99 kernels (no heap, no exceptions in the update path), ship the Lean theorem IDs in the plugin description, and demonstrate the CBF safety filter as the 'separate stop logic' the ISO 3691-4 guidance asks for, benchmarked on a MuJoCo or Gazebo unicycle.
- **External pull.** community: ROS 2 Safety WG / Open Robotics; customer-shaped: Apex.AI-SYSGO integrators needing certified algorithm blocks
- **Edge.** nonlinear_safety → robotics (0.6): The Lorentz-cone CBF filter becomes a drop-in 'safety-rated' stop layer for AMR stacks that currently have none.
- **Evidence.** <https://www.apex.ai/apexgrace> · <https://www.sysgo.com/technology-alliances/apexai> · <https://vimeo.com/649645295> · <https://github.com/ros-safety> · <https://discourse.openrobotics.org/t/safety-working-group-survey-on-ros-2-safety/23511> · <https://fictionlab.pl/glossary/iso-3691-4/>

### `IND-08` Grant vehicle: FMitF Feb-2027 / AI-for-Math 2027 proposal for a verified-kernel-to-PLC pipeline

**industrialize** · score 0.197 · 3 wk · confidence 0.35 · payoff 4/5 · domains: codegen_certification, lean_tooling, prizes  
Builds on: `CTRL-01`, `EST-01`, `ROBO-04`.  
Unlocks: `IND-02`, `IND-03`.  

- **Why now.** Every 2026 call relevant to this lane has closed (DARPA CLARA Apr 2026, NSF FMitF 17 Feb 2026, AI for Math Fund 30 Mar 2026, Horizon CL3 ECCC 15 Sep 2026); the next windows are plausibly FMitF Feb 2027 (third Tuesday pattern, unconfirmed) and AI for Math spring 2027 (fund topped up by $13M from XTX), and PROVERS is near its 42-month end, so DARPA follow-ons on 'software certification' are expected.
- **Prior art.** 2026 AI for Math awards went largely to Lean projects (classification of finite simple groups, LeanExplore); FMitF funds formal-methods + domain pairings; CLARA mandated Apache-2.0 open source.
- **What we would build.** A 2-page concept and a demo repo state (IND-02 or IND-03 partially done) ready for abstracts; requires an academic PI partner for FMitF (NSF eligibility), which ctrl does not currently have.
- **External pull.** funding: NSF FMitF, Renaissance Philanthropy AI for Math Fund, DARPA follow-ons
- **Edge.** prizes → certification (0.4): Grant money is the only realistic way to fund the 8-week float-bound work that certification bodies will demand.
- **Evidence.** <https://www.nsf.gov/funding/opportunities/fmitf-formal-methods-field/nsf24-509/solicitation> · <https://www.renaissancephilanthropy.org/ai-for-math-fund> · <https://www.renaissancephilanthropy.org/ai-for-math-fund-2026-projects> · <https://renaissancephilanthropy.org/insights/renaissance-philanthropy-and-xtx-markets-additional-13-million> · <https://www.darpa.mil/sites/default/files/attachment/2026-04/clara-program-darpa-faqs.pdf> · <https://www.darpa.mil/sites/default/files/attachment/2025-04/darpa-portfolio-revolutionizing-cyber-resiliency-military-systems.pdf> · <https://www.darpa.mil/research/programs/pipelined-reasoning-of-verifiers-enabling-robust-systems> · <https://cybersecurity-centre.europa.eu/funding-opportunities/calls-proposals/cybersecurity-horizon-cl3-2026-02-cs-eccc_hr>

### `IND-05` Verified attitude/geofence safety module for PX4/ArduPilot with DO-178C-style trace

**industrialize** · score 0.177 · 6 wk · confidence 0.40 · payoff 3/5 · domains: robotics, nonlinear_safety, codegen_certification  
Builds on: `ROBO-03`, `NL-02`, `CTRL-03`.  
Unlocks: `IND-01`.  

- **Why now.** No formal verification or DO-178C credit exists for PX4/ArduPilot; 2025-2026 academic DO-178C UAV compliance work (Polytechnique) and the CAP2018 Level-A drone process show the demand, and the CompCert 2026 qualification lowers the perceived risk of proof-based credit.
- **Prior art.** ISP RAS partitioned-RTOS quadcopter with deductive + dL proofs on ArduPilot-derived PID; CAP2018 DO-178C Level A drone autopilot; Galois HACMS flight control. No verified SO(3)/quaternion error + CBF geofence module as a C99 drop-in.
- **What we would build.** A C99 module (quaternion error, SO(3) Rodrigues, Lorentz-cone CBF geofence/velocity limiter) compiled into a PX4 or ArduPilot build as a runtime safety filter, with the IND-01 evidence pack and a SITL regression showing zero geofence violations; honest statement that the autopilot around it remains uncertified.
- **External pull.** standard: DO-178C/DO-333; community: PX4/ArduPilot; customer-shaped: DO-178C UAV certification programs
- **Edge.** nonlinear_safety → certification (0.5): A small proved safety filter is the only part of an open autopilot that can realistically carry formal credit.
- **Evidence.** <https://ispras.ru/proceedings/docs/2019/31/4/isp_31_2019_4_39.pdf> · <https://arxiv.org/pdf/2412.08102> · <https://publications.polymtl.ca/63404/1/2025_RimZrelli.pdf> · <https://hal.archives-ouvertes.fr/hal-02156141> · <https://compcert.org/>

### `IND-06` DO-330-style trusted-base and tool-qualification narrative for the Lean-to-C pipeline

**industrialize** · score 0.146 · 3 wk · confidence 0.40 · payoff 2/5 · domains: codegen_certification, lean_tooling  
Builds on: `CTRL-01`.  
Unlocks: `IND-01`, `IND-03`.  

- **Why now.** DO-330 tool-qualification templates were refreshed in Feb 2026, CompCert's 2026 qualification shows a proof-based tool can be qualified, and the NASA/Rockwell/U-Iowa 'qualify the proof-certificate checker instead of the prover' approach has never been written up for Lean (kernel + external checker + axiom audit).
- **Prior art.** NASA CR on formal-methods tool qualification via proof certificates (Rockwell Collins / U. Iowa); AdaCore DO-330 qualification docs for GNAT/SPARK; AbsInt CompCert/aiT qualification. Nothing for Lean 4.
- **What we would build.** A reproducible TQL-5 (Criteria 3) argument: Lean kernel as the checker, independent re-check of all 445 headline theorems, axiom audit as the validation suite, the codegen classified as a verification-support tool with a parity validation suite, and an explicit list of unqualified components (Mathlib trust, clang). Delivered as a document plus CI job.
- **External pull.** standard: DO-330 / ISO 26262-8 tool confidence; community: HCSS / NASA formal-methods-in-certification groups
- **Edge.** lean_tooling → certification (0.5): The existing axiom auditor is already the shape of a DO-330 validation suite.
- **Evidence.** <https://iro.uiowa.edu/esploro/outputs/report/Formal-Methods-Tool-Qualification/9984410859402771> · <https://shemesh.larc.nasa.gov/fm/FMinCert/DO-330-case-studies-RC.html> · <https://airworthinesscert.com/wp-content/uploads/2026/02/DO-330-Tool-Qual-Package.r1.pdf> · <https://www.adacore.com/uploads_gems/do-330-ed-215-tool-qualification-document.pdf> · <https://www.cl.cam.ac.uk:443/~pes20/pip2014-slides/PIP2014-Leroy.pdf> · <https://compcert.org/>

### `IND-07` WCET and schedulability evidence for zero-heap kernels via RTA proofs plus aiT-ready annotations

**productionize** · score 0.146 · 3 wk · confidence 0.40 · payoff 2/5 · domains: realtime_systems, codegen_certification  
Builds on: `ROBO-04`.  
Unlocks: `IND-01`, `IND-03`.  

- **Why now.** aiT Release 25.04i (Apr 2025) is the qualified WCET tool for ISO 26262/DO-178C and consumes exactly the branch-light, loop-bounded C99 that ctrl emits; no verified control library found ships timing evidence alongside its proofs.
- **Prior art.** AbsInt aiT and its qualification kits; RoboLean RealTime/CriticalInstant RTA proofs already in ctrl. No link between the two.
- **What we would build.** Emit per-kernel loop-bound and no-recursion annotations in the C99 output, measure cycle counts on one Cortex-M/ARM target, and feed the measured/analysed WCETs into the Lean RTA fixpoint theorem to produce a machine-checked schedulability certificate for a sample task set.
- **External pull.** standard: DO-178C timing objectives, ISO 26262 Part 6 resource usage; tool: AbsInt aiT users
- **Edge.** realtime_systems → certification (0.5): Turns ROBO-04's RTA theorems from a formalization exercise into certification evidence consumed with the kernels.
- **Evidence.** <https://www.absint.com/factsheets/factsheet_ait_arm_web.pdf> · <https://link.springer.com/chapter/10.1007/978-3-030-47487-4_2> · <https://arxiv.org/pdf/0710.4753>

### `IND-09` Verified infusion-rate safety kernel against the FDA Generic PCA pump reference model

**explore** · score 0.066 · 6 wk · confidence 0.30 · payoff 2/5 · domains: codegen_certification, estimation, controls  
Builds on: `EST-01`, `CTRL-03`.  

- **Why now.** The FDA-backed Generic PCA pump remains the open regulatory benchmark (UPPAAL/PVS verifications exist, 54 software-related Class-1 pump recalls since 2001), and a 2025 arXiv record shows continued interest in SPARK-style verification of syringe drivers; no 2025 FDA formal-methods guidance was found, so pull is academic/regulatory-sandbox rather than commercial.
- **Prior art.** UPenn GPCA reference model, UPPAAL timed-automata translation, PVS UI verification, SPARK syringe driver dissertation (2022/2025).
- **What we would build.** A Lean-verified scalar-Kalman flow estimator plus ISS-bounded rate limiter matching GPCA safety requirements, emitted as C99 with a parity test, and mapped to IEC 62304 class C verification items.
- **External pull.** standard: IEC 62304 / FDA GPCA benchmark; community: medical CPS research groups
- **Edge.** estimation → certification (0.3): Scalar Kalman proofs already in ctrl map directly onto a regulated single-channel device.
- **Evidence.** <https://rtg.cis.upenn.edu/medical/gpca/gpca.html> · <https://repository.upenn.edu/cis_papers/358> · <https://repository.upenn.edu/cis_papers/758/> · <https://web3.arxiv.org/abs/2509.16681>

## Lane ROB: Robotics and vision frontier

### `ROB-01` Geometric SO(3)/SE(3) tracking certificate (Lee-Leok-McClamroch)

**explore** · score 0.522 · 4 wk · confidence 0.80 · payoff 4/5 · domains: robotics, nonlinear_safety, controls  
Builds on: `ROBO-03`, `NL-03`, `EST-02`, `NL-01`.  
Unlocks: `ROB-13`, `ROB-04`, `ROBO-02`.  

- **Why now.** ISO 25785-1 (actively balanced robots) and drone RTA standards now ask for stability evidence; the July-2026 Lean control paper (arXiv 2607.19727) covers Lyapunov/small-gain but nothing on Lie groups, so SE(3) geometric control is the open Lean niche.
- **Prior art.** Paper proofs only (Lee-Leok-McClamroch 2010/2013, Goodarzi-Lee-Lee PID/adaptive). coq-robot has static SO(3)/SE(3)/screws but no dynamics or Lyapunov; Isabelle AFP Lie groups are abstract; Mathlib LieGroup is abstract. No mechanized geometric tracking controller found.
- **What we would build.** Lean theorems: attitude error function Psi(R,Rd)=1/2 tr(I - Rd^T R), error vector e_R, bounds 1/2\|e_R\|^2 <= Psi <= \|e_R\|^2/(2-Psi), dPsi/dt = e_R . e_Omega, and exponential convergence of the attitude/position tracking errors on the sublevel set {Psi < 2} for the rigid-body Euler equations; then the C99 kernel ctrl_geometric_so3_pd bound via @lean_theorem.
- **External pull.** Drone/quadrotor industry and ASTM F3269 RTA; humanoid balance (ISO/CD 25785-1 working group led by Agility/Boston Dynamics)
- **Edge.** robotics → nonlinear_safety (0.7): The SO(3) error function is the Lyapunov function needed to certify any Lie-group CBF or geometric MPC terminal set.
- **Evidence.** <https://arxiv.org/pdf/1003.2005> · <https://mathweb.ucsd.edu/~mleok/pdf/LeLeMc2013_complex.pdf> · <https://arxiv.org/pdf/1411.2986> · <https://pdf.arxiv.org/pdf/1304.6765> · <https://arxiv.org/pdf/2607.19727> · <https://rocq-prover.org/p/coq-robot>

### `ROB-07` Machine-checked optimality certificates for Wahba/Kabsch and pose-graph SDP duals

**explore** · score 0.457 · 5 wk · confidence 0.75 · payoff 5/5 · domains: vision, math, robotics  
Builds on: `VIS-01`, `MATH-01`, `ROBO-03`.  
Unlocks: `ROB-08`, `ROB-02`.  

- **Why now.** Certifiable perception (SE-Sync, TEASER++, Burer-Monteiro overview 2024, certified SLAM talks Nov 2025, 2026 correct-by-construction pose estimation) all rely on post-hoc dual certificates checked in floating point; ctrl already has exact rational LDL^T positive-definiteness certificates from the Byers-Nash work.
- **Prior art.** SE-Sync, Carlone-Rosen duality-gap theorems, TEASER++ (Douglas-Rachford certification), landmark-SLAM certificates; none in a proof assistant.
- **What we would build.** Lean: weak-duality theorem for the quadratic rotation (Wahba) problem over the orthogonal/SO(3) constraint set, theorem that a rational dual matrix Z with (Q - Z) PSD (checked by exact LDL^T) and complementary slackness certifies global optimality of a candidate R; same for the SE-Sync-style pose-graph Lagrangian; a kernel that emits and checks such certificates for ICP/registration outputs.
- **External pull.** MIT-SPARK / certifiable-perception community; citable first machine-checked perception certificate
- **Edge.** math → vision (0.8): Exact rational PSD certificates developed for an open matrix inequality become proof-carrying perception outputs.
- **Evidence.** <https://arxiv.org/pdf/1611.00128> · <https://arxiv.org/pdf/1505.03437> · <https://arxiv.org/abs/2001.07715> · <https://arxiv.org/pdf/2410.00117> · <https://ar5iv.labs.arxiv.org/html/2206.12961> · <https://square.itu.dk/11-11-2025-square-talk-certified-slam-an-overview-by-ola-ronning/> · <https://arxiv.org/pdf/2601.17556>

### `ROB-10` Laplacian consensus and displacement-based formation control

**explore** · score 0.444 · 3 wk · confidence 0.80 · payoff 3/5 · domains: controls, robotics, math  
Builds on: `CTRL-03`, `CTRL-05`, `ROBO-04`.  
Unlocks: `EST-03`, `ROB-12`.  

- **Why now.** 2026 surveys and preprints (SoK on consensus verification; sheaf-theoretic planning) explicitly list Lyapunov consensus stability as unverified future work; Mathlib now has SimpleGraph.lapMatrix with kernel = connected components, so convergence is one Lyapunov step away.
- **Prior art.** Isabelle verification of fault-tolerant discrete consensus (Charron-Bost/Merz), Veil in Lean (protocols); no mechanized Laplacian/dynamical consensus or formation control.
- **What we would build.** Lean: for a connected undirected graph, x' = -L x converges to the average (continuous) and x+ = (I - eps L) x converges for eps < 2/lambda_max (discrete, via DiscreteLyapunov); displacement-based formation as consensus on offsets; link to FleetDeadlock for warehouse fleets; C99 kernel.
- **External pull.** Warehouse fleet vendors (Geek+, Locus-type) and swarm-drone research; cited gap in 2026 preprints
- **Edge.** math → robotics (0.6): Mathlib spectral graph theory becomes a multi-robot convergence certificate.
- **Evidence.** <https://arxiv.org/pdf/2608.21935> · <https://arxiv.org/pdf/2605.01879> · <https://arxiv.org/pdf/0902.4098> · <https://hal-univ-tlse3.archives-ouvertes.fr/INRIA/inria-00539899>

### `ROB-06` Neural CBF soundness bridge: TorchLean bounds to a Lean forward-invariance theorem

**explore** · score 0.439 · 4 wk · confidence 0.75 · payoff 4/5 · domains: nonlinear_safety, lean_tooling, robotics  
Builds on: `NL-02`, `CTRL-03`, `NL-01`.  
Unlocks: `ROB-13`, `ROB-12`.  

- **Why now.** TorchLean (Feb 2026, ICML 2026) gives Lean-checkable IBP/CROWN certificates for networks, and 2025-2026 neural-CBF verifiers (symbolic derivative bounds, linear bound propagation, LightCROWN) are all external numeric tools; nobody has closed the loop to a machine-checked safety theorem.
- **Prior art.** TorchLean (network semantics + bound checking, no CBF); Zhang et al. exact ReLU NCBF verification, Hu 2025, Vertovec 2026 (numeric); shielding papers (AAAI 2025, realizable shields) without provers.
- **What we would build.** Lean theorem: if a cover of the safe-set boundary band by boxes is given, h is L-Lipschitz on each box and the sampled CBF condition holds with margin L*diam, then the CBF inequality holds everywhere; combined with ctrl's discrete-time CBF forward-invariance theorem this yields closed-loop safety from a TorchLean-checked certificate. Deliverable: a certificate format + checker and one MuJoCo example.
- **External pull.** Safe-RL / learning-based control community; TorchLean maintainers; any robot vendor shipping learned safety filters
- **Edge.** nonlinear_safety → lean_tooling (0.7): Turns ctrl's CBF theorems into the consumer of TorchLean's bound certificates.
- **Evidence.** <https://arxiv.org/abs/2602.22631> · <https://reservoir.lean-lang.org/@lean-dojo/TorchLean> · <https://proceedings.mlr.press/v270/hu25a.html> · <https://proceedings.mlr.press/v331/vertovec26a.html> · <https://arxiv.org/pdf/2310.09360> · <https://arxiv.org/html/2410.02038v1>

### `ROB-02` Invariant EKF: group-affine dynamics imply log-linear error on SE(3)/SE_2(3)

**explore** · score 0.431 · 5 wk · confidence 0.75 · payoff 4/5 · domains: estimation, robotics, math  
Builds on: `ROBO-03`, `EST-01`, `EST-02`.  
Unlocks: `ROB-03`, `VIS-01`.  

- **Why now.** 2025 work (arXiv 2506.01514) settled left/right-invariant equivalence under covariance reset, and contact-aided invariant EKFs are the de facto legged-robot estimator; no proof assistant has the core Barrau-Bonnabel theorem.
- **Prior art.** Barrau-Bonnabel (TAC) paper proofs; Isabelle AFP Lie Groups (abstract, no filtering); ctrl EST-01 is Euclidean Kalman. No mechanization found.
- **What we would build.** Lean: definition of group-affine vector fields on matrix Lie groups (concrete SE(3) and SE_2(3) as 4x4/5x5 matrices), theorem that the invariant error eta = Xhat X^-1 obeys an autonomous ODE independent of the trajectory, the linearized error equation in the Lie algebra via adjoint6, and the resulting trajectory-independent Riccati equation; a Python/C99 IEKF kernel bound to these theorems.
- **External pull.** Legged/humanoid state estimation (contact-aided InEKF), VIO/SLAM consistency community (OpenVINS)
- **Edge.** robotics → estimation (0.8): SE3Kinematics adjoint functoriality is exactly the algebra that makes the IEKF error dynamics linear.
- **Evidence.** <https://arxiv.org/pdf/1410.1465> · <https://arxiv.org/pdf/2506.01514> · <https://arxiv.org/pdf/1903.05384> · <https://arxiv.org/pdf/1702.06680> · <https://arxiv.org/abs/2407.19211v1>

### `ROB-04` Capturability / DCM push-recovery certificate composed with the ZMP allocator

**explore** · score 0.423 · 4 wk · confidence 0.65 · payoff 5/5 · domains: robotics, nonlinear_safety, codegen_certification  
Builds on: `NL-02`, `CTRL-04`, `ROBO-04`.  
Unlocks: `ROB-12`, `ROB-11`.  

- **Why now.** ISO/CD 25785-1 targets loss-of-balance of actively stabilized robots (draft mid-2025, 3-year clock); Agility says the safety case was the hard part. ctrl already proves the friction-cone/ZMP deceleration bound; capture-point theory is the missing stepping half.
- **Prior art.** Koolen/Pratt capturability and Englsberger DCM are paper theory (URLs not seen this session: search budget exhausted); IS-MPC proves CoM/ZMP stability from recursive feasibility; SOS on HZD (Walking with Confidence). No mechanization.
- **What we would build.** Lean: LIPM divergent component xi' = omega (xi - p_zmp), closed-form 0-step and 1-step capture regions as explicit sets, theorem that a step inside the region with ZMP inside the (Lean-verified) 4-contact support polygon yields bounded xi; composition with NL-02 gives an end-to-end 'no tip-over under push of magnitude F' certificate and a C99 kernel for MuJoCo quadruped/humanoid push tests.
- **External pull.** ISO TC299/WG12 humanoid safety standard; Agility, Boston Dynamics, Figure, Unitree safety cases
- **Edge.** certification → robotics (0.6): A quantitative tip-over bound is the artefact the draft standard's risk categories are asking for.
- **Evidence.** <https://www.iso.org/standard/91469.html> · <https://www.techbriefs.com/component/content/article/53111-safety-in-motion-setting-the-standard-for-humanoid-robots> · <https://www.designworldonline.com/?p=628358> · <https://arxiv.org/pdf/1901.08505.pdf> · <https://awesomepapers.io/robotics/papers/1903.08327>

### `ROB-03` VIO observability: 4-dim unobservable subspace and FEJ consistency theorem

**explore** · score 0.397 · 5 wk · confidence 0.70 · payoff 4/5 · domains: estimation, vision, controls  
Builds on: `CTRL-05`, `EST-01`, `ROBO-03`.  
Unlocks: `ROB-02`, `VIS-01`.  

- **Why now.** FEJ/OC-EKF are standard in every production VIO (OpenVINS, MSCKF) but the nullspace-preservation argument exists only as paper linear algebra; ctrl's dual-annihilator Observability.lean is the exact tool to state it coordinate-free.
- **Prior art.** Kottas et al. ISER 2012, Li-Mourikis IJRR 2013, OpenVINS FEJ documentation; no proof-assistant formalization.
- **What we would build.** Lean theorems: for the linearized IMU-camera error model, the explicit 4-column nullspace (global position, rotation about gravity) lies in the kernel of the observability matrix; evaluating Jacobians at first estimates preserves this kernel (FEJ), and naive re-linearization strictly shrinks it (the inconsistency counterexample as a theorem).
- **External pull.** OpenVINS/MSCKF community; AR/VR and drone VIO vendors who need consistency arguments
- **Edge.** controls → vision (0.7): Coordinate-free observability from CTRL-05 turns a VIO folklore result into a theorem.
- **Evidence.** <https://www-users.cse.umn.edu/~stergios/papers/ISER-2012-OC-VINS-MSCKF.pdf> · <https://intra.ece.ucr.edu/~mourikis/papers/Li2013IJRR.pdf> · <https://docs.ros.org/en/api/ov_core/html/fej.html> · <https://arxiv.org/pdf/2207.08214>

### `ROB-11` Whole-body task-priority projection and N-contact closed-form wrench feasibility

**explore** · score 0.391 · 4 wk · confidence 0.65 · payoff 4/5 · domains: robotics, nonlinear_safety  
Builds on: `NL-02`, `ROBO-03`, `NL-03`.  
Unlocks: `ROB-04`, `ROB-12`.  

- **Why now.** Humanoid loco-manipulation stacks (multi-contact MPC 2022-2025, contact-implicit MPC 2024-2025) have no feasibility guarantees; ctrl's 4-contact bilinear allocator with zero torque drift is the only closed-form verified piece and generalizing it to N contacts plus a verified priority projection is the natural next kernel.
- **Prior art.** IS-MPC recursive feasibility (paper); hierarchical QP / null-space projection literature (URLs not seen this session); no mechanization.
- **What we would build.** Lean: strict task-priority null-space projection P = I - J^+ J leaves higher-priority task residuals unchanged (Moore-Penrose algebra, extending the Pythagorean nullspace IK); N-contact generalization of the bilinear ZMP + proportional shear allocator with explicit Lorentz-cone feasibility conditions and zero net torque; C99 kernel + MuJoCo humanoid benchmark.
- **External pull.** Humanoid companies replacing 1 kHz QPs with certified closed forms; ISO 25785-1 evidence
- **Edge.** robotics → realtime_systems (0.5): Closed-form allocation removes solver non-convergence from the WCET analysis in ROBO-04.
- **Evidence.** <https://arxiv.org/pdf/1901.08505.pdf> · <https://arxiv.org/pdf/2408.07855> · <https://arxiv.org/pdf/2510.19974> · <https://deepai.org/publication/multi-contact-mpc-for-dynamic-loco-manipulation-on-humanoid-robots>

### `ROB-09` Zhang camera calibration from planar homographies (image of the absolute conic)

**explore** · score 0.372 · 3 wk · confidence 0.80 · payoff 3/5 · domains: vision, math  
Builds on: `VIS-01`.  
Unlocks: `ROB-08`, `ROBO-02`.  

- **Why now.** Every HBVS/visual-servoing and SfM deployment assumes a calibrated K; ctrl's homography and 4-point rigidity theorems make the two linear constraints per view a short derivation, and no proof assistant has any calibration theory.
- **Prior art.** Zhang TR98 / Sturm-Maybank; textbook treatments; nothing mechanized.
- **What we would build.** Lean: H = K [r1 r2 t] implies h1^T omega h2 = 0 and h1^T omega h1 = h2^T omega h2 with omega = K^-T K^-1; three views in general position determine omega up to scale; recovery of K by Cholesky; plus the rational-arithmetic checker in the Python runtime.
- **External pull.** Camera/vision pipelines; completes the 'verified visual servoing' story for ROBO-02
- **Edge.** vision → robotics (0.4): A verified K closes the gap between the HBVS theorems and real cameras.
- **Evidence.** <https://users.ece.northwestern.edu/~yingwu/teaching/EECS432/Reading/Zhang_TR98.pdf> · <https://arxiv.org/pdf/1707.09332> · <https://www.ce.unipr.it/people/medici/geometry_en/node163.html>

### `ROB-12` ISO 25785-1 / ISO 3691-4 verified safety-function evidence pack

**industrialize** · score 0.363 · 4 wk · confidence 0.60 · payoff 4/5 · domains: codegen_certification, robotics, realtime_systems  
Builds on: `NL-02`, `ROBO-03`, `ROBO-04`, `CTRL-03`.  
Unlocks: `ROB-04`, `ROB-11`.  

- **Why now.** ISO/CD 25785-1 is in committee draft (started July 2025, 3-year timeline) with Agility and Boston Dynamics leading; ISO 3691-4:2023 requires every AMR safety function to be verified; vendors cannot certify against a draft but can design against it now and want reusable evidence.
- **Prior art.** No formal-methods artefacts referenced by either standard; vendor guides give worked stopping-distance examples only.
- **What we would build.** A documented package: (1) AMR protective-field/stopping-distance kernel from Unicycle arc odometry + CBF braking with a Lean-proved bound, (2) tip-over/friction-cone deceleration bound from NL-02 (+ ROB-04 when available), (3) RTA/Simplex switching from ROBO-04, each with C99/IEC 61131-3 ST output, axiom audit report and traceability matrix mapped to the draft clauses.
- **External pull.** ISO TC299/WG12 participants (Agility, Boston Dynamics, A3), AMR vendors under ISO 3691-4; TUV/UL assessors
- **Edge.** certification → codegen (0.6): Standards want testable artefacts; the C99/ST kernels plus Lean audit are the artefact.
- **Evidence.** <https://www.iso.org/standard/91469.html> · <https://www.i-scoop.eu/iso-25785-1-explained-and-what-it-means-for-humanoid-robot-safety/> · <https://novanta.com/?p=980> · <https://www.technologyreview.com/2025/06/11/1118519/humanoids-safety-rules/amp/> · <https://www.fabrico.io/blog/iso-3691-4-driverless-industrial-trucks/> · <https://www.geekplus.com/resources/knowledge-base/amr-safety-standards-and-compliance-the-enterprise-guide-to-risk-mitigation-and-operational-excellence>

### `ROB-08` Minimal-solver degeneracies and RANSAC bounds as theorems

**explore** · score 0.359 · 3 wk · confidence 0.70 · payoff 3/5 · domains: vision, math  
Builds on: `VIS-01`, `MATH-04`.  
Unlocks: `ROB-07`, `ROB-09`.  

- **Why now.** 2025 Galois-group computations for minimal problems and the CVPR-2022 instability theory show solver degeneracies are an active topic; OpenCV P3P instability bug reports (2025) show industrial pain; ctrl already has rank-8 uniqueness and cheirality, so the degenerate complement is one step away.
- **Prior art.** Classical results (Hartley-Zisserman, Grunert P3P, Maybank critical surfaces) and recent algebraic-geometry papers; no mechanization.
- **What we would build.** Lean: (a) coplanar scene points force a rank drop of the 8-point constraint matrix so the essential matrix is not unique (complement of eq_smul_of_rank_eq_eight) and the homography path is the correct fallback; (b) P3P has at most 4 physical solutions and the danger-cylinder configuration is singular; (c) RANSAC iteration bound N >= log(1-p)/log(1-w^s) via Mathlib probability; (d) chirality selects a unique pose among the 4 essential-matrix decompositions.
- **External pull.** OpenCV/COLMAP maintainers; SfM vendors; teaching
- **Edge.** math → vision (0.5): Rank/Galois-theoretic facts about minimal problems become executable preconditions for solvers.
- **Evidence.** <https://arxiv.org/pdf/2507.10407> · <https://openaccess.thecvf.com/content/CVPR2022/papers/Fan_On_the_Instability_of_Relative_Pose_Estimation_and_RANSACs_Role_CVPR_2022_paper.pdf> · <https://hub.harborframework.com/tasks/abundant/opencv__opencv-27736> · <https://arxiv.org/pdf/1007.1432> · <https://arxiv.org/pdf/2309.08690>

### `ROB-13` ASTM F3269 run-time-assurance geofence kernel for drones

**industrialize** · score 0.337 · 4 wk · confidence 0.60 · payoff 4/5 · domains: codegen_certification, robotics, nonlinear_safety, realtime_systems  
Builds on: `ROBO-04`, `NL-02`, `CTRL-03`.  
Unlocks: `ROB-01`, `ROB-06`.  

- **Why now.** ASTM F3269 RTA is the accepted route to bound uncertified autopilots (GE M100 program), NASA proved geofence constraints in PVS, and the 2025-2026 shielding literature is converging on the same enforcer pattern; a Lean-verified enforcer with a C99 kernel is directly reusable.
- **Prior art.** NASA PVS geofence proofs; GE F3269 implementation; DLR Lola monitors; VeriPhy monitors. None in Lean, none with an SE(3) stability certificate behind the recovery controller.
- **What we would build.** Lean: enforcer soundness (if the monitored command would exit the keep-in polytope within the reaction horizon then the verified recovery controller is engaged and keeps the state inside, using the CBF/ISS bounds), Simplex switching from RoboLean, exported as C99 and tested in a MuJoCo quadrotor benchmark; later backed by ROB-01's SE(3) certificate.
- **External pull.** UAS integrators seeking FAA/EASA waivers via ASTM F3269; drone OEMs
- **Edge.** realtime_systems → certification (0.5): RTA is where verified WCET switching and verified control bounds meet a published aviation standard.
- **Evidence.** <https://par.nsf.gov/servlets/purl/10215462> · <https://ntrs.nasa.gov/api/citations/20190000716/downloads/20190000716.pdf> · <https://elib.dlr.de/118317> · <https://uh-ir.tdl.org/items/b7c29e04-4c39-4f0b-a530-3063b1e39974/full> · <https://arxiv.org/html/2410.02038v1>

### `ROB-05` Hybrid systems in Lean: Poincare-map orbit stability and non-Zeno conditions (HZD skeleton)

**explore** · score 0.248 · 8 wk · confidence 0.55 · payoff 3/5 · domains: controls, robotics, math  
Builds on: `CTRL-03`, `CTRL-05`, `EST-02`.  
Unlocks: `ROB-04`, `ROB-11`.  

- **Why now.** Hybrid-system formalization lives only in Isabelle (dL AFP, Foster/Munive) and KeYmaera X; the July-2026 Lean control paper claims hybrid coverage only at the statement level. Legged-robot HZD results (arXiv 2509.00294, Sept 2025) are proved by hand.
- **Prior art.** Isabelle/HOL dL (Bohrer CPP 2017), Foster-Munive hybrid verification, KeYmaera X/VeriPhy; nothing in Lean; no mechanized HZD or Zeno results anywhere.
- **What we would build.** Lean: hybrid system with flow + guard + reset, executions, a sufficient non-Zeno condition (dwell time), and the theorem that an exponentially stable fixed point of the Poincare map (via existing discrete Lyapunov/Jury results) gives a stable hybrid periodic orbit; then HZD: invariance of the zero-dynamics surface under reset.
- **External pull.** Legged locomotion community (Ames/Grizzle lineage); hybrid-systems verification community
- **Edge.** controls → robotics (0.5): Discrete-time Lyapunov machinery already in ctrl becomes the stability engine for gaits via the Poincare map.
- **Evidence.** <https://devel.isa-afp.org/entries/Differential_Dynamic_Logic.html> · <https://repositum.tuwien.at/handle/20.500.12708/136157> · <https://logic.kastel.kit.edu/ap/pub/VeriPhy.pdf> · <https://arxiv.org/abs/2509.00294v1> · <https://grizzle.robotics.umich.edu/files/Robotic_Walking_HSCC_2015.pdf> · <https://arxiv.org/pdf/2607.19727>

## Lane EST: Estimation, probabilistic and learning-based control

### `EST-04` Willems' Fundamental Lemma and DeePC certificate in Lean

**explore** · score 0.487 · 4 wk · confidence 0.80 · payoff 4/5 · domains: controls, estimation, math  
Builds on: `CTRL-04`, `CTRL-05`, `EST-01`.  
Unlocks: `EST-09`, `EST-12`, `EST-10`.  

- **Why now.** Dec 2025 KTH preprint shows the stochastic DeePC decision subspace is the null space of the Kalman-predictor innovation Hankel, tying data-driven control to ctrl's Kalman predictor; Jan 2026 results classify all DeePC reformulations; no proof assistant has the lemma.
- **Prior art.** Paper proofs only: Willems et al. 2005, De Persis-Tesi 2019 (arXiv 1903.06842), van Waarde et al. controllability relaxations (arXiv 2102.02953). No Lean/Coq/Isabelle mechanization found in standard or extended search.
- **What we would build.** Lean definitions of persistency of excitation and Hankel trajectory matrix; theorem that every length-L trajectory of a controllable LTI lies in the Hankel column span (and converse); corollary data-driven LQR/MPC predictor with recursive feasibility via MPCFeasibility.lean.
- **External pull.** Data-driven control community (Dörfler/Coulson DeePC, De Persis-Tesi); citable first formalization; CDC/L4DC venue
- **Edge.** estimation → controls (0.8): Kalman innovation null space (EST-01) is exactly the stochastic DeePC constraint subspace.
- **Evidence.** <https://arxiv.org/abs/2512.14520v1> · <https://arxiv.org/pdf/2209.06414> · <https://arxiv.org/pdf/2102.02953> · <https://ar5iv.org/html/1903.06842> · <https://ar5iv.labs.arxiv.org/html/2303.08707> · <https://www.imperial.ac.uk/events/146099/data-driven-control-of-general-linear-systems-extensions-of-the-fundamental-lemma-for-stochastic-and-descriptor-settings>

### `EST-05` H-infinity (minimax) filter via dual Bounded Real Lemma

**explore** · score 0.425 · 3 wk · confidence 0.75 · payoff 3/5 · domains: estimation, controls  
Builds on: `CTRL-02`, `EST-01`, `CTRL-01`.  
Unlocks: `EST-14`, `EST-15`, `EST-06`.  

- **Why now.** BoundedRealHInf.lean already proves the completion-of-squares and worst-case-disturbance tightness; the filter-side dual is a few hundred lines away and no ITP has an H-inf filter.
- **Prior art.** Shaked-Theodor 1992 (BRL-derived a priori/a posteriori H-inf filter gains), Park-Kailath 1997 LMI form, Zhou-Doyle Riccati form; none mechanized.
- **What we would build.** Indefinite estimation Riccati with feasibility condition P^-1 + C^T C - gamma^-2 I > 0, l2-gain bound from (process,measurement) noise to estimation error, worst-case tightness, and comparison with the Joseph/Kalman gain.
- **External pull.** Robust estimation users in aerospace/automotive where noise statistics are unknown; direct reuse in EST-14/EST-15
- **Edge.** controls → estimation (0.9): The existing H-inf Bounded Real Lemma dualizes almost verbatim to the minimax filter.
- **Evidence.** <https://folk.ntnu.no/skoge/prost/proceedings/ifac2002/data/content/00060/60.pdf> · <https://arxiv.org/pdf/1812.08307>

### `EST-06` Invariant EKF on SO(3)/SE(3): log-linear autonomous error dynamics

**explore** · score 0.418 · 5 wk · confidence 0.70 · payoff 4/5 · domains: estimation, robotics, math  
Builds on: `ROBO-03`, `EST-01`, `EST-02`, `CTRL-03`.  
Unlocks: `EST-15`, `VIS-01`, `ROBO-02`.  

- **Why now.** IEKF is now the default estimator for legged robots and IMU dead reckoning (2024-2026 InEKF/DRIFT work, iterated IEKF 2024) with zero machine-checked guarantees; ctrl's SE(3) adjoint functoriality module supplies the needed Lie machinery.
- **Prior art.** Barrau-Bonnabel 2015/2017 (paper proofs of autonomy of invariant error and local stability), Hartley et al. RSS 2018 contact-aided InEKF; no formalization found.
- **What we would build.** Lean theorem: group-affine dynamics implies invariant error obeys a state-independent linear ODE in log coordinates (log-linear property); discrete-time IEKF covariance Riccati on the Lie algebra; SE_2(3) IMU model and ISS envelope for the linearization remainder.
- **External pull.** Legged-robot and GNSS/INS industry adoption of InEKF; citable first formalization of invariant filtering
- **Edge.** robotics → estimation (0.85): SE(3) adjoint functoriality (ROBO-03) is the exact algebra that makes IEKF error dynamics autonomous.
- **Evidence.** <https://arxiv.org/pdf/1410.1465> · <https://arxiv.org/pdf/1310.2539> · <https://arxiv.org/abs/2404.10665v2> · <https://arxiv.org/html/2403.16252v1> · <https://par.nsf.gov/biblio/10632263> · <https://m.roboticsproceedings.org/rss14/p50.html>

### `EST-13` Point-based POMDP value iteration error bounds (PBVI/SARSOP) on Smallwood-Sondik

**explore** · score 0.396 · 3 wk · confidence 0.80 · payoff 3/5 · domains: estimation, robotics, math  
Builds on: `EST-03`, `ROBO-04`.  
Unlocks: `ROBO-04`.  

- **Why now.** No POMDP mechanization exists (TUM lists it as an open thesis topic; Isabelle/Coq/Lean MDP libraries stop at full observability); 2025 tighter POMDP value-bound work renews interest; ctrl already has the PWLC backup.
- **Prior art.** Isabelle MDP (Schaffeler-Abdulaziz AFP 2021/AAAI 2023), Coq CertRL, Lean mdplib (finite-horizon DP, VaR MDPs), AFP Hidden Markov Models (forward/Viterbi); none handle belief-space value bounds.
- **What we would build.** Lean proof that the alpha-vector backup is a gamma-contraction in sup norm over the simplex, the Pineau-Gordon-Thrun point-based error bound in terms of belief-set density, and the sawtooth upper bound used by SARSOP.
- **External pull.** Verified planning under uncertainty (TUM/Nipkow group interest), robotics POMDP planners
- **Edge.** estimation → robotics (0.5): Certified epsilon-optimal belief planning plugs into fleet scheduling under uncertainty (ROBO-04).
- **Evidence.** <https://wwwnipkow.cs.tum.edu/students/verified_planning_under_uncertainty/index.html> · <https://arxiv.org/pdf/1110.0027.pdf> · <https://arxiv.org/pdf/2502.06523> · <https://www.ri.cmu.edu/?p=9237> · <https://ojs.aaai.org/index.php/AAAI/article/view/26759/26531> · <https://reservoir.lean-lang.org/@formalproofs/mdplib>

### `EST-12` Ho-Kalman realization correctness and finite-sample system identification

**explore** · score 0.389 · 3 wk · confidence 0.75 · payoff 3/5 · domains: estimation, controls, math  
Builds on: `CTRL-05`, `EST-01`.  
Unlocks: `EST-04`, `EST-08`.  

- **Why now.** Finite-sample Ho-Kalman theory matured 2021-2025 (Oymak-Ozay TAC 2021, Tsiamis-Pappas, Sun-Wang 2025 pole bounds) and is the bridge between ctrl's Gramian modules and learning-based control; deterministic core is pure linear algebra already present.
- **Prior art.** Ho-Kalman 1966, Kung; Oymak-Ozay/Tsiamis-Pappas sample complexity; no mechanization found.
- **What we would build.** Lean theorem that the Hankel matrix of Markov parameters factors as observability x controllability with rank n, and that the balanced realization recovers (A,B,C) up to similarity; optional concentration-bound layer.
- **External pull.** System identification and learning-based control community; sets up EST-04
- **Edge.** controls → estimation (0.6): Gramian/observability modules give both Hankel factors for free.
- **Evidence.** <https://par.nsf.gov/servlets/purl/10312038> · <https://arxiv.org/pdf/1903.09122> · <https://arxiv.org/html/2503.16331v5> · <https://ar5iv.labs.arxiv.org/html/1912.12309>

### `EST-11` Conformal prediction coverage theorem and CP-based safe control

**explore** · score 0.384 · 4 wk · confidence 0.70 · payoff 4/5 · domains: estimation, controls, math  
Builds on: `EST-01`, `CTRL-04`.  
Unlocks: `EST-10`, `NL-02`.  

- **Why now.** Lindemann-Pappas et al. survey (revised Apr/Aug 2025) made CP the standard distribution-free safety tool for learned predictors in control; the exchangeability coverage theorem is unformalized in any prover and Mathlib now has the probability base to do it.
- **Prior art.** Paper proofs (Vovk; Angelopoulos-Bates; Theoretical Foundations of CP 2024); no Lean/Isabelle artifact found.
- **What we would build.** Mathlib-level exchangeable finite sequences and rank/quantile lemma; split-conformal 1-alpha coverage theorem; corollary CP-tube constraint tightening for MPC.
- **External pull.** Learning-enabled CPS verification community (CPS-VO tutorials 2025); strong citation potential
- **Edge.** math → controls (0.7): A one-page probabilistic theorem unlocks distribution-free safety for learned predictors inside verified MPC.
- **Evidence.** <https://arxiv.org/abs/2409.00536v3> · <https://arxiv.org/pdf/2411.11824> · <https://arxiv.org/pdf/2107.07511> · <https://ar5iv.labs.arxiv.org/html/2202.13415>

### `EST-07` Unscented transform sigma-point moment-matching exactness

**explore** · score 0.345 · 2 wk · confidence 0.80 · payoff 2/5 · domains: estimation, math  
Builds on: `EST-01`.  
Unlocks: `EST-14`, `EST-06`.  

- **Why now.** 2026 polynomial-UKF and higher-order UT papers restate the moment-matching claims; a small finite-sum Lean proof settles exactly which moments the symmetric 2n+1 set matches and for which kappa.
- **Prior art.** Julier-Uhlmann classical UT; HOUT (arXiv 2006.13429) has an appendix moment-matching proof; no mechanization found.
- **What we would build.** Lean lemmas: symmetric sigma set reproduces mean and covariance exactly given any S with S S^T = P, all odd central moments vanish, fourth-moment condition on kappa; statement of third-order Gaussian exactness.
- **External pull.** UKF is ubiquitous in BMS SoC and navigation stacks; feeds EST-14
- **Edge.** math → estimation (0.4): Pure polynomial-identity proof style already used in ctrl applies directly.
- **Evidence.** <https://arxiv.org/pdf/2603.20259> · <https://arxiv.org/pdf/2006.13429>

### `EST-09` Moving-horizon estimation robust stability via i-IOSS and MPC duality

**explore** · score 0.330 · 5 wk · confidence 0.65 · payoff 3/5 · domains: estimation, controls, nonlinear_safety  
Builds on: `CTRL-04`, `CTRL-03`, `EST-01`.  
Unlocks: `EST-10`, `EST-14`.  

- **Why now.** Knufer-Muller/Allan-Rawlings settled nonlinear MHE RGAS via i-IOSS in 2021-2023 and the data-based MHE dual of DeePC appeared; MPCFeasibility.lean's shifted-tail proof is the exact dual argument.
- **Prior art.** Knufer-Muller 2021 (time-discounted FIE/MHE RGAS iff i-IOSS), Schiller-Muller Lyapunov function for MHE, Allan-Rawlings FIE; no mechanization.
- **What we would build.** Lean definition of (time-discounted) i-IOSS; full-information estimator cost compatibility; theorem that MHE with sufficiently long horizon is robustly globally exponentially stable.
- **External pull.** Process-control and automotive MHE users (constrained estimation); academic citation
- **Edge.** controls → estimation (0.7): MPC recursive-feasibility machinery dualizes to MHE horizon arguments.
- **Evidence.** <https://arxiv.org/pdf/2105.02764> · <https://ar5iv.arxiv.org/html/2305.06614> · <https://arxiv.org/pdf/2203.16090> · <https://arxiv.org/pdf/2111.04979>

### `EST-08` Rauch-Tung-Striebel fixed-interval smoother and two-filter equivalence

**explore** · score 0.317 · 3 wk · confidence 0.70 · payoff 3/5 · domains: estimation  
Builds on: `EST-01`.  
Unlocks: `EST-12`, `VIS-01`.  

- **Why now.** Batch/factor-graph estimation (GTSAM-style) is smoothing; ctrl has forward Joseph and Woodbury but no backward pass, which is the missing half of offline calibration and SLAM back-ends.
- **Prior art.** Textbook RTS 1965 and two-filter smoothers; no ITP formalization found (search budget exhausted before fetching a canonical source; standard result).
- **What we would build.** Backward gain recursion, smoothed covariance recursion, proof that the smoothed estimate is MMSE given all data, and equivalence with information-form backward pass via InformationFilter.lean.
- **External pull.** SLAM/visual-inertial back-ends (GTSAM) and offline sensor calibration
- **Edge.** estimation → vision (0.5): Smoothing is the estimator behind bundle-adjustment-style pose graphs that VIS-01 feeds.
- **Evidence.** <https://arxiv.org/pdf/2111.04979>

### `EST-14` Verified Joseph/EKF battery state-of-charge kernel for ISO 26262 / EU battery passport

**industrialize** · score 0.261 · 6 wk · confidence 0.50 · payoff 4/5 · domains: estimation, codegen_certification, realtime_systems  
Builds on: `EST-01`, `SED`, `ROBO-04`, `CTRL-03`.  
Unlocks: `EST-07`, `EST-05`.  

- **Why now.** EU Battery Regulation 2023/1542 makes the battery passport (SoH/SoC data from the BMS) mandatory from 18 Feb 2027; ISO/PAS 8800 + ISO 26262 assessments of SoC estimators appeared in 2025; no public ISO 26262 safety case for an EKF SoC estimator exists.
- **Prior art.** Many EKF SoC implementations (HIL/MCU studies); PRISM model checking of KF numerical divergence (Evangelidis-Parker); ASIL-rated sensing hardware (LEM); no verified estimator software.
- **What we would build.** Thevenin equivalent-circuit model + EKF Jacobian spec in Lean, Joseph-form update theorem bound to a @lean_theorem C99 kernel with IEEE-754 parity test, ISS envelope for linearization error, and a traceability package mapping theorems to ISO 26262 Part 6 work products.
- **External pull.** EU battery passport deadline Feb 2027; BMS suppliers (ISO 26262 ASIL B-D); ISO/PAS 8800 assessors
- **Edge.** estimation → certification (0.8): A machine-checked covariance update is the kind of evidence ISO 26262 tool-qualification arguments lack for BMS software.
- **Evidence.** <https://codibly.com/blog/articles/eu-battery-regulation-passport-bess-operators> · <https://www.eurobat.org/wp-content/uploads/2025/12/EUROBAT-position-on-provisions-of-data-resulting-from-battery-uses-_.pdf> · <https://www.tuvsud.com/en-us/knowledge-hub/articles/understanding-the-new-eu-battery-regulation> · <https://arxiv.org/abs/2509.03270v1> · <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC12049525/> · <https://www.prismmodelchecker.org/bibitem.php?key=EP21>

### `EST-10` Chance-constrained / CVaR stochastic MPC recursive feasibility

**explore** · score 0.260 · 6 wk · confidence 0.55 · payoff 3/5 · domains: controls, estimation, nonlinear_safety  
Builds on: `CTRL-04`, `EST-01`, `CTRL-03`.  
Unlocks: `NL-02`, `EST-11`.  

- **Why now.** 2025-2026 wave: SMPC recursive feasibility under unbounded disturbances (arXiv 2504.17718), CVaR-in-cost-and-constraints with exponential stability, DR-MPC with disturbance-affine feedback (Apr 2026); none mechanized and Mathlib now has the kernel/Ionescu-Tulcea infrastructure.
- **Prior art.** Hewing-Zeilinger PRS, Lorenzen first-step constraint, Mark-Liu DR tube MPC; Bøving-Matheja ITP 2026 Lean MDP/HeyVL is the closest formal infrastructure.
- **What we would build.** Lean CVaR definition and convexity, tube/PRS constraint tightening lemma, and recursive feasibility + mean-square stability theorem for a linear SMPC with Kalman state estimate.
- **External pull.** Stochastic MPC adoption in energy and automotive; risk-sensitive control literature
- **Edge.** estimation → nonlinear_safety (0.6): Kalman covariance feeds the probabilistic reachable set used to tighten CBF/MPC constraints.
- **Evidence.** <https://arxiv.org/pdf/2504.17718> · <https://par.nsf.gov/servlets/purl/10617656> · <https://www.emergentmind.com/papers/2604.12555> · <https://arxiv.org/abs/2109.09558> · <https://arxiv.org/abs/2602.19867>

### `EST-15` Kalman-filter integrity monitor and protection levels for GNSS/INS

**industrialize** · score 0.162 · 5 wk · confidence 0.50 · payoff 3/5 · domains: estimation, codegen_certification, robotics  
Builds on: `EST-01`, `EST-05`, `EST-06`.  
Unlocks: `ROBO-04`.  

- **Why now.** ARAIM is moving beyond aviation (EC-funded ARAIMTOO; Racelis-Joerger 2026 modified HPL) and KF-based RAIM is being patented for autonomous takeoff/landing; filter-based integrity (recursive VPL) has no machine-checked treatment.
- **Prior art.** DO-229 snapshot RAIM, ARAIM (Stanford/Blanch), KAIST KF integrity architecture, Honeywell filter-augmented RAIM patents; power-grid WLS bad-data chi-square test (arXiv 2104.13908) is the same residual algebra; none mechanized.
- **What we would build.** Lean theorems for innovation covariance S = C P C^T + R, normalized-innovation chi-square monitor correctness, worst-case-slope protection-level bound (least-squares and Joseph-recursive forms), bound to a C99 kernel.
- **External pull.** GNSS receiver and automotive localization vendors; ISO 21448 SOTIF arguments; power-grid state estimation reuse
- **Edge.** estimation → certification (0.6): Residual-test correctness is shared by aviation integrity, automotive localization and grid bad-data detection.
- **Evidence.** <https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/12153147> · <https://koasas.kaist.ac.kr/handle/10203/265428> · <https://www.gmv.com/de-de/kommunikation/veranstaltungen/araim-fuer-anwendungen-jenseits-der-luftfahrt> · <https://navi.ion.org/index.php/admin/highwire/citation/153335/medlars_journal> · <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9786326/> · <https://arxiv.org/pdf/2104.13908>

## Lane MATH: Math prizes, bounties and open problems

### `MATH-07` Discrete-time Kalman–Yakubovich–Popov lemma (LMI <=> frequency-domain inequality) in Lean

**explore** · score 0.391 · 4 wk · confidence 0.70 · payoff 3/5 · domains: controls, math, lean_tooling  
Builds on: `CTRL-02`, `CTRL-03`, `CTRL-05`.  
Unlocks: `MATH-08`, `NL-01`.  

- **Why now.** No KYP formalization exists in Lean, Isabelle or Coq (only an unverified 2026 Lur'e-systems repo), while Formal Conjectures now routes research-grade formal proofs to Palomar and ctrl already has the Bounded Real Lemma and controllability machinery the proof needs.
- **Prior art.** Classical proofs (Willems optimal-control route, spectral factorization); ctrl BoundedRealHInf.lean, Gramian.lean, Reachability.lean; Mathlib lacks numerical range and Lyapunov equations
- **What we would build.** Lean statement and proof of KYP for controllable (A,B): existence of symmetric P with the LMI iff the FDI on the unit circle, plus the strict/positive-real corollaries used by Popov/circle criteria
- **External pull.** Mathlib/Palomar credibility; absolute-stability certificates demanded by safety-critical controls (IEC 61508 style evidence)
- **Edge.** controls → nonlinear_safety (0.7): KYP turns ctrl's linear H-infinity/ISS certificates into Lur'e absolute-stability guarantees for sector-bounded nonlinearities.
- **Evidence.** <https://github.com/AEjonanonymous/Improving-on-Popov> · <https://en.wikipedia.org/wiki/Kalman%E2%80%93Yakubovich%E2%80%93Popov_lemma> · <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Matrix/Spectrum.lean>

### `MATH-06` Priority rescue: link Erdős 834 (and the 1148/367 variants) in Formal Conjectures, correct the claimed counts

**industrialize** · score 0.364 · 1 wk · confidence 0.85 · payoff 2/5 · domains: prizes, lean_tooling, math  
Builds on: `MATH-04`.  
Unlocks: `MATH-09`.  

- **Why now.** Since 2026-10-17 plby/lean-proofs added ctrl problems 291 and 367 and Erdős 261 was registered on Palomar by a third party; 363 of 424 solved FC statements already carry formal_proof links, and ctrl has no PR in TheJustinSunPrize/awards.
- **Prior art.** plby/lean-proofs (563 problems), Jayyhk/williamjblair/anatoliiohorodnyk/linrock/Woett repos; 9 JSP awards so far (4 Lean, all to W. van Doorn)
- **What we would build.** Per the 2026-10-24 audit: FC formal_proof link for erdos_834.parts.ii (proof on main at erdos/ErdosLab/Erdos834.lean), short inline FC proofs or links for erdos_1148.variants.weaker and erdos_367.variants.k_le_two, optional Palomar entry for 834, a type_of% check binding each proof to the FC theorem, and removal of the 17 unsupported numbers from README/STATUS/portfolio docs. No JSP filing: every exact main-statement proof is already covered by others.
- **External pull.** Formal Conjectures solved-status credit, Palomar citation; credibility of the repo's public claims
- **Edge.** prizes → lean_tooling (0.5): A reusable statement-faithfulness + lean-verify + Palomar packaging script serves every future claim.
- **Evidence.** <https://raw.githubusercontent.com/plby/lean-proofs/main/data/sources.yaml> · <https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md> · <https://raw.githubusercontent.com/TheJustinSunPrize/awards/main/docs/award-process.md> · <https://github.com/TheJustinSunPrize/awards/tree/main/awards>

### `MATH-08` Kharitonov theorem and interval-Hurwitz stability certificates

**productionize** · score 0.330 · 3 wk · confidence 0.75 · payoff 2/5 · domains: controls, math, codegen_certification  
Builds on: `CTRL-05`.  
Unlocks: `MATH-07`, `ROBO-04`.  

- **Why now.** A 2026 preprint claims a Lean 4 formalization of an SPR-synthesis theorem for sixth-order interval polynomial families, signalling demand, but Kharitonov itself is still unformalized and ctrl already has Routh–Hurwitz for degrees 2 and 3.
- **Prior art.** Kharitonov 1978; Bhattacharyya–Chapellat–Keel textbook; ctrl Hurwitz2/Hurwitz3.lean; no Mathlib Hermite–Biehler theorem
- **What we would build.** Lean proof of the four-vertex-polynomial criterion for degrees <= 4 (via explicit Routh tables) and a C99 kernel emitting the interval-stability check for PLC/robot controllers
- **External pull.** robust-stability evidence for certification packages; Mathlib contribution
- **Edge.** controls → certification (0.5): Interval-coefficient stability is the form in which plant uncertainty is specified in safety cases.
- **Evidence.** <https://arxiv.org/html/2609.26541> · <https://people.engr.tamu.edu/spb/books/robustcontrol/chapter05.pdf> · <https://www.tandfonline.com/doi/full/10.1080/21642583.2026.2646370>

### `MATH-10` SAIR Lean Kernel Challenge entries for the permanent and polynomial-discriminant problems

**industrialize** · score 0.265 · 3 wk · confidence 0.60 · payoff 2/5 · domains: lean_tooling, math, prizes  
Builds on: `CTRL-05`, `MATH-04`.  

- **Why now.** Stage 1 (deadline 2026-11-20 AoE) scores kernel-reducible verified algorithms by instruction count; two of the eight tasks (0/1 permanent, exact discriminant of a degree-24 monic polynomial) are matrix/polynomial computations close to ctrl's companion-matrix and determinant proofs.
- **Prior art.** Starter repo with Spec.lean per problem; unofficial community harnesses (Amey-Thakur/SAIR-LEAN-KERNEL-CHALLENGE)
- **What we would build.** Kernel-efficient verified Ryser/Gray-code permanent and resultant-based discriminant implementations with proofs against the fixed Spec.lean
- **External pull.** XTX-funded SAIR competition, recognition only (Tao, de Moura, Morrison, Breitner organizers)
- **Edge.** lean_tooling → codegen (0.4): Instruction-count-optimized kernel algorithms transfer to verified numeric kernels in the C99 codegen path.
- **Evidence.** <https://github.com/SAIRcompetition/lean-kernel-challenge> · <https://github.com/SAIRcompetition> · <https://terrytao.wordpress.com/2026/09/16/sair-competition-lean-kernel-challenge/>

### `MATH-05` Close the Byers–Nash n=6 symmetric-maximizer case with a kernel-checked certificate

**explore** · score 0.217 · 6 wk · confidence 0.50 · payoff 4/5 · domains: math, controls, prizes  
Builds on: `MATH-01`, `EST-02`, `CTRL-01`.  
Unlocks: `MATH-06`.  

- **Why now.** arXiv:2608.20875 (Aug 2026) reportedly refutes the symmetric-maximizer conjecture for every n >= 7 while Chen–Tian settled n <= 5, leaving n = 6 as the only open order; ctrl already holds the rank <= 4 exclusion and 10/10 rational LDL^T certificates for that case.
- **Prior art.** Byers–Nash 1987 (flawed Thm 9); Chen–Tian 2015 proof for n<=5; 2026 counterexample preprint for n>=7; no Lean work besides ctrl lean/Research/ByersNash*.lean
- **What we would build.** Analytic closure of the J vs {I2,F,G} off-diagonal cross-term (or an exact rational n=6 counterexample seeded by the n>=7 construction), audited to standard axioms and registered on Palomar
- **External pull.** citable resolution of the last open case of a named SIAM conjecture; Palomar registry entry; Lyapunov-conditioning guarantee for CARE/Kalman–Bucy solvers
- **Edge.** math → estimation (0.6): k(A) <= s(A) at n=6 certifies symmetric-cone conditioning checks for 6-state Riccati/Lyapunov solvers used in EST-02.
- **Evidence.** <https://epubs.siam.org/doi/10.1137/140974031> · <https://arxiv.org/pdf/2608.20875> · <https://scholar.hit.edu.cn/en/publications/note-on-on-the-singular-vectors-of-the-lyapunov-operator-by-r-bye/>

### `MATH-11` Absolute-stability package: Lean-checked Kalman/Aizerman counterexamples and the n<=3 positive case

**explore** · score 0.128 · 5 wk · confidence 0.40 · payoff 2/5 · domains: controls, nonlinear_safety, math  
Builds on: `CTRL-02`, `NL-01`.  
Unlocks: `MATH-07`.  

- **Why now.** With KYP (MATH-07) in place, machine-checked Fitts/Leonov–Kuznetsov counterexamples plus the low-dimensional positive results would be the first formal account of a classical control conjecture; a 2026 Lean Lur'e project shows community interest but no verified status.
- **Prior art.** Kalman 1957, Aizerman 1949, Fitts 1966, Leonov–Kuznetsov hidden-oscillation analyses (background, not re-verified this session)
- **What we would build.** Exact-arithmetic certificate of a periodic orbit for a 4th-order Lur'e counterexample and Lean proofs of the n<=3 Kalman-conjecture cases
- **External pull.** citation value in control theory; Palomar if judged research-grade
- **Edge.** nonlinear_safety → controls (0.4): Hidden-oscillation counterexamples are the canonical warning for sector-based safety filters.
- **Evidence.** <https://github.com/AEjonanonymous/Improving-on-Popov>

### `MATH-09` Formalize the few remaining unlinked solved Erdős problems with 2026 papers (1033, 348, 1133, 633)

**explore** · score 0.061 · 6 wk · confidence 0.35 · payoff 2/5 · domains: math, prizes  
Builds on: `MATH-04`.  

- **Why now.** Only 15 solved FC main statements lack any external Lean proof as of 2026-10-21; four of them (Fan 1988 degree-sum, Geneson 2609.25107, Yang 2609.14769, Beeson–Laczkovich–Zhang 2604.03609) have self-contained modern papers and no merged JSP record.
- **Prior art.** FC files 1033/348/1133/633.lean (statements only); open JSP PRs exist for 1033 and 1133; plby has none of the four
- **What we would build.** Complete sorry-free proofs of the FC main statements (not variants) in a public ctrl repo with pinned SHAs
- **External pull.** JSP formalizer share (legacy process), Formal Conjectures link, Palomar entry
- **Edge.** math → lean_tooling (0.3): Extremal-graph and interpolation proofs stress finite-combinatorics automation reusable elsewhere.
- **Evidence.** <https://github.com/google-deepmind/formal-conjectures/commits/main> · <https://github.com/google-deepmind/formal-conjectures/pull/6787> · <https://raw.githubusercontent.com/TheJustinSunPrize/awards/main/problems/README.md>

## Lane TOOL: Lean ecosystem tooling and productization

### `TOOL-01` ctrl MCP server exposing scratch, check, search, audit and the idea index

**productionize** · score 0.423 · 2 wk · confidence 0.80 · payoff 3/5 · domains: lean_tooling  
Builds on: `CTRL-01`, `MATH-01`, `SED`.  
Unlocks: `TOOL-02`, `TOOL-08`, `TOOL-11`.  

- **Why now.** lean-lsp-mcp (534 stars) and cameronfreer/lean4-skills (468 stars) made MCP the de facto agent interface to Lean in 2026; MCP 2025-11-25 resources with audience/priority annotations fit the idea index exactly; Claude Code/Codex/Cursor all speak it.
- **Prior art.** lean-lsp-mcp (generic LSP/search tools), gleachkr/aristotle-mcp, PyPantograph; none expose project-specific tactic cheat sheets, axiom audits as a Lake target, bounty triage, or a curated idea index as resources.
- **What we would build.** A `ctrl mcp` subcommand (Python, stdio) wrapping scratch_check.sh, check.sh --fast, loogle.sh, Audit.lean and triage, plus resources ctrl://ideas/{id}, ctrl://theorems/{name}, ctrl://playbook, so any agent host can drive ctrl without the Ollama loop; ship a SKILL.md for the host.
- **External pull.** community demand: lean4-skills + lean-lsp-mcp user base; Claude Code plugin marketplace
- **Edge.** lean_tooling → math (0.6): Gives frontier agents (Aristotle, Claude Code) direct access to the Research-branch sorries and idea index.
- **Evidence.** <https://github.com/oOo0oOo/lean-lsp-mcp> · <https://github.com/oOo0oOo/lean-lsp-mcp/blob/main/docs/tools.md> · <https://github.com/cameronfreer/lean4-skills> · <https://modelcontextprotocol.io/specification/2025-11-25/server/resources>

### `TOOL-04` Finish going public: Reservoir listing, stable toolchain pin, record the public-since date

**industrialize** · score 0.422 · 1 wk · confidence 0.90 · payoff 3/5 · domains: lean_tooling, prizes  
Builds on: `SED`.  
Unlocks: `TOOL-03`, `TOOL-06`, `TOOL-09`, `TOOL-11`, `MATH-01`, `MATH-02`.  

- **Why now.** The repo is public as of 2026-10-24 (GitHub API), so the remaining work is the Reservoir listing, replacing the v4.36.0-rc1 pin with a stable toolchain, and documenting the public-since date that JSP/Palomar priority depends on.
- **Prior art.** Reservoir already lists LeanCopilot, Pantograph, NormalForms, leanr; BOUNTIES.md already documents the JSP public-repo rule.
- **What we would build.** Flip visibility, add GitHub topics (lean4, control-theory, mathlib), bump lakefile keywords, move from v4.36.0-rc1 to the matching stable tag when released, verify Reservoir pickup or add a manual reservoir-index entry.
- **External pull.** Justin Sun Prize public-repo rule; Reservoir inclusion criteria
- **Edge.** lean_tooling → prizes (0.8): Prize eligibility and formalizer attribution both require an earliest public commit.
- **Evidence.** <https://raw.githubusercontent.com/RileyBetts/lean-tee/main/docs/GETTING_STARTED.md> · <https://github.com/leanprover/reservoir> · <https://github.com/leanprover/reservoir-index> · <https://github.com/TheJustinSunPrize/awards> · <https://theplatformengineering.substack.com/p/github-actions-2026-pricing-changes>

### `TOOL-06` Kernel certificate bundle: JSON-LD per kernel with axiom audit, toolchain SHAs, code hashes, parity results and external re-check

**industrialize** · score 0.387 · 2 wk · confidence 0.60 · payoff 4/5 · domains: codegen_certification, lean_tooling  
Builds on: `ROBO-01`, `ROBO-02`, `ROBO-03`, `VIS-01`.  
Unlocks: `TOOL-10`.  

- **Why now.** 2026 Lean papers already ship proof-carrying certificates checked under pinned toolchains; Lean4Lean gives an independent typechecker; lean-lsp-mcp's lean_verify shows agents want machine-readable axiom evidence; ctrl's Audit.lean output is currently a CI log line.
- **Prior art.** Apex.AI ASIL-D SEooC artifact packs; Certora enterprise retainers with written rules; Lean covering-code certificates; AGENT_IDEA_INDEX.json schema 1.0.0.
- **What we would build.** A `ctrl certify <kernel>` command emitting certificate.jsonld with schema.org context: theorem names, `#print axioms` result, Lean/Mathlib revs, SHA-256 of emitted C99/ST, parity-test stats, optional lean4export + Lean4Lean re-check status; served as MCP resources and committed under site/.
- **External pull.** assessors (TÜV-style SEooC), procurement due diligence; no named customer yet
- **Edge.** lean_tooling → certification (0.7): Turns the axiom audit into a sellable, re-checkable artifact.
- **Evidence.** <https://arxiv.org/pdf/2606.09600> · <https://arxiv.org/abs/2403.14064> · <https://github.com/oOo0oOo/lean-lsp-mcp/blob/main/docs/tools.md> · <https://github.com/mlcommons/croissant>

### `TOOL-05` Cedar-style compiled-Lean oracle with differential random testing against the C99/ST kernels

**productionize** · score 0.381 · 4 wk · confidence 0.60 · payoff 4/5 · domains: codegen_certification, realtime_systems  
Builds on: `ROBO-01`, `ROBO-02`, `EST-01`, `CTRL-01`.  
Unlocks: `TOOL-06`, `TOOL-10`.  

- **Why now.** Lean 4.30.0 (May 2026) completed the LCNF C emission path; AWS runs Cedar (Lean model + Rust, millions of DRT inputs, release-gated) and SampCert (Lean via C FFI, in AWS Clean Rooms) in production, so the pattern is industrially accepted; ctrl's parity test today is 8.88e-16 Python-vs-C on hand-emitted code with no executable Lean in the loop.
- **Prior art.** Cedar verification-guided development; SampCert FFI + extractor; VeriPhy (verified executables via HOL4/CakeML); Galois Lean robotics demo. None covers control kernels with rational certificates.
- **What we would build.** For each @lean_theorem kernel, a computable Lean definition (over ℚ or Float) compiled with `lake build` and linked through FFI/CLI, a property-based harness feeding identical inputs to Lean, Python, C99 and ST interpreters, and a release gate like Cedar's (no kernel ships unless model, proofs and DRT are current).
- **External pull.** customer-recognized pattern (AWS Cedar/SampCert); SEooC buyers expect executable evidence
- **Edge.** codegen → certification (0.8): Differential testing is the artifact assessors accept as the bridge from proof to shipped C.
- **Evidence.** <https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing> · <https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean-ffi> · <https://github.com/leanprover/SampCert/blob/main/REPRODUCING.md> · <https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/IR/EmitC.lean> · <https://lean-lang.org/doc/reference/latest/releases/v4.30.0/>

### `TOOL-09` ControlBench: a Croissant-tagged benchmark of ctrl theorem statements with proofs stripped

**explore** · score 0.342 · 3 wk · confidence 0.60 · payoff 4/5 · domains: lean_tooling, controls, estimation  
Builds on: `CTRL-01`, `CTRL-03`, `EST-01`, `NL-01`, `ROBO-01`.  
Unlocks: `TOOL-02`.  

- **Why now.** miniF2F is saturated (88-90% for open 32B models); AutoformBench (Oct 13 2026) and MathlibPR (ICML 2026) show appetite for new Lean benchmarks; NeurIPS dataset tracks require Croissant metadata; ctrl has 445 audited headline theorems in a domain absent from every existing benchmark.
- **Prior art.** miniF2F, PutnamBench, MathOlympiadBench, Lean-workbook, AutoformBench; none is applied-math/control.
- **What we would build.** Split statements/proofs for 445 theorems (plus 48 kernel specs), pin Mathlib rev, provide a kimina-lean-server evaluation harness, Croissant JSON-LD, baseline numbers for Goedel-V2-8B/32B and a generic coder, and a short paper.
- **External pull.** community: prover-model groups and NeurIPS/ICLR dataset tracks
- **Edge.** controls → lean_tooling (0.6): ctrl's corpus is the out-of-distribution test the prover community lacks.
- **Evidence.** <https://ai.meta.com/research/publications/autoformbench-a-lean-formalization-benchmark-for-advanced-mathematics> · <https://icml.cc/virtual/2026/82531> · <https://github.com/Goedel-LM/Goedel-Prover-V2> · <https://github.com/mlcommons/croissant> · <https://arxiv.org/pdf/2605.15079>

### `TOOL-12` CI hygiene: split GitHub cache from Mathlib cache, add lake test/lint and audit targets, schedule Mathlib bumps

**productionize** · score 0.305 · 1 wk · confidence 0.90 · payoff 2/5 · domains: lean_tooling  
Builds on: `SED`.  
Unlocks: `TOOL-04`, `TOOL-05`.  

- **Why now.** lean-action defaults to use-github-cache: true, which stores ~2.15 GiB of Mathlib oleans per entry and can exhaust the 10 GiB repo cache quota (practitioner reports, 2025-2026); ctrl's workflow uses the defaults, runs no tests, and has the mathlib-update-action schedule commented out while pinned to an RC toolchain.
- **Prior art.** lean-action, mathlib-update-action, docgen-action already wired; unsorry ADRs document the cache split.
- **What we would build.** Set use-github-cache: false and cache only .lake/build keyed on lean-toolchain + lake-manifest.json; add [[lean_exe]] audit (scripts/Audit.lean) and a `lake test` driver so `lean-action` test/lint run; enable the daily update schedule; publish docgen output as the Pages site next to llms.txt.
- **External pull.** none beyond internal reliability; prerequisite for Reservoir build badges
- **Edge.** lean_tooling → codegen (0.3): A real test target is where the C99/ST parity harness and DRT would run in CI.
- **Evidence.** <https://github.com/leanprover/lean-action> · <https://dev.to/iroha1203/taming-a-40-minute-lean-ci-three-rounds-three-wrong-suspects-7ke> · <https://raw.githubusercontent.com/agenticsnz/unsorry/main/docs/adrs/ADR-045-Gate-A-Library-Build-Cache.md> · <https://mintlify.wiki/leanprover-community/mathlib4/contributing/building-testing>

### `TOOL-03` Upstream four named Mathlib gaps: exp(tA) derivative and x'=Ax, det exp = exp trace, Loewner inverse antitone, PSD Schur complement

**explore** · score 0.275 · 6 wk · confidence 0.60 · payoff 3/5 · domains: math, controls, lean_tooling  
Builds on: `CTRL-01`, `CTRL-02`, `EST-02`.  
Unlocks: `TOOL-10`.  

- **Why now.** Verified against Mathlib master today: MatrixExponential.lean has no derivative/ODE lemma and carries a TODO for det-exp-trace; Order.lean has the Loewner order but no inverse antitonicity; PosDef.fromBlocks₁₁ needs PosDef+Invertible; SVD matrix PRs were closed unmerged in Nov 2025/Apr 2026 and Jordan form is absent, so small targeted PRs are welcome.
- **Prior art.** Mathlib Jordan-Chevalley, NormedSpace.exp, Loewner order (Order.lean), Schur determinant lemmas; arXiv 2607.19727 and LeanForControl formalize control on top of Mathlib without upstreaming; MathlibPR shows review is the bottleneck.
- **What we would build.** Mathlib-style PRs (<300 lines each) for HasDerivAt (t ↦ exp (t•A)), uniqueness of x'=Ax, det_exp, PosSemidef inverse antitone and congruence monotone under the MatrixOrder scope, and fromBlocks PSD criterion with PosSemidef A via a pseudo-inverse or kernel condition; ctrl then depends on them.
- **External pull.** community: Mathlib maintainers; explicit TODO in MatrixExponential.lean
- **Edge.** math → controls (0.7): Continuous-time CARE/Kalman-Bucy/Lyapunov integrals all need the exp(tA) ODE lemma.
- **Evidence.** <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean> · <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Matrix/Order.lean> · <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/PosDef.lean> · <https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+singular+value+decomposition> · <https://icml.cc/virtual/2026/82531>

### `TOOL-11` Agent-facing index upgrade: JSON-LD context on AGENT_IDEA_INDEX, llms.txt and Markdown twins on the Pages site

**industrialize** · score 0.212 · 1 wk · confidence 0.70 · payoff 2/5 · domains: lean_tooling, rust_systems  
Builds on: `SED`.  
Unlocks: `TOOL-01`.  

- **Why now.** llms.txt grew 8.8x to 36K sites by May 2026 but 97% get zero AI requests (Ahrefs), while OpenAI's Agents SDK and Lighthouse 13.3 support it; MCP resources are what agents actually read; Croissant/schema.org JSON-LD is now standard for dataset discovery. Cheap insurance, low measured payoff.
- **Prior art.** docs/AGENT_IDEA_INDEX.json and site/index.html already exist; llms.txt spec; Croissant 1.1.
- **What we would build.** Add @context (schema.org SoftwareSourceCode/CreativeWork + Dataset), generate site/llms.txt and per-doc .md twins with rel=describedby links in CI, and reuse the same JSON as MCP resources in TOOL-01.
- **External pull.** community: agent crawlers; Lighthouse agentic audits
- **Edge.** archive_formats → lean_tooling (0.3): One structured index feeds both web crawlers and MCP clients.
- **Evidence.** <https://github.com/AnswerDotAI/llms-txt> · <https://ppc.land/llms-txt-adoption-rises-8-8x-but-97-of-files-get-zero-ai-requests/> · <https://www.rankability.com/llms-report/> · <https://github.com/mlcommons/croissant>

### `TOOL-02` Prover-tuned inner loop: Goedel-Prover-V2-8B plus kimina-lean-server batch verification and LSP goal feedback

**productionize** · score 0.206 · 3 wk · confidence 0.60 · payoff 3/5 · domains: lean_tooling  
Builds on: `SED`.  
Unlocks: `TOOL-09`.  

- **Why now.** Goedel-Prover-V2-8B (Apache-2.0, 84.6% miniF2F pass@32) matches 671B DeepSeek-Prover-V2 and runs on one consumer GPU; kimina-lean-server ships Docker images with configurable Lean versions; ctrl loop still uses a generic 7B coder with no goal-state feedback.
- **Prior art.** Goedel-V2 verifier is pinned to Lean 4.9 + Mathlib 2f65ba7; Lean Copilot tracks v4.35/v4.36.0-rc1; LeanTool wires Pantograph into Aider/Cline. Nobody has measured prover-model gain on Mathlib-heavy control lemmas.
- **What we would build.** Replace the single-shot Ollama call in loop.py with (a) a prover model served via Ollama/vLLM, (b) N-sample batch verification through kimina-lean-server against ctrl's own Mathlib v4.36 build, (c) lean_goal/lean_multi_attempt feedback between rounds; report solve-rate on a held-out set of ctrl lemmas.
- **External pull.** community: prover-model authors seek out-of-distribution benchmarks; no customer
- **Edge.** lean_tooling → controls (0.4): Faster lemma closure directly accelerates CTRL/EST/NL theorem throughput.
- **Evidence.** <https://github.com/Goedel-LM/Goedel-Prover-V2> · <https://iclr.cc/virtual/2026/poster/10007912> · <https://github.com/project-numina/kimina-lean-server> · <https://github.com/lean-dojo/LeanCopilot>

### `TOOL-08` Harmonic Aristotle as an outer loop for Research-branch sorries (Byers-Nash, Erdos)

**explore** · score 0.175 · 1 wk · confidence 0.45 · payoff 3/5 · domains: math, lean_tooling, prizes  
Builds on: `MATH-01`, `MATH-02`, `MATH-03`.  
Unlocks: `MATH-01`.  

- **Why now.** Aristotle's API accepts Lean 4 files with sorry placeholders and runs up to 24h returning only Lean-checked results; a community MCP wrapper exists; Math Inc's Gauss closed 160K lines of sorry in 3 weeks on sphere packing, showing frontier systems excel at exactly 'statement fixed, proof missing' tasks.
- **Prior art.** UW Math AI Lab uses Aristotle to contribute to mathlib4; conjectures.io requires chat logs; JSP pays formalizers separately.
- **What we would build.** A `ctrl outer --aristotle` path that packages a scratch file + imports, submits, polls, and runs the strict axiom audit on returned proofs; log provenance for prize submissions. Pricing and quota are unverified and could kill it.
- **External pull.** Justin Sun Prize / conjectures.io bounties
- **Edge.** lean_tooling → prizes (0.5): Frontier provers raise the odds on 90%-done research formalizations.
- **Evidence.** <https://apis.io/providers/harmonic/> · <https://github.com/gleachkr/aristotle-mcp> · <https://arxiv.org/pdf/2603.15929> · <https://harmonic.fun/news/minif2f/>

### `TOOL-10` SEooC-style verified kernel pack offer: certificates plus parity harness plus retainer

**industrialize** · score 0.118 · 4 wk · confidence 0.30 · payoff 4/5 · domains: codegen_certification, robotics, realtime_systems  
Builds on: `ROBO-01`, `ROBO-02`, `ROBO-03`, `CTRL-01`, `EST-01`.  

- **Why now.** Every FV vendor found sells tool tier + services with quote-only pricing (Certora is the only free tier); Apex.AI proves robotics buyers pay for ASIL-D SEooC artifacts; DARPA SAFRON (2026) asked for formal verification and runtime monitors for foundation-model robots; AWS normalized Lean in production.
- **Prior art.** Apex.Grace (ASIL D), AdaCore SPARK assurance levels, TrustInSoft FVS, Imandra ROS/AV notebooks, VeriPhy; no vendor sells verified controller-math kernels with Lean certificates.
- **What we would build.** A whitepaper and offer sheet: per-kernel pack (Lean source, certificate JSON-LD, C99/ST, DRT harness, MuJoCo evidence), commercial license tiers mirroring Certora (free public tier, premium pack, enterprise retainer), and one pilot conversation with a ROS 2 safety vendor or SAFRON performer.
- **External pull.** DARPA SAFRON performers; ROS 2 safety vendors (Apex.AI-class); unverified Lean FRO industrial program
- **Edge.** certification → robotics (0.5): Packaging proofs as SEooC artifacts is what makes robotics integrators able to buy them.
- **Evidence.** <https://www.certora.com/pricing> · <https://www.apex.ai/apexgrace> · <https://discourse.openrobotics.org/t/ros-2-iso-26262-certification-and-thank-you/19249> · <https://grantedai.com/grants/darpa-safron-safe-assured-foundation-robots-open-environments-foundation-model-safety-darpa-f1a3b5c7> · <https://www.trust-in-soft.com/resources/blogs/2024-08-20-announcing-trustinsoft-formal-verification-services>

### `TOOL-07` Rust kernels translated to Lean with Aeneas/hax and proved equal to the ControlsLean spec

**explore** · score 0.113 · 6 wk · confidence 0.35 · payoff 3/5 · domains: rust_systems, codegen_certification, lean_tooling  
Builds on: `ROBO-02`, `ROBO-04`.  
Unlocks: `TOOL-10`.  

- **Why now.** Aeneas calls Lean its most mature backend; hax added `cargo hax into lean` (Charon+Aeneas, 'Recommended for Lean') with Cryspen announcing Aeneas integration in mid-2026; ROS 2/Apex.AI ecosystems are moving to Rust-adjacent safety stacks.
- **Prior art.** Aeneas used for low-level crypto (HACL* in Rust); hax backends F*, Rocq, Lean, ProVerif; no verified robotics kernels in Rust via Lean found.
- **What we would build.** Pick integer/fixed-point kernels (ZMP allocation, Jury/Hurwitz tests with rational certificates) where Aeneas's safe-Rust subset applies, translate, and prove the translated functions agree with ControlsLean definitions; document that float kernels are out of scope for now.
- **External pull.** community: Aeneas/hax maintainers seek non-crypto case studies
- **Edge.** rust_systems → robotics (0.4): A verified Rust kernel is the artifact ROS 2 safety vendors could consume.
- **Evidence.** <https://github.com/AeneasVerif/aeneas> · <https://github.com/cryspen/hax> · <https://talks.cam.ac.uk/talk/index/232588/> · <https://hax.cryspen.com/blog/archive/2026/>

## Lane SED: sediment and local-first Rust systems

### `SED-04` Reproducible ZIP/TAR creation mode (SOURCE_DATE_EPOCH, sorted, normalized)

**productionize** · score 0.330 · 2 wk · confidence 0.85 · payoff 3/5 · domains: rust_systems  
Builds on: `SED`.  
Unlocks: `SED-05`, `SED-11`.  

- **Why now.** Reproducible-builds practice (SOURCE_DATE_EPOCH, strip-nondeterminism, repro-zipfile/repro-tarfile, Helm 4 reproducible charts) is now expected of release tooling, and sediment's create path still uses wall-clock mtimes and directory-walk order (SimpleFileOptions::default()).
- **Prior art.** repro-zipfile/repro-tarfile (Python), python-stripzip, strip-nondeterminism (Debian), Cargo's own deterministic .crate packaging (no URL); zip2 supports fixed last-modified times and feature-gated compressors.
- **What we would build.** A `--reproducible` flag (and GUI toggle) that sorts entries bytewise, sets mtime from SOURCE_DATE_EPOCH or 1980-01-01, fixes modes to 0644/0755, drops extra fields, forces the UTF-8 flag, uses a fixed deflate level, and a CI test asserting byte-identical output across two hosts; documented as part of the auditability story.
- **External pull.** Standard: reproducible-builds.org SOURCE_DATE_EPOCH convention; release engineers using cargo-dist/GitHub Actions
- **Evidence.** <https://cwiki.apache.org/confluence/spaces/SECURITY/pages/287607354/Reproducible+Builds> · <https://github.com/drivendataorg/repro-tarfile> · <https://pypi.org/project/python-stripzip/0.2.4> · <https://github.com/zip-rs/zip2>

### `SED-07` OpenTelemetry CLI semantic-convention alignment of the JSON trace

**productionize** · score 0.310 · 1 wk · confidence 0.85 · payoff 2/5 · domains: rust_systems  
Builds on: `SED`.  
Unlocks: `SED-01`, `SED-08`.  

- **Why now.** OpenTelemetry now has dedicated 'Semantic conventions for CLI programs' (Release Candidate attributes process.executable.name/process.exit.code/process.pid, Stable error.type) whose privacy posture (do not collect command args by default) matches sediment's no-paths trace, so alignment costs field renames, not architecture.
- **Prior art.** OTel CLI span conventions; Equinix otel-cli v0.4.5 bridges shell output to OTLP; sediment's tracing-subscriber JSON layer with archive_operation span.
- **What we would build.** Emit process.executable.name, process.exit.code, process.pid and a closed-enum error.type (unsafe_path, limit_exceeded, cancelled, destination_exists, format_unsupported, io, changed_during_operation) on the root span; document the NDJSON schema with a version field; keep no exporter in-tree and show the otel-cli pipe recipe.
- **External pull.** Standard: OpenTelemetry semantic conventions (Development status, so early alignment can feed back issues)
- **Evidence.** <https://github.com/open-telemetry/semantic-conventions/blob/main/docs/cli/cli-spans.md> · <https://github.com/packethost/otel-cli> · <https://deploy.equinix.com/labs/otel-cli>

### `SED-02` Archive-hardening regression corpus and named extraction policy

**productionize** · score 0.298 · 2 wk · confidence 0.80 · payoff 3/5 · domains: rust_systems  
Builds on: `SED`.  
Unlocks: `SED-01`, `SED-06`, `SED-10`.  

- **Why now.** Between Mar 2025 and Jun 2026 at least six extractor advisories landed across zip (Rust), tar-rs, mholt/archiver (Go), par2cmdline and libarchive; sediment avoids all of them by construction but has no published, machine-checkable statement of what it rejects, and Python 3.14 just made PEP 706's 'data' filter the default, giving a vocabulary to align with.
- **Prior art.** PEP 706 filters (fully_trusted/tar/data); tar-rs and zip2 advisory test cases; sediment's own unit tests (rejects_traversal_without_publishing, rejects_tar_symlinks, rejects_tar_duplicate_paths, safety_limit_boundaries).
- **What we would build.** A fixtures crate/corpus reproducing each 2025-2026 CVE class (symlink-then-file, symlink-then-dir chmod, PAX size disagreement, PAX desync, dangling-symlink destination, zip64 metadata bomb, overlapping-entry bomb) with cargo-fuzz targets for the PAX reader and EOCD preflight, and a documented 'sediment data filter' policy table comparable to PEP 706.
- **External pull.** Community: contributable as regression fixtures to zip-rs/zip2 and alexcrichton/tar-rs; cited by security reviewers evaluating archive tooling
- **Evidence.** <https://github.com/advisories/GHSA-94vh-gphv-8pm8> · <https://github.com/rustsec/advisory-db/blob/main/crates/tar/RUSTSEC-2026-0068.md> · <https://github.com/alexcrichton/tar-rs/security/advisories> · <https://github.com/Parchive/par2cmdline/security/advisories/GHSA-j5pc-g362-c5xp> · <https://www.sentinelone.com/vulnerability-database/cve-2025-3445/> · <https://github.com/python/peps/blob/main/peps/pep-0706.rst>

### `SED-05` Notarized Homebrew cask and cargo-dist pipeline with sigstore bundles

**industrialize** · score 0.264 · 2 wk · confidence 0.70 · payoff 3/5 · domains: rust_systems, codegen_certification  
Builds on: `SED`.  
Unlocks: `SED-10`.  

- **Why now.** Homebrew 5.0.0 deprecated non-notarized casks with removal from the main tap by Sep 2026, so the only free Mac distribution channel that matters now requires exactly the Developer ID + notarization gate that sediment's 0.1.3 release notes list as still open; cosign sign-blob --bundle has become the one-file way to sign tarballs.
- **Prior art.** Homebrew Acceptable-Casks policy (Gatekeeper must pass; notability required; OSS without compiled distribution rejected); Foundry's release workflow (sha256 + SBOM + cosign + actions/attest) as a reference; sediment's scripts/package-macos.sh and docs/RELEASE_CHECKLIST.md.
- **What we would build.** A hosted CI job producing Developer-ID-signed, notarized, stapled app and CLI artifacts, cosign bundles and sha256, a homebrew tap (own tap first, since main-tap notability is not yet met), and completion of the native acceptance table in USER_JOURNEYS.md.
- **External pull.** Standard/market: Homebrew cask policy and Apple notarization; blocked on a paid Apple Developer account and a real Mac for native acceptance
- **Evidence.** <https://workbrew.com/blog/homebrew-5-0-0> · <https://flaviocopes.com/macos-open-anyway.md> · <https://github.com/Homebrew/brew/blob/main/docs/Acceptable-Casks.md> · <https://github.com/sigstore/docs/blob/main/content/en/cosign/signing/signing_with_blobs.md>

### `SED-06` Read-only zstd, xz, 7z and ZIP-AES support under sediment's limit wrappers

**productionize** · score 0.212 · 3 wk · confidence 0.70 · payoff 3/5 · domains: rust_systems  
Builds on: `SED`.  
Unlocks: `SED-10`.  

- **Why now.** sevenz-rust2 (pure Rust, Apache-2.0, AES read/write) replaced the unmaintained sevenz-rust, zip2 ships zstd/xz/lzma/aes-crypto feature flags, and 7-Zip 26.02's XZ heap overflow (CVE-2026-14266) shows users want a memory-safe reader for exactly these containers.
- **Prior art.** Keka/The Unarchiver/PeaZip/NanaZip cover these formats via p7zip/7-Zip C++ code; Rust: sevenz-rust2, zesven (2026, docs.rs only), lzma-rs (incomplete .xz), zip2 feature flags. RAR stays excluded by CLEAN_ROOM.md and the unRAR license.
- **What we would build.** Format detection and inspect/verify/extract for tar.zst, tar.xz, 7z (read-only) and AES ZIP entries, each routed through SafeZipReader-style byte budgets, MAX_EXPANDED/MAX_RATIO accounting and the same no-links/no-special policy; plus the dependency notices update.
- **External pull.** Community demand: every 2026 Mac archiver roundup lists 7z/multipart as Archive Utility's gap; Keka has 263 open issues largely on format edge cases
- **Evidence.** <https://github.com/hasenbanck/sevenz-rust2> · <https://github.com/zip-rs/zip2> · <https://github.com/gendx/lzma-rs> · <https://7-zip.org/history.txt> · <https://fedoraproject.org/wiki/Licensing:Unrar>

### `SED-08` Kani-proved resource accounting for decompression-bomb limits

**explore** · score 0.206 · 2 wk · confidence 0.65 · payoff 3/5 · domains: rust_systems  
Builds on: `SED`.  
Unlocks: `SED-06`.  

- **Why now.** Kani is now the workhorse of the AWS verify-rust-std program (10/29 challenges resolved, ASE'26 paper) and sediment's budget logic (check_limits, zip_metadata_preflight incl. zip64, SafeZipReader byte budget, drain_padding, MAX_TAR_EXTENSION) is small, integer-only and loop-bounded, which is exactly Kani's sweet spot.
- **Prior art.** verify-rust-std harnesses for numeric primitives/Duration/NonZero; sediment's safety_limit_boundaries unit test; no formal proof of archive budget invariants found.
- **What we would build.** Proof harnesses showing: no arithmetic overflow in check_limits/preflight for all u64 inputs; bytes written by copy_controlled never exceed the announced entry size; cumulative entries/bytes/metadata never exceed MAX_* before an Err; PAX size override is applied consistently (the CVE-2026-33055 class) in sediment's own TAR reader. Run in CI behind a feature.
- **External pull.** Community: verify-rust-std style harnesses are a recognised evidence format; useful collateral for SED-05's security claims
- **Evidence.** <https://github.com/model-checking/kani> · <https://github.com/model-checking/verify-rust-std> · <https://github.com/rustsec/advisory-db/blob/main/crates/tar/RUSTSEC-2026-0068.md>

### `SED-03` Verified GF(2^16) PAR2 recovery-record kernel bridging ctrl Reed-Solomon and ArkLib

**explore** · score 0.198 · 8 wk · confidence 0.55 · payoff 4/5 · domains: rust_systems, math, lean_tooling, codegen_certification  
Builds on: `SED`, `ROBO-04`.  
Unlocks: `SED-11`.  

- **Why now.** par2cmdline shipped two repair-path advisories on 2026-06-10 (dangling-symlink write-outside-base and a heap OOB write from block-count wrap), PAR3 is still unreleased after a 'near-final' 2022 spec, the only pure-Rust crate (rust-par2, created 2026-03) cannot create recovery sets, and ArkLib (Lean) now has RS codes, MDS/distance theorems and a Berlekamp-Welch decoder with correctness theorems to import rather than re-prove.
- **Prior art.** Verified-FEC (Coq/VST/MathComp, CAV 2022) proved an RS *erasure* decoder for C; ArkLib (Lean, Apache-2.0) has ReedSolomon.lean (Vandermonde generator, MDS, unique decoding radius, Lagrange interpolation, no sorry seen) and a noncomputable Berlekamp-Welch decoder with decoder_eq_some/not_exists_of_decoder_eq_none; rust-par2 implements GF(2^16) poly 0x1100B with PSHUFB nibble tables (~15 GB/s AVX2) for verify/repair only; par2cmdline-turbo uses ParPar GF16. ctrl's ROBO-04 Barcode decoder (on origin/backup/20261020/dev-ctrl/snapshot, lean/RoboLean/Barcode/) is error-decoding, likely GF(2^8), so only field/polynomial lemmas transfer.
- **What we would build.** (1) A Lean instance of GF(2^16) with PAR2's primitive polynomial and a proof that the PAR2 Vandermonde recovery matrix restricted to any set of surviving blocks is invertible (erasure-decoding correctness), importing ArkLib's RS statements; (2) a pure-Rust PAR2 *create* + repair kernel whose table arithmetic is refined to the Lean field (Kani for the table layer, Aeneas/hax for the polynomial layer) and whose repair path is dangling-symlink-safe by reusing sediment's create_new staging; (3) `sediment create --recovery N%` and `sediment repair`. Reuse ctrl's theorem-to-C99 codegen pattern for the kernel.
- **External pull.** Community: Parchive org and Usenet/long-term-archiving users (par2cmdline 1.4.0 Sep 2026 still active); 'verified recovery records' is a citable artifact for the Renaissance/XTX AI-for-Math tools track named in ctrl/BOUNTIES.md
- **Edge.** robotics → archive_formats (0.7): ctrl's verified Reed-Solomon field lemmas and theorem-to-C99 codegen pipeline become the proof core of a PAR2 recovery feature; the erasure-decoder correctness is the new part.
- **Evidence.** <https://github.com/Parchive/par2cmdline/security/advisories/GHSA-j5pc-g362-c5xp> · <https://github.com/Parchive/par2cmdline/releases> · <https://github.com/Parchive/par3cmdline> · <https://github.com/AusAgentSmith-org/rust-par2> · <https://crates.io/api/v1/crates/rust-par2> · <https://github.com/animetosho/par2cmdline-turbo> · <https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/Data/CodingTheory/ReedSolomon.lean> · <https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean>

### `SED-01` Lean-checked archive path sanitizer (hax/Aeneas) with Kani harness

**explore** · score 0.198 · 3 wk · confidence 0.60 · payoff 3/5 · domains: rust_systems, lean_tooling  
Builds on: `SED`.  
Unlocks: `SED-02`, `SED-08`, `SED-11`.  

- **Why now.** 2025-2026 produced fresh zip-slip variants in the Rust ecosystem itself (zip CVE-2025-29787 symlink-then-file; tar-rs CVE-2026-33056 chmod via symlink; PAX desync advisories in Mar/May 2026), and hax 0.4 now drives Lean through Charon+Aeneas with on-demand installs, so a Lean theorem about a small pure Rust sanitizer is finally a weeks-scale job rather than a toolchain project.
- **Prior art.** verify-rust-std (AWS) has 29 std challenges, none on std::path; Aeneas has verified crypto (libcrux-class) and a jxl-rs sample; Python PEP 706 'data' filter is the policy benchmark; no Lean-checked archive sanitizer found. sediment's safe_path already exists but uses std::path::Components/PathBuf, which Aeneas/hax do not translate.
- **What we would build.** A pure byte-level sanitize(&[u8]) -> Result<Vec<component>> in sediment, translated to Lean via cargo hax into lean, with theorem: every accepted output is a non-empty list of non-empty, separator-free, non-'..' components (so dest.join(out) stays under dest on a link-free tree); plus a Kani harness over bounded-length names and a proptest differential test against the std-based safe_path.
- **External pull.** Community: zip2/tar-rs maintainers are actively shipping path-safety advisories (GHSA-747h-hw98-c42x informational); a citable verified sanitizer is referenceable by both and by the verify-rust-std effort
- **Edge.** lean_tooling → rust_systems (0.6): ctrl's Audit.lean axiom-audit and escape-hatch ban transfer unchanged to a sediment Lean artifact.
- **Evidence.** <https://github.com/advisories/GHSA-94vh-gphv-8pm8> · <https://github.com/rustsec/advisory-db/blob/main/crates/tar/RUSTSEC-2026-0067.md> · <https://github.com/alexcrichton/tar-rs/security/advisories> · <https://github.com/AeneasVerif/aeneas> · <https://github.com/cryspen/hax> · <https://github.com/model-checking/kani> · <https://github.com/model-checking/verify-rust-std>

### `SED-11` Signed archive manifest and verify-against-manifest for auditable extraction

**productionize** · score 0.154 · 2 wk · confidence 0.60 · payoff 2/5 · domains: rust_systems, codegen_certification  
Builds on: `SED`.  

- **Why now.** Supply-chain practice in 2025-2026 moved to sigstore bundles plus attestations next to release archives (Foundry-style sha256 + SBOM + cosign + actions/attest), yet archive tools themselves still verify only internal CRCs; a manifest of entry names/sizes/hashes that a consumer can pin turns sediment's never-overwrite extraction into an auditable step.
- **Prior art.** cosign sign-blob/verify-blob bundles, SLSA provenance via slsa-verifier (search results only), in-toto attestations (no URL); content-addressed stores (Nix NAR, casync; no URL).
- **What we would build.** `sediment manifest archive.zip` emitting canonical JSON (sorted entries, sizes, BLAKE3/SHA-256 per entry, archive hash) and `sediment extract --manifest m.json` refusing on mismatch; signing left to cosign externally to keep the dependency tree small; pairs with SED-04 so manifests are reproducible.
- **External pull.** Standard: sigstore/SLSA ecosystems; release-engineering users
- **Evidence.** <https://github.com/sigstore/docs/blob/main/content/en/cosign/signing/signing_with_blobs.md> · <https://upd.dev/foundry-rs/foundry/src/branch/master/SECURITY.md> · <https://github.com/zip-rs/zip2>

### `SED-10` Linux/Windows CLI-first ports with egui GUI as beta

**industrialize** · score 0.121 · 3 wk · confidence 0.50 · payoff 2/5 · domains: rust_systems  
Builds on: `SED`.  

- **Why now.** eframe officially supports Web/Linux/Mac/Windows/Android with AccessKit on Windows and macOS, but egui states native look is a non-goal and APIs are still breaking; meanwhile Windows is saturated by free 7-Zip 26.x and NanaZip 6 with hardened MSIX builds, so the credible wedge on other platforms is the JSON/trace CLI, not the GUI.
- **Prior art.** NanaZip (CFG/CET/MSIX, zstd/brotli/lz4), PeaZip 11.4 (Apple Silicon DMG, 7z backend), 7-Zip 26.x; sediment's GUI-free feature set already builds without eframe.
- **What we would build.** Static musl Linux and Windows CLI builds via cargo-dist, Windows-specific path rules (reserved names, ADS already rejected), set_permissions no-op audit on Windows, and a clearly labelled beta GUI; distribution through cargo install and winget/apt later.
- **External pull.** Market: CI/agent users on Linux who want structured archive results; weak against free incumbents on Windows
- **Evidence.** <https://github.com/emilk/egui> · <https://github.com/M2Team/NanaZip> · <https://7-zip.org/history.txt> · <https://github.com/peazip/PeaZip/releases>

### `SED-09` Cancellation-latency bound as measured evidence (RTA cross-link, assessed as a stretch)

**explore** · score 0.077 · 1 wk · confidence 0.30 · payoff 1/5 · domains: realtime_systems, rust_systems  
Builds on: `SED`, `ROBO-04`.  

- **Why now.** sediment already records cancellation phases and durations (scripts/trace-smoke.py, docs/evidence/trace-cancellation-0.1.2.json), so a stated bound (time-to-ack <= one 64 KiB read + one fs call + staging cleanup) can be checked against evidence now; but ctrl's ROBO-04 fixed-priority response-time analysis models periodic task sets, which a single cooperative worker is not.
- **Prior art.** ctrl ROBO-04 RTA (Liu-Layland critical instant, per docs/IDEA_PORTFOLIO_AND_SYNERGIES.md); sediment OperationControl + copy_controlled check-per-buffer design.
- **What we would build.** A one-page doc stating the cancellation latency model and a test asserting the measured p99 against it. No theorem is warranted; information-theoretic bomb detection likewise reduces to the existing ratio policy.
- **External pull.** None identified
- **Edge.** realtime_systems → rust_systems (0.15): Only the vocabulary (deadline, worst-case response) transfers; the scheduling theorems do not apply to a single cooperative worker.
- **Evidence.** <https://github.com/open-telemetry/semantic-conventions/blob/main/docs/cli/cli-spans.md>

## Lane XD: Cross-domain edges (projects that live on a missing edge)

### `XD-06` Lorentz-cone CBF safe set as MPC terminal set with proven recursive feasibility

**explore** · score 0.417 · 4 wk · confidence 0.70 · payoff 4/5 · domains: nonlinear_safety, controls  
Builds on: `NL-02`, `CTRL-04`, `CTRL-03`.  
Unlocks: `CTRL-04`, `NL-02`, `XD-12`.  

- **Why now.** 2025-2026 papers (Maximal Controlled Invariant-MPC, receding-constraint MPC, safety-value-constrained MPC) push CBF terminal constraints for less conservatism; none has a machine-checked recursive-feasibility proof, and the repo already has both the closed-form CBF invariance and the shifted-tail argument.
- **Prior art.** Katriniok-Shakhesi-Heemels DTCBF terminal ingredients; Wabersich-Zeilinger predictive safety filters; system-level-synthesis predictive safety filter; repo MPCFeasibility.lean.
- **What we would build.** Lean theorem: if the terminal set is the forward-invariant sublevel set of the Lorentz-cone CBF (stopping-distance bound a_max=min(mu,W/h_G)g), then the receding-horizon problem is recursively feasible and the safety filter never needs the QP fallback; export `ctrl_mpc_cbf_terminal_check` to C99.
- **External pull.** safety-critical legged/mobile robotics community; publishable at CDC/L-CSS
- **Edge.** nonlinear_safety → controls (0.6): The barrier's invariant set is a larger, closed-form terminal set than the classic LQR ellipsoid.
- **Evidence.** <https://arxiv.org/pdf/2605.05575> · <https://arxiv.org/html/2309.11124v2> · <https://arxiv.org/pdf/2604.23863> · <https://arxiv.org/pdf/2212.02111> · <https://heemels.tue.nl/content/papers/KatSha_CDC23a.pdf>

### `XD-08` Verified information-consensus filter for fleets

**productionize** · score 0.380 · 3 wk · confidence 0.70 · payoff 3/5 · domains: estimation, realtime_systems, robotics  
Builds on: `EST-01`, `ROBO-04`, `EST-03`.  
Unlocks: `EST-03`, `XD-07`.  

- **Why now.** InformationFilter.lean already proves the SMW precision equivalence; 2024-2026 distributed invariant KF and adaptive Kalman-consensus work shows ongoing demand, and nobody has a mechanised proof that information-form fusion of independent measurements is additive and consistent.
- **Prior art.** Casbeer-Beard information consensus filter; Li-Huang-Hu ICF vs KCF comparison; Zhu-Ren fully distributed localisation; UCLA LEMUR covariance intersection. No proof-assistant versions.
- **What we would build.** Lean theorems: additivity of information contributions across agents, equivalence to the centralised Joseph update, and a conservative (covariance-intersection) bound under unknown correlation; `ctrl_info_fusion` C99 kernel and a multi-robot localisation benchmark.
- **External pull.** multi-robot localisation community; AMR vendors
- **Edge.** estimation → realtime_systems (0.4): Information form is the only filter form whose fusion is a sum, which is what communication-limited fleets need.
- **Evidence.** <https://skoge.folk.ntnu.no/prost/proceedings/acc09/data/papers/1107.pdf> · <https://strathprints.strath.ac.uk/47249/> · <https://doaj.org/article/0d550e1e5be04ef9bf459e8b867af6b7> · <https://arxiv.org/pdf/2603.11328> · <https://arxiv.org/abs/2405.04000v1>

### `XD-12` Barrier-derived Simplex switching for learned controllers

**productionize** · score 0.380 · 3 wk · confidence 0.70 · payoff 3/5 · domains: nonlinear_safety, realtime_systems, codegen_certification  
Builds on: `NL-02`, `ROBO-04`, `CTRL-03`.  
Unlocks: `ROBO-04`, `NL-02`.  

- **Why now.** Neural Simplex (reverse switching, online retraining), Black-Box Simplex and Bb-Simplex (barrier-certificate switching, 2025-2026) are the current runtime-assurance pattern for RL controllers; the repo has a Lean-verified barrier and a Simplex theorem but no switching condition derived from the barrier.
- **Prior art.** Sha's Simplex; Phan et al. NSA; Black-Box Simplex (F-16 collision case studies); Bb-Simplex (Taylor-expanded barrier switching for microgrids). No Lean-verified barrier used as the Simplex certificate.
- **What we would build.** Lean theorem: the Lorentz-cone CBF sublevel set is a Simplex recoverable region, the switching condition derived from one-step barrier decrease keeps the learned controller active whenever safe, and reverse switching is sound; `ctrl_simplex_barrier_switch` C99 kernel and MuJoCo quadruped benchmark with an RL policy as the advanced controller.
- **External pull.** runtime assurance for learning-enabled systems (DARPA Assured Autonomy lineage, UL 4600 context)
- **Edge.** nonlinear_safety → realtime_systems (0.6): A closed-form barrier is exactly the certificate that makes Simplex switching cheap and provable.
- **Evidence.** <https://arxiv.org/pdf/1908.00528> · <https://par.nsf.gov/biblio/10686450> · <https://par.nsf.gov/biblio/10483769> · <https://www3.cs.stonybrook.edu/%7Estoller/papers/nfm2020.pdf>

### `XD-10` Syntactic WCET bound of generated C99 kernels fed into RTA

**industrialize** · score 0.375 · 5 wk · confidence 0.60 · payoff 4/5 · domains: codegen_certification, realtime_systems  
Builds on: `ROBO-04`, `NL-02`, `ROBO-01`.  
Unlocks: `ROBO-04`, `XD-01`, `XD-02`.  

- **Why now.** rocq-prosa v0.6 (Oct 2025) makes verified RTA mainstream but takes WCET as an oracle; DO-178C 6.3.4f WCET objectives and tool-qualification pressure (Rapita, AbsInt) make a machine-checked 'kernel -> C_i -> schedulable' chain a differentiator; the repo's kernels are straight-line and zero-heap, the easy case.
- **Prior art.** Prosa abstract RTA (Bozhko-Brandenburg), RT-CertiKOS+Prosa (CAV19), Velus/CompCert verified Lustre-to-C, AbsInt aiT and Rapita RapiTime (qualified tools). None links a theorem-prover codegen's output structure to the C_i used by a verified RTA.
- **What we would build.** A Lean-side cost model over the codegen AST (op count, no loops/heap) yielding a per-kernel instruction-count bound, a theorem that the bound is monotone under the kernel composition used in the quadruped shield, and a response_time_analysis instance consuming those bounds; produce a DO-178C-style evidence bundle (bound, measurement on target, qualification narrative).
- **External pull.** certification bodies (DO-178C, IEC 61508/61131-3 PLC users); potential paying customers in PLC/robotics safety
- **Edge.** codegen → realtime_systems (0.7): RTA has no input without C_i, and zero-heap straight-line codegen is the one case where C_i can be proved rather than measured.
- **Evidence.** <https://rocq-prover.org/p/rocq-prosa> · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECRTS.2020.22> · <https://cs.yale.edu/flint/certikos/publications/cav19.pdf> · <https://www.rapitasystems.com/files/MC-WP-004%20Automating%20WCET%20analysis%20for%20DO-178C_3.pdf> · <https://www.absint.com/tum_absint.pdf> · <https://compcert.org/research.html>

### `XD-05` Basis-function ILC over the septic trajectory family

**productionize** · score 0.360 · 3 wk · confidence 0.70 · payoff 3/5 · domains: controls, robotics, codegen_certification  
Builds on: `CTRL-04`, `ROBO-01`, `NL-03`.  
Unlocks: `ROBO-01`.  

- **Why now.** Oomen-group basis-function ILC (2023-2025: rational bases, sparse basis selection, combined time-domain criterion) is the state of the art for task-flexible ILC; the septic family with eta as a parameter is a natural one-parameter basis nobody has used.
- **Prior art.** Norm-optimal and basis-function ILC (van Zundert, Oomen); minimum-jerk / minimum-time-jerk planners (Gasparetto-Zanotto); the repo's IterativeLearning.lean contraction \|\|I-GL\|\|<1.
- **What we would build.** Lean theorem that Arimoto contraction is preserved when the learned feedforward is restricted to the span of septic basis functions (projection does not increase the contraction constant), a `ctrl_ilc_septic_update` C99 kernel, and a MuJoCo repetitive pick-and-place benchmark reporting iteration-to-iteration error and Joule loss.
- **External pull.** industrial motion-control community (printers, wafer stages) that uses basis-function ILC
- **Edge.** controls → robotics (0.7): ILC turns the one-shot septic reference into a learned, repetition-robust feedforward.
- **Evidence.** <https://research.tue.nl/en/publications/combined-time-domain-optimization-design-for-task-flexible-and-hi/> · <https://export.arxiv.org/pdf/2505.05835> · <https://research.tue.nl/en/studentTheses/iterative-learning-control-with-a-rational-feedforward-basis/> · <https://arxiv.org/pdf/2102.07459>

### `XD-01` Pinwheel scheduling as Erdős covering systems in Lean

**explore** · score 0.358 · 4 wk · confidence 0.75 · payoff 4/5 · domains: math, realtime_systems  
Builds on: `MATH-03`, `ROBO-04`.  
Unlocks: `MATH-04`, `XD-10`.  

- **Why now.** Kawamura settled the 5/6 pinwheel density conjecture (STOC'24) and 2025-2026 papers (ISAAC 2025, Finite Pinwheel Covering, Dense Pinwheel Packing strongly NP-complete, Kleinberg-Mishra FOCS 2026) explicitly identify exact pinwheel covering with Erdős covering systems; none is mechanised.
- **Prior art.** Kawamura STOC'24 proof (computer search, fractional periods); Mishra-Rho-Kleinberg 0.84 bound for m=4; a standalone Lean 4 formalisation of the odd covering conjecture argument with 3 axioms exists on erdosproblems.com forum; Prosa/Rocq covers RTA, not pinwheel. No proof-assistant statement of 'exact pinwheel covering <-> covering system'.
- **What we would build.** Lean definitions of pinwheel instance/schedule, theorem that an exact pinwheel cover of periods a_1..a_n is a covering system {r_i mod a_i} and conversely, reuse of CoveringCRT density product to certify (un)schedulability of concrete instances, and the density<=1 necessary condition as a corollary of covering mass.
- **External pull.** community: erdosproblems.com #273 thread and the active 2025-2026 pinwheel complexity literature; real-time scheduling community (ECRTS/RTSS) for mechanised periodic-task results
- **Edge.** math → realtime_systems (0.7): The CRT density engine built for Erdős #273 is literally an exact-pinwheel feasibility engine.
- **Evidence.** <https://drops.dagstuhl.de/storage/00lipics/lipics-vol359-isaac2025/html/LIPIcs.ISAAC.2025.47/LIPIcs.ISAAC.2025.47.html> · <https://arxiv.org/pdf/2607.28574> · <https://arxiv.org/pdf/2609.20075> · <https://www.kurims.kyoto-u.ac.jp/~kawamura/pinwheel> · <https://arxiv.org/pdf/2508.18422>

### `XD-07` Small-gain string stability for robot fleets

**explore** · score 0.348 · 3 wk · confidence 0.65 · payoff 3/5 · domains: controls, realtime_systems, robotics  
Builds on: `CTRL-03`, `ROBO-04`.  
Unlocks: `ROBO-04`, `XD-08`.  

- **Why now.** Besselink-Johansson's ISS+gain<1 string-stability test and 2024-2025 stochastic/packet-loss platoon results are directly reusable; FleetThroughput.lean has the graph side and SmallGain.lean the gain side but they are not connected.
- **Prior art.** Swaroop-Hedrick 1996, Seiler et al. 2004, Ploeg et al. 2014 Lp string stability, Besselink-Johansson 2017, Dashkovskiy-Rueffer-Wirth network small-gain; no Lean/Coq formalisation found.
- **What we would build.** Lean theorem: for a chain (or DAG) of ISS subsystems built from the Peter-Paul ISS envelope, predecessor-to-follower gain < 1 implies a uniform-in-N disturbance bound (disturbance string stability), composed with the deadlock-free routing graph of FleetDeadlock.lean; Python fleet simulation benchmark.
- **External pull.** warehouse/AMR fleet vendors and platooning standards (ISO 22737 context)
- **Edge.** controls → realtime_systems (0.5): The ISS gain envelope is what makes fleet-level throughput guarantees robust to per-robot disturbances.
- **Evidence.** <https://arxiv.org/pdf/1702.01031> · <https://arxiv.org/pdf/2403.11043> · <https://arxiv.org/pdf/2511.08027> · <https://dept.aem.umn.edu/~SeilerControl/Papers/2004/SeilerEtAl_04TAC_DisturbancePropagationInStrings.pdf> · <https://arxiv.org/pdf/2312.06472>

### `XD-03` Byers-Nash sep bound to certified Riccati/Kalman condition numbers

**explore** · score 0.319 · 4 wk · confidence 0.60 · payoff 3/5 · domains: math, estimation, controls  
Builds on: `MATH-01`, `EST-02`, `CTRL-01`, `EST-01`.  
Unlocks: `EST-01`, `CTRL-01`.  

- **Why now.** MATH-01 is at 90% with lyapunov_singular_value_robustness_bound already proved; 2025-2026 work on structured Riccati condition numbers and Sylvester conditioning (arXiv 2609.04050) keeps sep-based bounds current; no proof assistant has a Riccati condition-number theorem.
- **Prior art.** Kenney-Hewer SIAM JCO 1990 (Riccati sensitivity), Gahinet-Laub-Kenney-Hewer (discrete Lyapunov), Sun (Rice condition numbers for CARE/DARE), Diao-Qiao structured condition numbers, SLICOT SB02RD condition estimates; Byers-Nash 1985 report on symmetric minimisers of sep.
- **What we would build.** Lean theorem: first-order DARE/CARE perturbation bound \|\|dP\|\|_F <= kappa * \|\|dA\|\|_F with kappa expressed through sep of the closed-loop Lyapunov operator, and a corollary that under Byers-Nash the symmetric-cone sep suffices; plus a runtime `riccati_condition_estimate` kernel in estimation_lqr.py bound via @lean_theorem.
- **External pull.** community: numerical linear algebra / SLICOT users; certification bodies want numerical-robustness evidence for filters
- **Edge.** math → estimation (0.6): sep(A) on the symmetric cone is the quantity that bounds Kalman DARE sensitivity.
- **Evidence.** <https://arxiv.org/pdf/1601.03787> · <https://arxiv.org/pdf/1803.04046> · <https://arxiv.org/pdf/2609.04050> · <https://www3.math.tu-berlin.de/Vorlesungen/SoSe11/Kontrolltheorie/uebung4.pdf> · <https://fox.cs.vt.edu/VAD1/DOWN/BIB/R/HPKINMSD>

### `XD-09` Homography ground plane to tilted ZMP/CBF deceleration bound

**explore** · score 0.292 · 4 wk · confidence 0.55 · payoff 3/5 · domains: vision, nonlinear_safety, robotics  
Builds on: `VIS-01`, `NL-02`, `ROBO-03`.  
Unlocks: `NL-02`.  

- **Why now.** Perceptive legged locomotion (2025-2026 MIQP on depth-derived steppable regions) now estimates terrain planes online, but the safety bound is always re-solved numerically; the repo's closed-form bound assumes a flat ground and the 4-point homography uniqueness gives the plane normal for free.
- **Prior art.** Ground-plane homography (Hartley-Zisserman style), Dragon-Van Gool CVPR14, Fallon et al. Atlas 2015 planar segmentation, 2026 perceptive MIQP footstep planning; none derives a closed-form inclined-plane deceleration/ZMP bound from a homography.
- **What we would build.** Lean theorem: given the plane normal n from homography decomposition (HomographyDecomposition.lean), the safe deceleration bound becomes a_max(theta)=min(mu cos theta - sin theta, (W/h_G)cos theta - ...)g on a slope, with forward invariance of the corresponding Lorentz-cone CBF; MuJoCo quadruped-on-ramp benchmark with a camera.
- **External pull.** legged-robot vendors (perceptive locomotion); no bounty
- **Edge.** vision → nonlinear_safety (0.5): The homography's plane normal is the one scalar the closed-form ZMP bound is missing on non-flat ground.
- **Evidence.** <https://www.doc.ic.ac.uk/~ajd/Robotics/RoboticsResources/lecture7.pdf> · <https://openaccess.thecvf.com/content_cvpr_2014/papers/Dragon_Ground_Plane_Estimation_2014_CVPR_paper.pdf> · <https://groups.csail.mit.edu/robotics-center/public_papers/Fallon15.pdf> · <https://arxiv.org/pdf/2603.07400> · <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC4431242/>

### `XD-02` Verified PAR2-style recovery records for sediment

**productionize** · score 0.265 · 5 wk · confidence 0.70 · payoff 3/5 · domains: rust_systems, math, codegen_certification  
Builds on: `ROBO-04`, `SED`.  
Unlocks: `XD-10`.  

- **Why now.** sediment 0.1.3 lists recovery records as unsupported; pure-Rust PAR2 crates (rust-par2, par2-rs) now exist for interop testing; ArkLib (2026) shows Lean RS verification is tractable, and the lean-zip OOM bug (2025) showed verified codecs with unverified archive layers still fail.
- **Prior art.** Cohen-Wang-Appel (Coq/VST+MathComp) verified a different RS FEC C implementation; Affeldt-Garrigue-Saikawa Coq ECC library; ArkLib Lean RS list decoding for ZK; rust-par2 and par2-rs (unverified). PAR2 spec itself notes Plank's sequential-constant construction is wrong.
- **What we would build.** Lean theorem over GF(2^16) that the PAR2 constant choice (powers of 2 of multiplicative order 65535, recovery exponents) yields an invertible recovery matrix for any erasure pattern with #missing <= #recovery, plus an erasure-decoding kernel extracted via the existing C99 codegen (or Rust port with Kani harness) and wired into sediment's `test`/`extract` with its JSON trace model.
- **External pull.** product gap: sediment README/CLEAN_ROOM.md list recovery records as unsupported; archive-utility users expect PAR2 parity
- **Edge.** math → rust_systems (0.5): A crisp finite-field invertibility theorem is the missing certificate behind every PAR2 repair.
- **Evidence.** <https://parchive.sourceforge.net/docs/specifications/parity-volume-spec/article-spec.html> · <https://docs.rs/crate/rust-par2/latest> · <https://docs.rs/par2-rs> · <https://www.cs.princeton.edu/~jmc16/docs/FECVerification.pdf> · <https://staff.aist.go.jp/reynald.affeldt/documents/ecc.pdf> · <https://eprint.iacr.org/2026/2056> · <https://kirancodes.me/posts/log-who-watches-the-watchers.html>

### `XD-04` Occlusion-aware log-depth visual servoing via POMDP belief

**explore** · score 0.244 · 6 wk · confidence 0.50 · payoff 3/5 · domains: estimation, vision, robotics  
Builds on: `EST-03`, `ROBO-02`, `VIS-01`.  
Unlocks: `ROBO-02`.  

- **Why now.** Perception-based POMDP beliefs from camera observations (2026) and active target tracking under occlusion (Kim-Sentis) are active, but no work combines belief-space planning with a provably retreat-free servoing law; both halves are READY in the repo.
- **Prior art.** Kim-Sentis DBN/particle-filter active tracking with POMDP formulation; Shi et al. 2018 adaptive IBVS with temporary signal loss; Radmard et al. 2018 occlusion resolution; Schaefers et al. 2026 perception-based beliefs. None has formal guarantees.
- **What we would build.** Lean model: finite-state occlusion POMDP whose actions are servo-rate choices; theorem that under the PWLC value backup the expected log-depth error is non-increasing and the lower bound d(t) >= d* + (d0-d*)e^{-lambda t} persists in expectation across occlusion episodes; MuJoCo SE(3) benchmark with intermittent target loss.
- **External pull.** community demand in active perception / manipulation under occlusion; no bounty
- **Edge.** estimation → vision (0.7): POMDP belief planning is the standard formalism for deciding what to look at when the target is occluded.
- **Evidence.** <https://arxiv.org/pdf/1912.06754v1> · <https://arxiv.org/html/2602.05679v1> · <https://ifaamas.org/Proceedings/aamas2026/pdfs/XUFR9329.pdf>

### `XD-11` Cross-ratio fiducial detection with Reed-Solomon coded identity

**explore** · score 0.189 · 4 wk · confidence 0.50 · payoff 2/5 · domains: vision, realtime_systems, robotics  
Builds on: `VIS-01`, `ROBO-04`.  
Unlocks: `ROBO-04`.  

- **Why now.** Learned tag families (E2ETag) and projective-invariant tags (Pi-Tag, X-tag) coexist with AprilTag's Hamming-table decoding; a verified pipeline that uses the cross-ratio for detection and an RS code for ID has no formal counterpart and reuses two READY modules.
- **Prior art.** Pi-Tag (Bergamasco et al. 2011, cross-ratio detection), X-tag (Birdal 2016), AprilTag 2 (code tables), RUNE-tag; cross-ratio known to be noise-sensitive so only a few configurations are distinguishable.
- **What we would build.** Lean theorem that cross-ratio invariance (CrossRatio.lean) plus an RS(n,k) code on the bit pattern gives a decoding with provable false-positive bound given the known cross-ratio noise sensitivity; Python/C99 decoder; honest benchmark against AprilTag on synthetic perspective views.
- **External pull.** weak: AprilTag dominates; niche interest in projective-invariant markers
- **Edge.** vision → realtime_systems (0.4): Projective invariants supply the geometry, RS codes the identity; the pair is the fiducial.
- **Evidence.** <https://www.dsi.unive.it/~atorsell/papers/Conferences/3dimpvt2011-tag.pdf> · <https://campar.in.tum.de/pub/tbirdal20163dv/tbirdal20163dv.pdf> · <https://april.eecs.umich.edu/pdfs/wang2016iros.pdf> · <https://arxiv.org/pdf/2105.14184>

## Appendix: domain unlock edges

| from | to | weight | why |
| --- | --- | ---: | --- |
| controls | estimation | 0.9 | DARE/Kalman duality already proven in repo (CTRL-01 <-> EST-01). |
| math | prizes | 0.9 | Solved-but-unformalized Erdős problems are the direct money lane. |
| controls | nonlinear_safety | 0.8 | DARE terminal cost, shifted-tail feasibility and ISS sublevel invariants are the terminal/switching ingredients predictive safety filters and CBF shields need. |
| estimation | robotics | 0.8 | Quaternion error-state KF is the standard IMU attitude estimator and POMDP belief planning is the standard formalism for active perception. |
| nonlinear_safety | robotics | 0.8 | Lorentz-cone CBF and ZMP allocator are the legged-robot safety layer (in repo). |
| realtime_systems | codegen_certification | 0.8 | RTA consumes WCET; DO-178C 6.3.4f recommends WCET determination with qualified tools, and Prosa/Rocq is the verified-RTA prior art. |
| vision | robotics | 0.8 | Ground-plane homography is the standard single-matrix camera-to-ground model and planar-region extraction feeds footstep planners. |
| lean_tooling | prizes | 0.7 | Prize eligibility and formalizer attribution both require an earliest public commit. |
| codegen_certification | realtime_systems | 0.7 | Straight-line zero-heap C99 admits a syntactic WCET bound; without C_i the RTA theorem has no input. |
| controls | robotics | 0.7 | ILC contraction on a parametrised septic reference family is basis-function ILC for task flexibility. |
| estimation | vision | 0.7 | Kalman pose filtering of homography measurements and POMDP observation models for occluded targets. |
| lean_tooling | math | 0.7 | Triage and proof automation are what make the Erdős bounty pipeline cheap. |
| math | realtime_systems | 0.7 | CoveringCRT exact density products and prime sieves compute exactly what decides exact pinwheel covering/packing feasibility. |
| realtime_systems | math | 0.7 | Exact pinwheel covering is an Erdos covering system; Kawamura's 5/6 density theorem is a covering-density schedulability statement, giving MATH-03 an applied audience and new finite instances. |
| estimation | controls | 0.6 | Kalman innovation null space (EST-01) is exactly the stochastic DeePC constraint subspace. |
| codegen_certification | robotics | 0.6 | MuJoCo/C99 parity feeds benchmark evidence back (in repo). |
| controls | codegen_certification | 0.6 | Closed-form (solver-free) kernels are what makes a control loop WCET-analysable for certification. |
| lean_tooling | controls | 0.6 | Tactics, Loogle search and the inner loop lower the cost of every new module. |
| math | controls | 0.6 | Byers-Nash k(A)<=s(A) makes sep checkable on the symmetric cone; sep governs Lyapunov and first-order Riccati conditioning. |
| math | estimation | 0.6 | Same sep-based conditioning applies to the Kalman DARE/CARE and the discrete Lyapunov equation. |
| math | vision | 0.6 | Exact rational PSD certificates developed for an open matrix inequality become proof-carrying perception outputs. |
| nonlinear_safety | controls | 0.6 | A CBF-defined terminal set gives MPC recursive feasibility with a larger feasible region than classic invariant sets. |
| nonlinear_safety | realtime_systems | 0.6 | Simplex decision modules derive cheap switching conditions from a barrier certificate (Bb-Simplex); NL-02's closed-form barrier is that certificate. |
| robotics | codegen_certification | 0.6 | Septic/IK kernels already generated to C99. |
| robotics | estimation | 0.6 | SO(3)/quaternion kinematics and non-inertial transport are the manifold and process model of the ESKF. |
| robotics | nonlinear_safety | 0.6 | SE(3) kinematics feed the centroidal CBF (in repo). |
| vision | estimation | 0.6 | Multi-view measurement models for filters. |
| nonlinear_safety | lean_tooling | 0.5 | Turns ctrl's CBF theorems into the consumer of TorchLean's bound certificates. |
| codegen_certification | prizes | 0.5 | A verified kernel pipeline is grant-shaped (AI for Math Fund tools track, DARPA formal methods programs). |
| nonlinear_safety | codegen_certification | 0.5 | Sub-100ns zero-heap safety filters are the certifiable artefact for DO-178C-style timing evidence. |
| realtime_systems | controls | 0.5 | RTA guarantees the sampling-period assumption of every discrete-time theorem. |
| realtime_systems | nonlinear_safety | 0.5 | Simplex is a real-time architecture (in repo). |
| realtime_systems | robotics | 0.5 | Fleet deadlock (in repo). |
| realtime_systems | rust_systems | 0.5 | Reed-Solomon decoding and deadline-bounded cancellation transfer to archive recovery records and cooperative cancellation. |
| robotics | realtime_systems | 0.5 | Fleet deadlock/throughput and 1 kHz loop deadlines (in repo). |
| robotics | vision | 0.5 | SE(3) log-depth servoing (in repo). |
| vision | nonlinear_safety | 0.5 | A camera-estimated terrain plane changes the support polygon and ZMP constraint; literature couples vision to steppable regions under ZMP/DCM constraints but not to the closed-form deceleration bound. |
| controls | vision | 0.5 | Coordinate-free observability from CTRL-05 turns a VIO folklore result into a theorem. |
| math | robotics | 0.5 | Mathlib spectral graph theory becomes a multi-robot convergence certificate. |
| lean_tooling | codegen_certification | 0.4 | Turns the axiom audit into a sellable, re-checkable artifact. |
| codegen_certification | controls | 0.4 | Benchmark feedback loop (in repo). |
| controls | realtime_systems | 0.4 | ISS/small-gain envelopes quantify the disturbance budget that timing jitter and deadline misses consume; adjacent literature only. |
| estimation | codegen_certification | 0.4 | A machine-checked covariance update is the kind of evidence ISO 26262 tool-qualification arguments lack for BMS software. |
| estimation | realtime_systems | 0.4 | Information-consensus filters are the distributed-estimation primitive for robot/sensor networks. |
| lean_tooling | rust_systems | 0.4 | Aeneas/Verus-style pipelines let the Lean verification habit reach the Rust archive engine. |
| prizes | lean_tooling | 0.4 | Prize rules (standard axioms, public SHA pinning) shape the tooling. |
| vision | realtime_systems | 0.4 | Projective-invariant fiducials (Pi-Tag, X-tag) use cross-ratios for detection; AprilTag decodes by Hamming code tables, so the unlock is cross-ratio geometry plus an RS-coded ID. |
| robotics | rust_systems | 0.4 | ctrl's verified Reed-Solomon field lemmas and theorem-to-C99 codegen pipeline become the proof core of a PAR2 recovery feature; the erasure-decoder correctness is the new part. |
| controls | lean_tooling | 0.4 | ctrl's corpus is the out-of-distribution test the prover community lacks. |
| math | rust_systems | 0.3 | A crisp finite-field invertibility theorem is the missing certificate behind every PAR2 repair. |
| estimation | nonlinear_safety | 0.3 | Kalman covariance feeds the probabilistic reachable set used to tighten CBF/MPC constraints. |
| codegen_certification | estimation | 0.3 | Exact-Q vs float parity for filters. |
| codegen_certification | nonlinear_safety | 0.3 | Closed-form safety filters already emitted. |
| controls | math | 0.3 | Riccati sensitivity reduces to a Lyapunov equation whose conditioning is sep-governed, motivating Byers-Nash. |
| estimation | math | 0.3 | Kalman/Riccati numerical conditioning pulls on sep(A). |
| math | codegen_certification | 0.3 | Exact rational LDL^T certificates are the evidence pattern for certification. |
| realtime_systems | estimation | 0.3 | Event-triggered / communication-limited information filters. |
| rust_systems | codegen_certification | 0.3 | A hardened, auditable extraction engine is a small worked example of shipping a verified artifact. |
| rust_systems | lean_tooling | 0.2 | One structured index feeds both web crawlers and MCP clients. |
| codegen_certification | vision | 0.2 | Weak. |
| math | nonlinear_safety | 0.2 | Conic duality is algebra; weak. |
| vision | math | 0.2 | Projective geometry draws on algebraic invariants; weak. |
| prizes | codegen_certification | 0.1 | Grant money is the only realistic way to fund the 8-week float-bound work that certification bodies will demand. |
| rust_systems | robotics | 0.1 | A verified Rust kernel is the artifact ROS 2 safety vendors could consume. |
| codegen_certification | math | 0.1 | Weak. |
| math | lean_tooling | 0.1 | Extremal-graph and interpolation proofs stress finite-combinatorics automation reusable elsewhere. |

