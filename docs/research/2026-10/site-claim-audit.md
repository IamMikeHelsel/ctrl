# Site claim audit — 21 October 2026

The homepage now presents a research notebook: model statements, executable checks, simulations,
and hardware measurements are separate kinds of evidence. The source supports useful small
examples. It does not support a general claim of verified deployed controllers, hardware safety,
or measured superiority over optimized solvers.

This is an AI-assisted source audit and editorial correction. It is not a fresh audit of every
Lean declaration or a system safety assessment. No approved challenge, runtime code, Git history,
repository visibility, or live deployment was changed by this audit.

## Scope and deployment

- Examined local branch `crossover-research-2026-10-19`, based on
  `96f083c36bda20afb818c5183d19fbefbbd473de`. The checkout has substantial pre-existing modified and
  untracked work, including research modules. The base commit is **not** a complete snapshot of
  the files inspected.
- `gh repo view` reports `IamMikeHelsel/ctrl` is **PRIVATE**, with default branch `main`.
- `gh api repos/IamMikeHelsel/ctrl/pages` reports a built, public GitHub Pages site at
  <https://iammikehelsel.github.io/ctrl/>, using the `site` branch at `/` with legacy branch-based
  publishing. HTTPS is enforced; there is no custom domain. No `.github/` workflow directory
  exists in this checkout.
- The working site's sources are under `site/`. Editing these files in the research branch does
  not update the deployed `site` branch. Publication is a distinct subsequent action.
- Parent work adds the literature matrix, staged plan, and latency/braking case study. This audit
  owns the homepage, shared stylesheet, public legacy catalog retirement, and this note.

## Findings

| Claim in the previous homepage | Source evidence and limitation | Homepage treatment |
| --- | --- | --- |
| The theorem registry verifies the implementation's binding to Lean | [`registry.py`](../../../src/ctrl/robotics/registry.py), `audit_lean_file` and `verify_lean_bindings`, strip comments and strings, use a declaration-name regular expression (including definitions and short names), and check selected tokens. They do not invoke Lean, analyze a Python AST, check semantic equivalence, or inspect transitive axioms. | Call this a declaration-name/source check. Explicitly distinguish it from a formal refinement proof. |
| All functions run in exact rational and float modes | Some arithmetic routines accept `Fraction`; matrix and simulation paths use NumPy and floating-point computations. Selected exact examples in [`test_ctrl_robotics_lib.py`](../../../tests/test_ctrl_robotics_lib.py) cannot establish exact semantics for every public function or input. | Describe exact rational examples and numerical tests with their limited scope. |
| Randomized C checks establish `8.88e-16` / “1 ULP” parity | [`codegen.py`](../../../src/ctrl/robotics/codegen.py), `compile_and_verify_c99_kernels`, uses fixed parameter samples and maximum absolute error. Its returned criterion is `< 1e-12`; the wrapper test additionally requires `< 1e-13`. Absolute error is not a ULP bound across arbitrary scales. The harness compiles C; Structured Text is emitted and checked for expected text, not compiled in a PLC runtime. | Remove universal precision claims. Describe finite differential checks. |
| `<100 ns`, `100–1000×` faster, ready for `1–10 kHz`, no loops or solver failure states | The C harness has no timing measurement. The generated C has bounded loops. The site did not identify hardware, timing distribution, compiler/PLC runtime evidence, or a matched QP/SOCP measurement. The contact filter returns a fallback even when its hypotheses do not hold. | Remove timing, deployment-rate, and solver superiority claims. Retain generated code as an implementation artifact. |
| A single `a_max = min(μ, W/hG) g` proves the displayed general two-axis contact theorem | [`LorentzConeCBF.lean`](../../../lean/Research/LorentzConeCBF.lean), `quad_contact_in_lorentz_cone`, requires separate x/y support bounds and a friction-disk bound, as well as corner signs. Its structure is `CentroidalQuadParams`, not the homepage's `QuadParams`; the displayed theorem signatures were not exact copies. | Replace illustrative Lean signatures with the actual three acceleration obligations and describe the rectangular-stance model. |
| The continuous-time proof transfers directly to the displayed sampled braking simulation | `centroidal_cbf_forward_invariant` requires trajectory derivatives and a **nonnegative barrier derivative at every time**. [`run_quadruped_zmp_cbf_benchmark`](../../../src/ctrl/robotics/mujoco_benchmarks.py) uses a sampled condition corresponding to `hdot >= -alpha * h`, clips `b_req`, and uses velocity thresholds. These are distinct obligations. The interpolation theorem also assumes both endpoints lie in the cone, a strictly better backup barrier value, and sufficient backup margin. | Do not describe the simulation as an implementation of a proved closed-loop safety theorem. Preserve this mismatch as follow-up work. |
| A four-foot physical quadruped is validated in MuJoCo | `QUAD_TRUNK_MJCF` has a free trunk and contact marker sites, with no articulated legs, floor-contact dynamics, or actuator model. The rollout applies summed forces and torques directly through `qfrc_applied`. There is no QP/SOCP comparison. Max position and barrier minima are computed from decimated history rather than every integration point. | Label it a rigid-body/net-wrench demonstration and identify missing physical tests. |
| The `39–40%` error reduction isolates the benefit of Sontag control against identical gains | The disturbance benchmark uses auxiliary damping `-12*z2` in the CTC branch and `-(1/0.20²)*z2 = -25*z2` in the other branch, plus a Sontag term. The backstepping expression also includes `-x1`; its effective position coefficient with `c1=16,c2=26` is 417, while CTC uses 416. No matched-effort tuning study, noise/saturation sweep, or Sontag ablation is present. | Remove the causal attribution and general improvement range. Require matched constraints, tuning, effort, and ablations before a comparative write-up. |
| `certified_gamma=0.20` and an ISS “certificate” establish the nonlinear arm's bound | The benchmark names the scalar `certified_gamma`, evaluates an empirical finite-rollout ratio, and uses `0.025 * w_peak_sq` as a sublevel threshold. No derivation of these constants for that nonlinear closed loop is supplied by that function. A Python variable or boolean named “certified”/“verified” is not a certificate. | Do not repeat certificate terminology for the rollout. Require a model-to-theorem mapping and certificate artifact. |
| The vision benchmark compares log-depth HBVS and a full IBVS controller | `run_se3_visual_servoing_benchmark` directly sets camera velocity using **linear** depth feedback `-lam*(z-d_star)`. Its IBVS curve is an analytic expression, not a second image-feedback simulation. There is no image formation, feature matching, calibration error, or depth-estimation pipeline. Its boolean checks range containment, not monotonicity at every step. | Present geometry/vision as a research direction; remove the claimed log-depth implementation and broad no-retreat result. |
| Energy percentages are expected improvement ranges with a known Coriolis explanation | The arm comparison uses one model, target, duration, and controller. It computes torque-based Joule proxies using fixed electrical constants; “dynamic” and “total” are different quantities. The elementary integral reduction and one simulation outcome do not form an uncertainty interval. No mechanism ablation isolates the claimed Coriolis contribution. | Remove the general gain range and causal explanation. Retain energy, torque, error, and duration as future metrics. |
| Static counts and “Ready to Use / A3 / N3” identify public release readiness and novelty | The original `site/AGENT_IDEA_INDEX.json` mixed dated counts, production-readiness labels, novelty assertions, and work across branches. Presence of a runtime routine or passing simulation does not establish either readiness or novelty. | Remove these badges/counts from the homepage. Replace the public JSON with an explicit deprecation notice pointing to the sourced research matrix. |

## What the homepage retains

The site retains the existing restrained teal palette, light/dark appearance, and emphasis on
control, estimation, geometry, and robotics. It now provides:

- A literature-matrix entry point and a specific latency/braking study, with a staged-plan link.
- An evidence table from hypothesis through hardware, with the scope of each kind of evidence.
- A contact-force example that names the model and its actual support/friction obligations.
- Six research areas, each with possible use, measurement criteria, and an explicit open limit.
- A standard for comparative write-ups: matched baselines, raw artifacts, uncertainty, and failures.
- An AI-use disclosure and a clear note that source access is currently restricted.
- A link to the parent-generated Manim study animation, distinguished from experimental evidence.

The HTML contains the content without JavaScript. The shared stylesheet adds a skip link, visible
keyboard focus, semantic table headers/caption, a keyboard-focusable overflow region, fluid card
widths, reduced-motion handling, and a print view. No third-party scripts, analytics, or fonts are
required.

## Public catalog compatibility change

`site/AGENT_IDEA_INDEX.json` is retained at its existing URL as a **schema 2.0.0 deprecation
notice**. It points consumers to `research.json` (schema 1, `records`) and explicitly states that
the former readiness/novelty labels are not current evidence. This is a breaking schema change:
`summary`, `rating_scales`, and `ideas` are absent. Consumers must explicitly migrate; an empty
`ideas` list would misleadingly resemble a successful refresh.

The original site's bytes exactly matched the already tracked `docs/AGENT_IDEA_INDEX.json`
(SHA-256 `fbbc2e27211ff3722b75c4d2a32b212349e125796b88567087d26bfd8b7a1715`). That historical
document is preserved unchanged, so no duplicate archive was created. It remains unreviewed
historical material. The deprecation record's replacement path, schema version, and record key
were checked against the new local matrix. The live endpoint changes only after publication.

## Checks and remaining publication work

Source-level checks on the homepage passed: balanced tag nesting, unique IDs, one `h1`, and all
same-page anchors resolved. At this audit checkpoint the new `research.html` and
`studies/latency-braking.html` were still being generated by the parent; integrated link/browser
checks belong to the final combined preview. The parent subsequently supplied the rendered MP4
at `site/assets/research/latency-braking.mp4` and requested the corrected homepage link.

The declared text colors were checked against the three principal surface colors: the minimum
contrast ratio was **5.70:1 in light mode** and **7.83:1 in dark mode**. This is a palette check,
not a complete accessibility certification. `git diff --check` passed for the homepage/style
changes. The new matrix was then checked: its 17 rows, 17 source cards, and 17 JSON records agree;
IDs are unique and same-page links resolve. Its source claims are distinguished from proposed
transfers and explicitly limited to the passages inspected.

The delayed-braking page was also read against the Python, Lean, results, and animation-source
snapshots. Its formula, counts, example, and proof limitations agree. All five listed braking
snapshots matched both their manifest hashes and their current source files at review time.
An interactive floating-point equality issue was reported to the parent for correction; the
exact-rational experiment is unaffected. The transport snapshot was still being finalized and
was flagged for a final source/hash refresh.

Browser sizing, keyboard behavior, cross-page links, media playback, and final transport assets
require the parent's combined preview check. Repository-wide tests and the challenge audit are
handled separately by the parent task; no fresh theorem-build claim is made by this document.

Before publishing source or a new site version:

1. Reconcile the remaining README, `docs/IDEA_PORTFOLIO_AND_SYNERGIES.md`, historical
   `docs/AGENT_IDEA_INDEX.json`, paper drafts, docstrings, and benchmark boolean names with these
   findings. Include the new public JSON deprecation notice in the publish artifact so the live
   endpoint does not continue advertising the previous claims.
2. Preserve a reproducible source snapshot and evidence report. A successful regex/token scan or
   historical test count must not be used as the Lean build/axiom report.
3. Review any formal/runtime composition claim against exact theorem signatures, sampling,
   floating-point behavior, fallback feasibility, and plant assumptions. Existing theorems are
   not changed to accommodate an implementation.
4. Replace performance headlines only after a repeatable benchmark with matched constraints,
   tuning budgets, ablations, and raw data. Keep simulation and hardware conclusions distinct.
5. Publish only the reviewed site artifact to the existing `site` branch. A repository visibility
   change is a separate decision; no such change occurred here.
