# Put useful mathematics into tools people already use

22 October 2026 · AI-assisted assessment and proposed delivery plan. No downstream integration, hardware benefit, new performance result, or partnership is claimed.

## Decision

Organize around a user's existing job: compare motion plans, check a solver result, reject a stale command, or spend less time processing camera frames. Offer a small callable component, a portable output, and a reproducible comparison. Keep the underlying research discoverable behind that task.

The first delivery candidate should be a **motion comparison kit** using the Python routines and MuJoCo already here. The second should be a **command admission kit** with versioned receipts and an independently checked consumer. The YOLO idea deserves a profiling experiment before a new package. These are priorities for implementation, not release approvals.

The current checkout contains 48 theorem-registered Python functions; the registry matches declaration names and scans source tokens. It does not prove executable refinement. The campaign has 60 initial reviews, 55 GO routes, one HOLD and four NO-GO routes. One first extension is complete and S12 is partial. Neither function count nor GO count is a count of release-ready products. No Rust crate was found in the inspected repository surface. A refreshed, per-capability release inventory replaces a blanket “11 ready” claim. [Inventory](domain-inventory.md)

## Start with familiar consumers

“Already used” below means present in this checkout's dependencies or code, not a claim about every tool Mike personally uses. “Target” means a proposed integration to validate.

| Consumer / relationship | User task and proposed attachment | Useful bundle / output | Adoption burden | Discriminating comparison |
|---|---|---|---|---|
| MuJoCo + NumPy/SciPy — already used | Compare two ways of making the same move | Motion profile + actuator bounds + tracking/effort accounting; trajectory samples and a trace/report | Local offline adapter first; controller replacement is a separate project | Same endpoints, duration, limits, payload, tuned baseline. Measure total electrical energy when available; otherwise label torque/loss proxies. Include cases where smoothness increases energy. |
| CVXPY/OSQP — already used | Check whether a proposed command meets the modeled constraints | Candidate solver output → rational certificate → independent verifier → versioned command interval | Offline checking is local; live enforcement needs state/context ownership | Mutated certificates, stale model/version, empty feasible set, producer and checking costs. Compare existing solver tolerances and verification options. No solver replacement or speed claim yet. |
| python-control — dependency | Inspect why a controller passes or fails a modeled condition | Model and gain → residual/margin report, exact certificate when available | Analysis helper; numerical-to-exact conversion must be explicit | Known stable, unstable, nearly singular and poorly scaled cases; compare library result and exact obligations. No new LQR/Kalman algorithm claim. |
| MoveIt / Ruckig / TOPPRA — targets | Change a motion profile while keeping the task and limits visible | External trajectory comparison/retiming adapter; preserve original planner | Coordinated integration: timing, collision checks, cancellation and buffered motion matter | Compare against the existing jerk-limited or retiming baseline, not an intentionally weak profile. Recheck path and constraints after retiming. |
| ROS 2 / OpenRR — targets | Explain or reject a command based on old state | Timestamp + model/version + uncertainty + stop reserve → decision with reason | Wrapper API can be small; reliable clock bounds and coherent actuator use are system work | Recorded delayed/reordered/replaced messages, deadline misses and stale snapshots; measure availability as well as rejection. |
| PLC Structured Text — existing emitted examples, target deployment open | Use bounded arithmetic and a readable command guard | Fixed schema, integer scale, checked limits, ST example, target-specific test vectors | Target compiler and scan semantics must be checked; no portable certification claim | Signed limits, rounding, overflow, cold start, model-version change and coherent publication. Pair with a named compiler/runtime. |
| Ultralytics YOLO / OpenCV — user-nominated target | Spend less time on detection while retaining required detections | Profile first; then exact spatial candidate filtering or bounded detection scheduling | Postprocessing can be local; skipped frames/crops change behavior and require evaluation | Pin model/head/backend and compare full-pipeline p50/p95 latency, recall, mAP, small/occluded objects, first-detection delay and energy/frame. No YOLO speedup established. |
| Rerun — target | See why a result was accepted or rejected | Portable trace with units, assumptions, decisions and evidence links | Optional viewer adapter; keep replay possible without it | Independent user can reproduce a decision and identify the failing premise from the trace. |

MoveIt already exposes Ruckig smoothing, so a smooth trajectory alone is not a competitive advantage. OSQP already generates fixed-family embedded C; merely generating code is also not a differentiator. Our proposed contribution is an auditable contract, a useful scoped method, and a fair comparison at a real integration seam. [MoveIt interface](https://moveit.picknik.ai/main/api/html/ruckig__traj__smoothing_8hpp_source.html), [OSQP code generation](https://osqp.org/docs/codegen/index.html). See [eight comparables and participation plan](comparables-community.md).

## A notional bar that permits smaller wins

These are PM screening defaults, not measured gains or universal purchasing rules. Choose the primary metric and allowed regressions before tuning.

- **Major migration:** aim for at least 30% improvement in the user's primary whole-task metric, or a clearly specified capability the old system cannot supply. Include installation, runtime overhead, maintenance and migration cost.
- **Local optional adapter:** a reproducible 3–10% whole-task improvement can justify adoption when the change is small, reversible, and preserves important behavior. This range is a proposed screening band, not a result.
- **Capability/evidence improvement:** a supported target, a detected failure class, a checkable certificate, or a new operating envelope may justify an upgrade without a speed percentage. Quantify the new capability and its cost separately.
- **Below those bars:** keep a cheap benchmark or research artifact if informative; do not build a maintained package solely because a theorem exists.

Report both absolute and relative change: 10 ms → 7 ms is 30% less latency and about 43% more throughput only in a serial, unconstrained throughput model. “30% faster” is too ambiguous for a result table. Define the denominator.

A 50% reduction in a component occupying 10% of end-to-end latency saves at most 5% overall before overhead. Four sequential 10% reductions on the remaining same metric yield 34.39%, not 40%, if they compose as assumed. Four improvements to different metrics do not combine into a percentage. Interactions, bottleneck shifts and batch/device contention must be measured. Benchmark baseline, each change alone, and the full bundle; use an ablation when attribution matters. A bundle should share a task, assumptions, data and runtime boundary—not merely contain 3–5 theorems.

## Python and Rust: one public contract

Every capability offered publicly in Python should also have a supported Rust path. This is a release requirement; current parity is absent. Prefer a canonical Rust runtime core with thin Python bindings (PyO3/maturin), shared schemas and one cross-language fixture corpus. Keep a separate Python reference or exact independent checker when it provides useful independent evidence. PyO3 supports exposing Rust as Python modules; it does not establish mathematical or numerical equivalence. [PyO3 guide](https://pyo3.rs/v0.29.2/)

Proposed release units (names provisional, no published crates implied):

1. `ctrl-core`: narrow numerical kernels and typed decisions; per-module allocation and target support documented.
2. `ctrl-evidence`: exact certificate/receipt checking and schema/version handling; separate from the control loop and optional solvers.
3. Python bindings: same task inputs, outputs, errors and lifecycle, plus convenient array handling. Offline research scripts are internal until supported in both languages.
4. Examples/adapters: MuJoCo first; MoveIt/OpenRR, solver wrappers and Rerun only when their benchmark justifies maintenance.
5. Optional C ABI and ST examples: selected supported functions only. Generation, target compilation, execution parity, timing bounds and physical acceptance are separate milestones.

Portable outputs: trajectory samples with time/units; a receipt with model/context digests and rational encoding; a benchmark trace/report with baseline, target and revisions. A JSON file is not automatically a trusted certificate: the consumer must verify content and bind it to externally authoritative current context. Bindings must preserve rejection, malformed input, overflow and cancellation behavior, not just happy-path numerical output.

## Technical copy editing

Keep established technical terms searchable in secondary text and API compatibility notes. Change visible product copy first; do not silently rename existing public symbols or theorem declarations.

| Current technical label | Reader-facing name | One sentence that stays within the evidence |
|---|---|---|
| Septic trajectory | Seventh-degree motion profile | Compare motion profiles that trade actuator effort against timing and derivative limits. |
| Lorentz-cone CBF | Contact-force guard | Check a commanded acceleration against the stated contact and braking model. |
| Sontag / H-infinity / ISS bundle | Tracking under disturbance | Compare how accurately the model follows a command when disturbances are added. |
| SE(3) / homography servoing | Geometry-aware camera motion | Use camera geometry to test motions and identify ambiguous or unsupported cases. |
| Farkas / support-function certificate | Checkable command limits | Independently check the evidence behind a permitted command interval. |
| Structured Boolean OMv | Structured spatial queries | Exploit a proven input pattern; reject cases that do not fit it. |
| Production-verified / breakthrough | Evidence-specific label | State kernel proof, numerical test, simulation or target measurement, with its scope. |

“Your robot shakes less, uses less energy and runs cooler” is an excellent description **after** separate vibration, electrical-energy and temperature measurements support it under comparable conditions. Until then: “Compare motion profiles to see whether your robot can move with less effort.” Lower jerk is not a universal vibration or energy guarantee; a reduced torque proxy is not measured electrical energy or temperature.

## Participation when public

Make the first contribution a fixture or adapter someone can finish: a MoveIt trajectory, a YOLO stage profile, a PLC signed-boundary test, or an independently reproduced rejected certificate. Supply one command, a pinned environment, a known failure, a data/license manifest, an owner and an explicit acceptance condition. Credit original mathematics, implementation, data, reproduction and maintenance separately. Publish supported language/target matrices and failure cases beside successes. Start with a few design partners, then promote reproducible examples into documented packages. No outreach or publication was performed.

## Current delivery and open boundaries

This assessment supplies an adoption map, language plan, comparative research, YOLO experiment proposals and local site copy. It does not supply a Rust implementation, deployed PLC block, downstream integration or measured new YOLO gain. The site preview is local. Campaign research resumes S12-B01 with its recorded time; this work is not credited as a timed extension.

Quality: 17/20 (source grounding4, integration specificity4, evidence boundaries4, reproducibility3, downstream validation2). This is an editorial/engineering assessment, not a probability of successful deployment.
