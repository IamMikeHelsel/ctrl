# Comparable packages and a practical participation model

Assessment date:22 October2026. AI-assisted research using fresh primary project sources. No packages were installed, outside maintainers contacted, changes submitted, or material published. Recommendations below are proposals, not partnerships or evidence of demand. Project documentation was inspected; their performance and correctness claims were not independently reproduced.

## Recommendation

Expose a small capability that a control engineer can call and independently check: a versioned input contract, an offline certificate/receipt, and a narrow decision or trajectory adapter. Keep research synthesis, the Lean replay environment, and optional visualization separate from the consumer's runtime dependencies. The useful public unit is a complete task with an example and a failure case, not a count of theorems.

For the current S12 result, that unit could be “check this static joint uncertainty model and obtain a bounded command guard.” It is not a general robot-safety product. The repaired Python receipt closes an actual mutation hole, but neither its small benchmark nor its four-support predecessor demonstrated a speed advantage. The ST sketch has no target-compiler validation. Those facts belong beside the example, not behind a general “production verified” label. See the [S12 extension](../../../work/pod/crossover-60-20261018/extensions/S12-B01/inventor.md) and [site-usability instruction](../../../work/pod/crossover-60-20261018/SITE-USABILITY.md).

## Prioritized ways to improve tools already in use

Start inside an existing workflow. Local evidence shows MuJoCo and matplotlib are declared dependencies and `src/ctrl/robotics/mujoco_benchmarks.py` already drives MuJoCo. The other projects below are integration candidates; this assessment does not assume Mike already uses or prefers them. No new framework is required to begin.

| Priority | Existing seam and small deliverable | Useful result and honest boundary | First acceptance test |
|---|---|---|---|
| 1 | Extend the existing Python/MuJoCo benchmark module with a task/assumption manifest and portable trace export | Makes the current energy, braking or tracking result independently reproducible. Does not turn simulation into theorem-to-plant validation. | Clean-process replay of one selected benchmark with identical task, integrator, initial state, payload and limits; include a changed-assumption negative and report timing separately from simulation cost. |
| 2 | Put the independently checked receipt and immutable guard behind a narrow existing Python API | Helps callers avoid unchecked/mutable results and stale contexts. Current evidence supports API integrity, not a speedup. | Install without the research notebook, compile one S12 receipt against external context, reject a corrupted proof and stale snapshot, and preserve the documented empty-model behavior. |
| 3 | Add a Ruckig/TOPPRA comparison adapter to the same benchmark harness | Contributes better matched task and replacement tests to familiar planners; does not replace their algorithms. | One state-to-state Ruckig case and one fixed-path TOPPRA case, each with its own contract. Check limits and traces before comparing time or energy; keep waypoint cloud modes outside a local-loop test. |
| 4 | Offer a small Rust receipt/guard adapter only when an actual Rust consumer is chosen | Could fit an OpenRR client or another existing Rust application without adopting a new robotics stack. The parity corpus is the first deliverable. | Same valid/invalid receipts and boundary commands as Python; explicit integer and context semantics. No general numerical parity claim from this narrow result. |
| 5 | Turn the ST guard sketch into one complete PLC verification case | Helps an existing PLC toolchain by specifying source dialect, widths, scan/context assumptions and a test case. It is presently an integration experiment. | Compile with the chosen target or supported verifier frontend; exercise signed bounds, stale receipt and default rejection; then separately test publication/use timing. |
| Later, demand-led | One external Drake or acados example; optional Rerun trace viewer | Reuses a consumer's established model/solver/viewer. Do not add all three dependencies to the base package. | A named downstream task, an owner and a minimal example that runs independently of ctrl's source tree. |

MuJoCo's official Python interface exposes the underlying simulator through a consistent C/Python API, while its simulation documentation distinguishes control callbacks, held controls and integrator-dependent stepping. The first adapter must record these choices rather than treating all `mj_step` loops as the same control experiment. [Python interface](https://mujoco.readthedocs.io/en/stable/python.html), [simulation/control loop](https://mujoco.readthedocs.io/en/stable/programming/simulation.html)

These priorities are recommendations based on local integration proximity and current evidence, not measured demand or percentages of theoretical benefit. Upstream contributions should initially be a benchmark, example or precise bug fix that makes a project we use better. A separate ecosystem is warranted only if an existing extension point demonstrably cannot carry the required contract. The user's permission to merge ready work removes an unnecessary approval stop; it does not make an untested adapter ready or authorize unsolicited outreach. This document creates no PR and sends no message.

## Eight comparables worth learning from

### 1. Ruckig — a narrow motion-generation contract

**Consumption.** The project offers a C++ library with CMake integration and a Python module. Its central interface names current state, target state, derivative limits, control period and output; the update loop is visible in a short example. The repository is MIT-licensed. The Community intermediate-waypoint route invokes a cloud API and is explicitly unsuitable for a real-time local loop; local state-to-state use and waypoint use must therefore be distinguished. [Primary README](https://github.com/pantor/ruckig/blob/main/README.md)

**Value evidence and lesson.** Ruckig publishes numerical tolerances, input-range limitations and benchmark documentation. These are its reported numerical guarantees, not Lean proofs or our measurements. The packaging lesson is to make the exact callable task and unsupported modes explicit. A ctrl comparison should match state, target, limits, replacement schedule and commitment semantics before measuring cycle time. A useful future contribution is a small reproducible edge-case fixture or adapter example; it is not a blanket claim that verified research should replace the planner. [Numerical testing and benchmarks](https://docs.ruckig.com/benchmark.html)

**Maintenance boundary.** The current benchmark page describes Community as the final academic-project state, identifies known numerical issues, and directs maintained production use toward Pro. That makes the edition and support expectations part of any integration decision. This assessment proposes an existing-access benchmark adapter, not purchasing a service or assuming Community receives future fixes. [Project's maintenance statement](https://docs.ruckig.com/benchmark.html)

### 2. TOPPRA — path retiming and the cost of two implementations

**Consumption.** TOPPRA consumes a geometric path and constraints and returns a path parametrization. Its README provides installation, examples, an issue tracker, contribution guidance and contributor credits; the license is MIT. Crucially, the current README announces that separate Python support will be dropped and recommends the C++ version with bindings. Older Python documentation must not be mistaken for the future support contract. [Current README](https://github.com/hungpham2511/toppra/blob/develop/README.md), [license](https://github.com/hungpham2511/toppra/blob/develop/LICENSE)

**Lesson.** Put algorithm semantics in one maintained implementation where feasible, then bind it. A second language port creates an additional numerical and maintenance obligation. For ctrl, use one frozen contract and differential fixture corpus before advertising Rust/Python parity. A concrete participation opening is a path-and-constraint regression case with solver/version details, plus a shared-language reproducer. Retiming a fixed path is a different task from online target replacement; keep their benchmarks separate.

### 3. Drake — supported platforms, bindings and external examples

**Consumption.** Drake provides C++ and Python interfaces, precompiled installation paths, and a documented support matrix tied to CI coverage. Python bindings expose a substantial subset rather than claiming every C++ feature. Its stability policy distinguishes public and experimental APIs and explicitly does not promise a stable C++ ABI. The main license is BSD-3-Clause, with noted third-party exceptions. [Installation](https://drake.mit.edu/installation.html), [bindings](https://drake.mit.edu/python_bindings.html), [stability](https://drake.mit.edu/stable.html), [license](https://github.com/RobotLocomotion/drake/blob/master/LICENSE.TXT)

**Lesson.** Publish a tested platform/language matrix and an external example before asking users to rebuild a large research stack. Treat “Python coverage” as an enumerated API surface. Drake separates bug reports from usage discussions and asks for precise environment information; it also welcomes external gallery examples. A ctrl integration can initially live outside Drake, with a maintainer responsible for its versions and regression tests. [Help/reporting](https://drake.mit.edu/getting_help.html), [developer guidance](https://drake.mit.edu/developers.html)

### 4. acados — high-level authoring, explicit embedded deployment

**Consumption.** acados uses a C core with high-level interfaces for expressing optimal-control problems. `acados_template` generates C sources and build files; deployment is a distinct workflow. Its embedded documentation names platform prerequisites and cross-compilation steps and invites contributions documenting additional targets. The core license is BSD-2-Clause. [Overview](https://docs.acados.org/), [Python/code-generation interface](https://docs.acados.org/python_interface/index.html), [embedded workflow](https://docs.acados.org/embedded_workflow/index.html), [license](https://github.com/acados/acados/blob/main/LICENSE)

**Lesson.** A generated file is not a deployed component. Separate authoring dependencies, generated-runtime dependencies, target build, and target behavior. For ctrl, the analogous deliverable is certificate generation/replay on a workstation plus a narrowly specified runtime payload. A useful design partner supplies one target/toolchain and an executable integration example. Any claimed reduction in online work must include publication, decoding and guard overhead; a solver-speed claim does not establish physical safety or a compiler-correctness theorem.

### 5. OpenRR — Rust interfaces that isolate hardware adapters

**Consumption.** OpenRR separates abstract robot interfaces (`arci` traits), concrete clients, libraries and tools. It distributes Rust crates and documents platform differences; its README calls the project under development and ROS2 support experimental. The license is Apache-2.0. A `JointTrajectoryClient` implementation is an explicit integration seam. [Primary README and architecture](https://github.com/openrr/openrr/blob/main/README.md)

**Lesson.** Offer a small adapter trait/interface rather than a replacement robotics platform. A future ctrl Rust surface could accept typed model/context inputs and return a checked decision while a separate client owns transport and actuation. However, a transport trait does not by itself preserve cancellation, buffering, timestamps or committed motion. A design partner should contribute recorded replacement traces and a mocked client first. The README's experimental labels are useful examples of honest support boundaries; they are not evidence of Python parity or hard-real-time behavior.

### 6. Rerun — shared types and usable cross-language evidence

**Consumption.** Rerun offers Rust, Python and C++ SDKs around a Rust implementation, distributed through language-specific entry points. It is a data/visualization comparator, not a motion planner. Its repository advertises MIT/Apache-2.0 licensing. Shared type definitions generate SDK types and documentation across languages. [README](https://github.com/rerun-io/rerun/blob/main/README.md), [current code-generation layout](https://github.com/rerun-io/rerun/blob/main/AGENTS.md), [SDK architecture history](https://rerun.io/blog/cpp-sdk)

**Lesson.** Shared schema/code generation can reduce interface drift, while semantic parity still needs tests. Visualization can show a certificate's assumptions, branches, rejected commands and replay history without being the proof. Rerun's contribution guide favors small changes or previously discussed larger work, requires human understanding of agent-assisted changes, and records benchmark/binary-size effects. An evidence-viewer example is a plausible bounded contribution; a large unreviewed AI-generated integration is not. [Contribution policy](https://github.com/rerun-io/rerun/blob/main/CONTRIBUTING.md)

### 7. FOSSIL — a research certificate workflow users can specify

**Consumption.** FOSSIL exposes Python and a YAML-driven CLI for certificate/controller synthesis. Its CEGIS workflow combines learned candidates with verification; the repository documents solver prerequisites, an optional container route and experiment examples. The license is BSD-3-Clause. [README and example specification](https://github.com/oxford-oxcav/fossil/blob/main/README.md), [license](https://github.com/oxford-oxcav/fossil/blob/main/LICENSE)

**Lesson.** Let researchers express model, domain, requested property and verifier explicitly, while preserving solver versions and failed/inconclusive runs. A configuration-driven experiment makes a stronger participation unit than a prose conjecture. A potential ctrl researcher contribution is a frozen model/property plus reproducible certificate or counterexample and an independent replay. FOSSIL's verifier semantics are its own: an SMT result must not be relabeled a Lean kernel proof. Do not imply that adding a container removes solver trust or target-deployment work.

### 8. PLCverif — verification-case files and an explicit frontend/backend boundary

**Consumption.** PLCverif documents graphical and command-line execution of the same verification-case file, with selectable requirements and model-checking backends. Its documented frontend covers STEP7 SCL/STL; that does not establish support for every IEC61131-3 dialect or compiler. The core license is EPL-2.0, with separate dependency/backend notices. [Quick start and CLI](https://plcverif-oss.gitlab.io/plcverif-docs/userdocs/QuickStart.html), [frontend/framework overview](https://plcverif-oss.gitlab.io/plcverif-docs/), [core license](https://gitlab.com/plcverif-oss/cern.plcverif/-/raw/master/LICENSE), [dependency notices](https://plcverif-oss.gitlab.io/plcverif-docs/project/License.html)

**Lesson.** Package a complete verification case: source dialect, entry block, scan/environment assumptions, requirements, backend and settings. Do not present generated ST plus a mathematical Boolean theorem as verified PLC execution. The smallest future collaboration is a compiler/model-checker expert reproducing one tiny guard case, including signed boundaries and stale-context behavior. Backend installation and license scope remain explicit integration work. Documentation was available; no target was built in this assessment.

## What Rust/Python parity should mean here

This is a proposed acceptance contract, not a claim that ctrl currently meets it:

| Surface | Shared requirement | Evidence before advertising parity |
|---|---|---|
| Model and receipt schema | Same units, rational encoding, branch coverage, semantics/version binding, invalid-input rules | Versioned schema plus round-trip and malformed-input fixtures |
| Exact verifier | Same accepted/rejected certificates, including missing branches, false Farkas proofs and stale external context | Independent cross-language replay on the frozen corpus; no float coercion |
| Runtime guard | Same inward-rounded interval, integer range, empty-grid behavior and fail-closed context gates | Boundary tests, overflow/type controls, and target-specific execution evidence |
| Numerical trajectory adapter | Same task, initial/terminal state, timing, tolerances, cancellation and retained commitments | Differential traces with declared tolerances; bitwise identity only when actually justified |
| Error and lifecycle behavior | Same unsupported cases, cancellation outcome, ownership and snapshot lifetime | Contract tests alongside happy-path examples |

A binding to one core reduces duplicated algorithms; it does not prove all-language behavior. An independent implementation is valuable when it supplies a genuinely independent checker, but then disagreement handling and maintenance ownership are part of the product. Package exact offline checking separately from optional large solvers and from the runtime. Do not require a PLC consumer to install Lean or Python merely to compare an already checked interval, but do preserve a route to replay the receipt independently.

For S12, a verified immutable Python object improves local API integrity, not hostile-process security. A Rust newtype can similarly prevent ordinary unchecked construction, but serialized receipts still need verification and externally authoritative current context. Coherent publication and actuator use remain integration obligations in both languages.

## Participation model for a future public release

Invite contributions with a small, reviewable completion condition. These are possible participant types, not commitments by the projects above.

| Participant | Concrete contribution | Acceptance and credit |
|---|---|---|
| Benchmark contributor | One self-contained model/trace fixture, task contract, platform/toolchain manifest and reproduction command | Preserve failures and inconclusive outcomes. Credit fixture author and source in its manifest and release notes; record data license separately from code. |
| Integration design partner | One adapter to an existing consumer, first against a mock or recorded trace | Demonstrate installation, happy path, a rejected case and lifecycle/context behavior. Report integration files changed, dependencies and measured cost; no implied endorsement. |
| Research owner | One named open proof/bridge or counterexample with frozen statement and explicit assumptions | Independent reproduction, permitted-axiom and statement-binding audit where formalized, honest prior-art/AI disclosure. Cite the original method and the implementation separately. |
| Language/target maintainer | One tested Rust/Python binding or one concrete C/ST target profile | Own the build matrix, version compatibility, migration notes and regression corpus; unsupported targets remain labeled. |

A practical first invitation set would be: a Ruckig/TOPPRA user with a matched trajectory fixture, an OpenRR or Drake user who can run an external adapter, and a PLC verification practitioner who can validate one compiler/runtime boundary. Ask each for one artifact, not a general endorsement. acados's target-workflow model and Rerun's example-contribution model suggest useful contribution shapes; they do not imply those maintainers want a ctrl integration.

An issue should contain: requested task and property; frozen model/statement digest; released information and timing/replacement semantics; minimal input; exact command and versions; expected versus observed result; evidence level; and permission/license for every included trace. Separate “install failed,” “certificate rejected,” “solver inconclusive,” “formal statement wrong,” and “physical model unsupported.” Give each a named owner and a next discriminating test. A reproducible negative result is a valid contribution.

Before any external submission, a human should understand and review the proposed change and follow the destination's current contribution policy. Keep AI assistance disclosed. No automated outreach, issue creation or publication was performed here. Rerun's policy is an especially clear primary example of why maintainer review capacity must shape the request. [Current contribution guidance](https://github.com/rerun-io/rerun/blob/main/CONTRIBUTING.md)

## License, attribution and maintenance preparation

Local `pyproject.toml` and README advertise MIT. That does not establish rights to every future benchmark, external paper asset, copied implementation, generated file, model or dataset. Before a public flip, inventory the actual release closure: authored code, Lean/Mathlib dependencies, runtime dependencies, solver/tool invocations, generated templates, example data and adapted third-party material. Retain applicable notices and source attribution; review dependencies by the versions actually shipped. The project license labels above describe inspected sources, not a compatibility opinion for an unbuilt combined distribution.

Recommended release artifacts are: a clear license/notice inventory; contributor and citation files; per-benchmark authors/source/license metadata; an AI-assistance disclosure; a supported-platform/API matrix; and an ownership file naming who maintains each adapter and evidence bundle. Do not change licenses or impose a new contribution agreement in this research pass. Resolve ownership and licensing decisions before accepting material intended for redistribution.

Credit should distinguish the original theorem/algorithm, adapter implementation, benchmark/data contribution, independent reproduction and maintenance. A kernel proof of a known result is not a new-discovery credit claim. A design partner's test is not product endorsement. A contributor should be able to supply one fixture without also volunteering to maintain the entire system.

## Small release candidate and broader opportunity

The smallest reviewable candidate is one externally runnable example with a stable callable function, exact input/output fixtures, a receipt checker, one failure path and a pinned replay environment. A contributor should be able to reproduce that artifact without navigating60 research cards. Preserve the cards as provenance behind the package rather than making them its installation guide.

A larger framework spanning planning, uncertainty updates, real-time scheduling and PLC control needs coordinated semantics across libraries. Treat that as a separate roadmap with owners and measured integration costs. Report capability-level adoption gates: mathematical result; concrete certificate check; language adapter; target compile; simulator; physical validation. Do not convert an illustrative percentage or a theorem count into an attainable speed or safety gain.

Success for the first public candidate should be measured by independent clean-environment reproductions, a downstream adapter that preserves its stated contract, failures caught by the negative corpus, and the cost of the complete consumer path. These are proposed release tests, not outcomes already achieved. No recommended comparison requires buying a service or moving private robot data to a hosted tool.

## Evidence limits

Eight selected comparables were examined through primary READMEs, documentation, license files and contribution guidance on the assessment date. One PLCverif architecture URL and an OpenRR CONTRIBUTING URL were unavailable; claims above use the accessible documented interfaces instead. Installation paths and maintainer policies can change and should be rechecked when implementing an adapter or preparing a submission. No conclusion here establishes novel mathematics, full API parity, licensed redistribution of a combined product, maintainer interest, deployed performance or safety certification.

Assessment quality: source relevance4/4, source freshness4/4, integration specificity4/4, evidence-boundary clarity4/4, direct adoption validation1/4 =17/20. This is a sourced packaging assessment; direct user/target trials remain open.
